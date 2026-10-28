// Vendored from https://github.com/symmr/ppt-translation-supporter/blob/5638b5d/docs/pdf-text.js
// (MIT License, Copyright (c) 2026 symmr). Update by copying the file again
// rather than editing it here.
// PDF text extract and two kinds of write-back: cover each text block on the
// original pages with its translation (pdf-lib), or lay the translations out
// as a new Word document. pdf.js, pdf-lib and fontkit are passed in, so the
// browser can load them from the CDN only when a PDF is dropped.
(function () {
"use strict";

// Static TTF: fontkit subsets TrueType outlines reliably, CFF/OTF less so.
const PDF_FONT_URL = "https://cdn.jsdelivr.net/npm/@expo-google-fonts/noto-sans-jp@0.4.1/400Regular/NotoSansJP_400Regular.ttf";
const PDF_BOLD_FONT_URL = "https://cdn.jsdelivr.net/npm/@expo-google-fonts/noto-sans-jp@0.4.1/700Bold/NotoSansJP_700Bold.ttf";
const PDF_FONT_NAME = "Noto Sans JP";
// Weight from the font name; Medium counts, as designs use it for headings.
const BOLD_FONT_RE = /(Bold|Black|Heavy|Semibold|SemiBold|Demi|Medium|W[6-9]\b)/;

const rewrite = typeof module !== "undefined" && module.exports
  ? require("./pdf-rewrite.js")
  : window;

const TAG_LIKE_RE = /(?:\[\/?\d+\]|⟦\/?\d+⟧)/;
// CJK, kana, full-width forms: no spaces between these when joining pieces.
const CJK_RE = /[⺀-鿿가-힯豈-﫿＀-￯]/;
// Never start a wrapped line with these; they stay on the previous line.
const NO_LINE_START_RE = /[、。，．,.:;!?！？）」』】〕〉》”’ー々ぁぃぅぇぉっゃゅょァィゥェォッャュョ・：；\])}]/;
const NO_LINE_END_RE = /[（「『【〔〈《“‘([{]/;
const MIN_SHRINK = 0.5;
// A list marker at the start of a line: bullets, "1.", "a)", "(iv)".
const LIST_MARKER_RE = /^(?:[•●○◦▪■□❏❑✓✔➢►▶‣⁃*\-–—]|\(?(?:\d{1,3}|[A-Za-z]|[ivxIVX]{1,4})[.)])(?:\s|$)/u;
// Nothing to translate: no letters, or only a list marker.
function isMarkerOnly(text) {
  const t = String(text).trim();
  return !/\p{L}/u.test(t) || /^\(?(?:\d{1,3}|[A-Za-z]|[ivxIVX]{1,4})[.)]$/u.test(t);
}

function isCjk(ch) {
  return CJK_RE.test(ch || "");
}

// A block's text is kept as runs: { text, style }. style is one shared
// { color, link, bold } object per combination, so runs compare by identity.
// Blocks with more than one run are tagged like PPTX paragraphs ([0]...[/0])
// so the translation can keep the colors.
const PLAIN = Object.freeze({ color: null, link: null, bold: false });
function runsText(runs) {
  return runs.map((r) => r.text).join("");
}

function pushRun(runs, text, style) {
  if (!text) return;
  const last = runs[runs.length - 1];
  if (last && last.style === style) last.text += text;
  else runs.push({ text, style });
}

function lastChar(runs) {
  for (let i = runs.length - 1; i >= 0; i -= 1) if (runs[i].text) return runs[i].text.slice(-1);
  return "";
}

// How "styled" a run is: a link outranks a color or weight, those outrank plain.
function styleWeight(style) {
  return (style.link ? 2 : 0) + (style.color && style.color !== "000000" ? 1 : 0) + (style.bold ? 1 : 0);
}

// A space between two runs goes to the plainer one, so "manual" is the link
// and not "manual ".
function spaceStyle(before, after) {
  return after && styleWeight(after) < styleWeight(before) ? after : before;
}

function joinPieces(runs, pieces, spaced) {
  const left = lastChar(runs);
  const right = (pieces[0] && pieces[0].text[0]) || "";
  if (left && right && spaced && !/\s/.test(left) && !/\s/.test(right) && !isCjk(left) && !isCjk(right)) {
    pushRun(runs, " ", spaceStyle(runs[runs.length - 1].style, pieces[0].style));
  }
  for (const piece of pieces) pushRun(runs, piece.text, piece.style);
}

function joinLines(runs, next) {
  const prev = runsText(runs);
  const first = runsText(next);
  if (/[A-Za-z]-$/.test(prev) && /^[a-z]/.test(first)) {
    const last = runs[runs.length - 1];
    last.text = last.text.slice(0, -1);
  } else if (!isCjk(prev.slice(-1)) && !isCjk(first[0])) {
    pushRun(runs, " ", spaceStyle(runs[runs.length - 1].style, next[0] && next[0].style));
  }
  for (const run of next) pushRun(runs, run.text, run.style);
}

// Collapses whitespace across run boundaries, trims the ends and drops
// empty runs.
function normalizeRuns(runs) {
  const out = [];
  let prevSpace = true;
  for (const run of runs) {
    let text = "";
    for (const ch of run.text.replace(/\s/g, " ")) {
      if (ch === " " && prevSpace) continue;
      text += ch;
      prevSpace = ch === " ";
    }
    pushRun(out, text, run.style);
  }
  while (out.length && /^ *$/.test(out[out.length - 1].text)) out.pop();
  if (out.length) out[out.length - 1].text = out[out.length - 1].text.replace(/ +$/, "");
  return out.filter((r) => r.text);
}

function horizontal(transform) {
  const [a, b, c, d] = transform;
  return a > 0 && d > 0 && Math.abs(b) <= a * 0.02 && Math.abs(c) <= d * 0.02;
}

// pdf.js text items to lines: items that sit on one baseline and follow each
// other closely. A wide gap (table columns, tab stops) starts a new line so
// the cells stay separate blocks. styler(item, x, y, size) splits an item's
// string into styled pieces; without one every item is one plain piece.
function itemsToLines(items, styles, styler) {
  const lines = [];
  let line = null;
  let pendingSpace = false;
  const close = () => {
    if (line) {
      line.runs = normalizeRuns(line.runs);
      line.text = runsText(line.runs);
      if (line.text) lines.push(line);
    }
    line = null;
    pendingSpace = false;
  };
  for (const item of items || []) {
    const transform = item.transform || [];
    if (transform.length < 6 || !horizontal(transform)) {
      if (item.str && item.str.trim()) close();
      continue;
    }
    const size = item.height > 0 ? item.height : Math.abs(transform[3]);
    const x = transform[4];
    const y = transform[5];
    const str = String(item.str || "");
    if (!str.trim()) {
      if (line && item.width > 1.5 * line.size) close();
      else if (line && str) pendingSpace = true;
      if (item.hasEOL) close();
      continue;
    }
    if (!(size > 0)) continue;
    const style = (styles && styles[item.fontName]) || {};
    if (line) {
      const sameBaseline = Math.abs(y - line.y) < 0.35 * Math.max(size, line.size);
      const gap = x - line.x1;
      const near = gap > -0.5 * line.size && gap < 1.5 * Math.max(size, line.size);
      if (!sameBaseline || !near) close();
    }
    const pieces = styler ? styler(item, x, y, size) : [{ text: str, style: PLAIN }];
    if (!pieces) continue;
    const firstFont = pieces.firstFont || item.fontName || "";
    const lastFont = pieces.lastFont || item.fontName || "";
    if (!line) {
      line = {
        x0: x,
        x1: x + (item.width || 0),
        y,
        size,
        ascent: typeof style.ascent === "number" && style.ascent > 0 ? style.ascent : 0.8,
        descent: typeof style.descent === "number" ? Math.abs(style.descent) : 0.2,
        runs: [],
        firstFont,
      };
      for (const piece of pieces) pushRun(line.runs, piece.text, piece.style);
    } else {
      joinPieces(line.runs, pieces, pendingSpace || x - line.x1 > 0.18 * line.size);
      line.x1 = Math.max(line.x1, x + (item.width || 0));
      line.size = Math.max(line.size, size);
    }
    line.lastFont = lastFont;
    pendingSpace = false;
    if (item.hasEOL) close();
  }
  close();
  return lines;
}

// Lines to paragraph-like blocks: next line below, similar size, overlapping
// horizontally, and (from the third line on) the same line pitch.
function linesToBlocks(lines) {
  const blocks = [];
  let block = null;
  const finish = () => {
    block.runs = normalizeRuns(block.runs);
    block.text = runsText(block.runs);
    blocks.push(block);
  };
  for (const line of lines) {
    if (block) {
      const ratio = line.size / block.size;
      const dy = block.lastY - line.y;
      const overlaps = line.x0 < block.x1 && line.x1 > block.x0;
      const indentOk = line.x0 > block.x0 - line.size;
      const pitchOk = !block.leading || Math.abs(dy - block.leading) < 0.35 * line.size;
      // a line ending in one font followed by a line starting in another is
      // a heading over its paragraph (same size, different weight)
      const fontOk = !block.lastFont || !line.firstFont || block.lastFont === line.firstFont;
      // a list marker starts a new item; a marker on its own never joins
      const listOk = !LIST_MARKER_RE.test(line.text) && !isMarkerOnly(line.text) && !isMarkerOnly(block.lastText);
      const joins = ratio > 0.8 && ratio < 1.25 &&
        dy > 0.6 * block.size && dy < 1.9 * block.size &&
        overlaps && indentOk && pitchOk && fontOk && listOk;
      if (joins) {
        block.leading = block.leading || dy;
        joinLines(block.runs, line.runs);
        block.x0 = Math.min(block.x0, line.x0);
        block.x1 = Math.max(block.x1, line.x1);
        block.bottom = Math.min(block.bottom, line.y - line.descent * line.size);
        block.lastY = line.y;
        block.lastFont = line.lastFont;
        block.lastText = line.text;
        block.lineCount += 1;
        continue;
      }
      finish();
    }
    block = {
      x0: line.x0,
      x1: line.x1,
      top: line.y + line.ascent * line.size,
      bottom: line.y - line.descent * line.size,
      firstY: line.y,
      lastY: line.y,
      size: line.size,
      leading: 0,
      lineCount: 1,
      lastFont: line.lastFont,
      lastText: line.text,
      runs: line.runs.map((r) => ({ ...r })),
    };
  }
  if (block) finish();
  return blocks;
}

function round2(n) {
  return Math.round(n * 100) / 100;
}

function median(values) {
  if (!values.length) return 0;
  const sorted = [...values].sort((a, b) => a - b);
  return sorted[Math.floor(sorted.length / 2)];
}

// Style of each character of a pdf.js item, from the strings the content
// stream shows there (fill color, font) and the link annotations over it.
// segments: from collectTextSegments; links: [{ rect, url }].
function makeStyler(segments, links) {
  const styles = new Map();
  const styleOf = (color, link, bold) => {
    const key = `${color}|${link}|${bold}`;
    if (!styles.has(key)) styles.set(key, { color: color || null, link: links[link] || null, bold });
    return styles.get(key);
  };
  return (item, x, y, size) => {
    const chars = Array.from(String(item.str));
    const width = item.width || 0;
    const charX = (i) => x + ((i + 0.5) / chars.length) * width;
    const nearby = segments.filter((s) => Math.abs(s.y0 - y) < 0.35 * size);
    const onLine = nearby.filter((s) => s.visible);
    // transparent or invisible text (alt text, OCR layers) is not extracted
    if (!onLine.some((s) => s.x1 > x && s.x0 < x + width) &&
      nearby.some((s) => !s.visible && s.x0 >= x - 0.5 && s.x0 < x + width)) return null;
    // strings that start inside the item; else the one drawn over its middle
    let segs = onLine.filter((s) => s.x0 >= x - 0.5 && s.x0 < x + width - 0.05);
    if (!segs.length) segs = onLine.filter((s) => s.x0 <= x + width / 2 && s.x1 >= x + width / 2).slice(-1);
    segs.sort((p, q) => p.x0 - q.x0);
    // one string per character when the glyph counts add up, else the
    // string nearest to where the character sits
    const perChar = segs.reduce((n, s) => n + s.count, 0) === chars.length
      ? segs.flatMap((s) => new Array(s.count).fill(s))
      : chars.map((_, i) => segs.reduce((best, s) => {
        const dist = (seg) => Math.max(seg.x0 - charX(i), charX(i) - seg.x1, 0);
        return !best || dist(s) < dist(best) ? s : best;
      }, null));
    const cy = y + size * 0.3;
    const styleAt = chars.map((_, i) => {
      const seg = perChar[i];
      const link = links.findIndex(({ rect }) => charX(i) >= Math.min(rect[0], rect[2]) && charX(i) <= Math.max(rect[0], rect[2]) &&
        cy >= Math.min(rect[1], rect[3]) - 1 && cy <= Math.max(rect[1], rect[3]) + 1);
      return styleOf(seg ? seg.color : null, link, Boolean(seg && BOLD_FONT_RE.test(seg.font)));
    });
    // Positions estimated from widths can land a character off; styled spans
    // nearly always start and end at a space, so snap boundaries to one.
    for (let b = 1; b < styleAt.length; b += 1) {
      if (styleAt[b] === styleAt[b - 1] || chars[b] === " " || chars[b - 1] === " ") continue;
      const k = [b + 1, b - 1, b + 2, b - 2].find((j) => j > 0 && j < chars.length && (chars[j] === " " || chars[j - 1] === " "));
      if (k === undefined) continue;
      if (k < b) styleAt.fill(styleAt[b], k, b);
      else styleAt.fill(styleAt[b - 1], b, k);
    }
    const pieces = [];
    chars.forEach((ch, i) => pushRun(pieces, ch, styleAt[i]));
    pieces.firstFont = (perChar[0] && perChar[0].font) || "";
    pieces.lastFont = (perChar[perChar.length - 1] && perChar[perChar.length - 1].font) || "";
    return pieces;
  };
}

function taggedText(runs) {
  if (runs.length <= 1) return runsText(runs);
  return runs.map((r, i) => `[${i}]${r.text}[/${i}]`).join("");
}

// pdf: a pdf.js PDFDocumentProxy. options.segmentsFor(pageIndex) returns the
// page's shown strings (collectTextSegments) for colors; without it every
// block is one plain run.
async function extractPdfTexts(pdf, onPage, options) {
  const opts = options || {};
  const texts = [];
  const metadata = [];
  const pages = [];
  let uidNum = 1;
  for (let index = 0; index < pdf.numPages; index += 1) {
    if (onPage) onPage(index + 1, pdf.numPages);
    const page = await pdf.getPage(index + 1);
    const content = await page.getTextContent();
    const [vx0, vy0, vx1, vy1] = page.view;
    pages.push({ width: vx1 - vx0, height: vy1 - vy0 });
    let segments = [];
    if (opts.segmentsFor) {
      try {
        segments = (await opts.segmentsFor(index)) || [];
      } catch (_) {
        segments = [];
      }
    }
    let links = [];
    try {
      links = (await page.getAnnotations())
        .filter((a) => a.subtype === "Link" && Array.isArray(a.rect) && (a.url || a.dest || a.action))
        .map((a) => ({ rect: a.rect.map(round2), url: a.url || null }));
    } catch (_) {
      links = [];
    }
    const styler = segments.length || links.length ? makeStyler(segments, links) : null;
    for (const block of linesToBlocks(itemsToLines(content.items, content.styles, styler))) {
      // bullets, "1.", "a." and the like stay as they are
      if (isMarkerOnly(block.text)) continue;
      const uid = `uid_${String(uidNum).padStart(4, "0")}`;
      uidNum += 1;
      texts.push(uid);
      texts.push(taggedText(block.runs));
      metadata.push({
        id: uid,
        type: "pdf",
        page: index,
        x: round2(block.x0),
        y: round2(block.bottom),
        w: round2(block.x1 - block.x0),
        h: round2(block.top - block.bottom),
        size: round2(block.size),
        leading: round2(block.leading),
        lines: block.lineCount,
        firstBaseline: round2(block.firstY),
        text: block.text,
        runs: block.runs.map((r) => ({ text: r.text, ...r.style })),
        title: false,
      });
    }
    if (page.cleanup) page.cleanup();
  }
  // Titles for the Word output: clearly larger than the usual body size.
  const body = median(metadata.map((m) => m.size));
  for (const m of metadata) m.title = body > 0 && m.size >= body * 1.3;
  return {
    lines: texts,
    text: texts.join("\n"),
    metadata,
    pages,
    slideCount: pdf.numPages,
    uidCount: metadata.length,
    unitLabel: `${pdf.numPages} ページ`,
  };
}

// Translation text plus the run index of every character. Tags that match
// the block's runs one to one keep the styles; anything else is flattened
// into the run with the most text.
function styledText(meta, translated) {
  const runs = meta.runs && meta.runs.length ? meta.runs : [{ text: meta.text, ...PLAIN }];
  const raw = String(translated).replace(/\s+$/, "");
  if (runs.length <= 1) {
    return { text: raw, styles: new Array(raw.length).fill(0), flattened: false, tagArtifact: TAG_LIKE_RE.test(raw) };
  }
  const re = /\[(\d+)\]([\s\S]*?)\[\/\1\]/g;
  const matches = [];
  let m;
  while ((m = re.exec(raw)) !== null) matches.push({ index: Number(m[1]), text: m[2], start: m.index, end: m.index + m[0].length });
  const seen = new Set(matches.map((x) => x.index));
  const valid = matches.length === runs.length && seen.size === runs.length &&
    [...seen].every((i) => i >= 0 && i < runs.length);
  if (!valid) {
    const text = raw.replace(/(?:\[\/?\d+\]|⟦\/?\d+⟧)/g, "");
    let main = 0;
    runs.forEach((r, i) => { if (r.text.length > runs[main].text.length) main = i; });
    return { text, styles: new Array(text.length).fill(main), flattened: true, tagArtifact: false };
  }
  let text = "";
  const styles = [];
  const add = (str, style) => {
    text += str;
    for (let i = 0; i < str.length; i += 1) styles.push(style);
  };
  let pos = 0;
  matches.forEach((match, k) => {
    const gap = raw.slice(pos, match.start);
    add(gap, k === 0 ? match.index : matches[k - 1].index);
    add(match.text, match.index);
    pos = match.end;
  });
  add(raw.slice(pos), matches[matches.length - 1].index);
  return { text, styles, flattened: false, tagArtifact: false };
}

// Break into wrap units: one CJK character, or a Latin word with the spaces
// after it. Closing punctuation sticks to the unit before it.
// Returns [{ start, end }] offsets into text.
function wrapUnits(text, offset) {
  const units = [];
  const re = /[A-Za-z0-9À-ɏ'’\-_.,:;/@#%&+=*!?()]+\s*|\s+|[\s\S]/g;
  let match;
  while ((match = re.exec(text)) !== null) {
    const unit = { start: offset + match.index, end: offset + match.index + match[0].length };
    const prev = units[units.length - 1];
    const prevLast = prev ? text[prev.end - offset - 1] : "";
    if (prev && (NO_LINE_START_RE.test(match[0][0]) || NO_LINE_END_RE.test(prevLast))) prev.end = unit.end;
    else units.push(unit);
  }
  return units;
}

// Paragraphs as wrap units with their widths, measured once: width with
// trailing spaces (w) and without (wt). measure(str, offset) may be called
// at any one size, as text width scales linearly with the font size.
function measureUnits(text, measure) {
  const src = String(text);
  const paras = [];
  let offset = 0;
  for (const para of src.split("\n")) {
    const units = wrapUnits(para.replace(/\r$/, ""), offset).map((u) => {
      const trimmed = src.slice(u.start, u.end).replace(/\s+$/, "");
      return { ...u, w: measure(src.slice(u.start, u.end), u.start), wt: measure(trimmed, u.start), tend: u.start + trimmed.length };
    });
    paras.push({ start: offset, units });
    offset += para.length + 1;
  }
  return paras;
}

// Line breaks as [{ start, end }] offsets into text, trailing spaces left
// out. measured: from measureUnits; widths there times scale are compared
// with maxWidth. Touching the edge counts as fitting (0.01pt), so rounding
// cannot tip an exact fit.
function layoutUnits(text, measured, maxWidth, measure, scale) {
  const k = scale || 1;
  const edge = maxWidth + 0.01;
  const src = String(text);
  const out = [];
  for (const { start: paraStart, units } of measured) {
    let start = paraStart;
    let end = paraStart;
    let used = 0; // width of the units on this line, trailing spaces included
    let lastTrimEnd = paraStart;
    for (const unit of units) {
      if (end === start || (used + unit.wt) * k <= edge) {
        used += unit.w;
        end = unit.end;
        lastTrimEnd = unit.tend > unit.start ? unit.tend : lastTrimEnd;
        continue;
      }
      out.push({ start, end: Math.max(start, lastTrimEnd) });
      // the line starts on this unit, without its leading spaces
      start = unit.start;
      while (start < unit.end && /\s/.test(src[start])) start += 1;
      end = unit.end;
      lastTrimEnd = unit.tend;
      used = start === unit.start ? unit.w : measure(src.slice(start, unit.end), start);
      // a single unit wider than the box: split it by character
      while (end - start > 1 && measure(src.slice(start, unit.tend), start) * k > edge) {
        let cut = end - 1;
        while (cut > start + 1 && measure(src.slice(start, cut), start) * k > edge) cut -= 1;
        out.push({ start, end: cut });
        start = cut;
        used = measure(src.slice(start, end), start);
      }
    }
    out.push({ start, end: Math.max(start, lastTrimEnd) });
  }
  return out;
}

// Line breaks as [{ start, end }] offsets into text, trailing spaces left out.
function wrapRanges(text, maxWidth, measure) {
  return layoutUnits(text, measureUnits(text, measure), maxWidth, measure);
}

function wrapText(text, maxWidth, measure) {
  return wrapRanges(text, maxWidth, measure).map((r) => String(text).slice(r.start, r.end));
}

// Wraps at width, shrinking the size in 2.5% steps down to MIN_SHRINK until
// the lines fit the block's height (shrink=false: original size only).
// measure(text, offset) is the width at size 1.
function fitWithin(text, block, measured, measure1, width, shrink) {
  const lineHeight = (size) => (block.leading > 0 ? block.leading * (size / block.size) : size * 1.2);
  const limit = block.h * 1.05 + 0.5;
  const steps = shrink ? 20 : 0;
  let fit;
  for (let step = 0; step <= steps; step += 1) {
    const size = (block.size * (40 - step)) / 40;
    const ranges = layoutUnits(text, measured, width, measure1, size);
    const overflow = size + (ranges.length - 1) * lineHeight(size) > limit;
    fit = { size, lineHeight: lineHeight(size), ranges, width, overflow };
    if (!overflow) break;
  }
  fit.lines = fit.ranges.map((r) => String(text).slice(r.start, r.end));
  return fit;
}

// Picks the width and size for a block's translation. In order: a widened
// one-line block (headings, labels) at its original size, the block's own
// width shrinking down to half size, then the full width to the page margin.
// If none fits, the candidate with the fewest lines wins.
// measure(text, size, offset) returns the width in points.
function fitBlock(text, block, measure, maxWidth, growWidth) {
  const measure1 = (str, offset) => measure(str, 1, offset);
  const measured = measureUnits(text, measure1);
  const base = Math.max(block.w, block.size);
  const candidates = [];
  if (growWidth > block.w) candidates.push({ width: growWidth, shrink: false });
  candidates.push({ width: base, shrink: true });
  if (maxWidth > base) candidates.push({ width: maxWidth, shrink: true });
  let best = null;
  for (const { width, shrink } of candidates) {
    const fit = fitWithin(text, block, measured, measure1, width, shrink);
    if (!fit.overflow) return fit;
    if (shrink && (!best || fit.lines.length < best.lines.length)) best = fit;
  }
  return best;
}

// @pdf-lib/fontkit writes a short-format loca table for small subsets but
// does not pad glyphs to an even length, so every glyph after an odd-length
// one points at the wrong bytes and renders blank. Padding fixes the offsets.
const patchedFontkits = new WeakSet();

function patchFontkitSubset(fontkit, fontBytes) {
  if (patchedFontkits.has(fontkit)) return;
  patchedFontkits.add(fontkit);
  const proto = Object.getPrototypeOf(fontkit.create(fontBytes).createSubset());
  if (!proto || typeof proto._addGlyph !== "function" || proto._addGlyphEvenPadded) return;
  const addGlyph = proto._addGlyph;
  proto._addGlyph = function addEvenGlyph(gid) {
    const index = addGlyph.call(this, gid);
    const buf = this.glyf && this.glyf[index];
    if (buf && buf.length % 2) {
      const Ctor = buf.constructor;
      const padded = Ctor && typeof Ctor.alloc === "function" ? Ctor.alloc(buf.length + 1) : new Uint8Array(buf.length + 1);
      padded.set(buf);
      this.glyf[index] = padded;
      this.offset += 1;
    }
    return index;
  };
  proto._addGlyphEvenPadded = true;
}

// Look-alikes for symbols the embedded font lacks (list bullets drawn with
// Wingdings or Segoe UI Symbol in the original). One character for one, so
// the per-character styles stay aligned.
const GLYPH_SUBSTITUTES = {
  "❏": "□", "❑": "□", "❒": "□", "☐": "□", "☑": "■", "☒": "■",
  "►": "▶", "➢": "▶", "➤": "▶", "➔": "→", "➜": "→",
  "✔": "✓", "✗": "×", "✘": "×",
  // Symbol / Wingdings private-use code points
  "\uF0B7": "•", "\uF0A7": "▪", "\uF0D8": "▶", "\uF0FC": "✓",
  "\uF06E": "■", "\uF06F": "□", "\uF071": "□", "\uF076": "◆",
};

// Returns text => text with look-alikes for symbols some of the fonts lack.
// The character sets are read once per document.
function glyphSubstituter(fonts) {
  let sets;
  try {
    sets = fonts.map((f) => new Set(f.getCharacterSet()));
  } catch (_) {
    return (text) => text;
  }
  const has = (ch) => sets.every((set) => set.has(ch.codePointAt(0)));
  return (text) => {
    let out = "";
    for (const ch of text) {
      const sub = GLYPH_SUBSTITUTES[ch];
      out += sub && !has(ch) && has(sub) ? sub : ch;
    }
    return out;
  };
}

function hexToRgb(PDFLib, hex, fallback) {
  const value = /^[0-9a-f]{6}$/i.test(hex || "") ? hex : fallback;
  const n = parseInt(value, 16);
  return PDFLib.rgb(((n >> 16) & 255) / 255, ((n >> 8) & 255) / 255, (n & 255) / 255);
}

// How wide a one-line block may grow: up to the next text block to its
// right on the same lines, the page margin, and 1.8 times its own width.
function freeWidth(meta, pageBlocks, maxWidth) {
  let limit = Math.min(maxWidth, meta.w * 1.8);
  for (const other of pageBlocks) {
    if (other === meta) continue;
    const overlapsY = other.y < meta.y + meta.h && other.y + other.h > meta.y;
    if (overlapsY && other.x >= meta.x + meta.w - 1) limit = Math.min(limit, other.x - meta.x - meta.size * 0.5);
  }
  return Math.max(meta.w, limit);
}

function sameRect(a, b) {
  return a.every((v, i) => Math.abs(v - b[i]) < 0.6);
}

// Link annotations of a page, as { index, dict, rect }.
function pageLinkAnnots(PDFLib, page) {
  const { PDFName, PDFArray, PDFDict, PDFNumber } = PDFLib;
  const annots = page.node.lookupMaybe(PDFName.of("Annots"), PDFArray);
  const out = [];
  if (!annots) return out;
  for (let i = 0; i < annots.size(); i += 1) {
    const dict = annots.lookupMaybe(i, PDFDict);
    if (!dict || dict.lookup(PDFName.of("Subtype")) !== PDFName.of("Link")) continue;
    const rect = dict.lookupMaybe(PDFName.of("Rect"), PDFArray);
    if (!rect || rect.size() !== 4) continue;
    const values = [0, 1, 2, 3].map((k) => {
      const v = rect.lookup(k);
      return v instanceof PDFNumber ? v.asNumber() : 0;
    });
    out.push({ index: i, dict, rect: [Math.min(values[0], values[2]), Math.min(values[1], values[3]), Math.max(values[0], values[2]), Math.max(values[1], values[3])] });
  }
  return out;
}

// Moves links: each original annotation goes, and a copy goes on every
// piece of translated text that carries it. moves: Map(link => rects).
function relinkAnnotations(PDFLib, page, moves) {
  const { PDFName, PDFArray } = PDFLib;
  const context = page.doc.context;
  const annots = page.node.lookupMaybe(PDFName.of("Annots"), PDFArray);
  if (!annots) return;
  const existing = pageLinkAnnots(PDFLib, page);
  const drop = new Set();
  const added = [];
  for (const [link, rects] of moves) {
    const found = existing.find((a) => sameRect(a.rect, link.rect));
    if (!found) continue;
    drop.add(found.index);
    for (const r of rects) {
      const copy = found.dict.clone(context);
      copy.set(PDFName.of("Rect"), context.obj([r.x0, r.y0, r.x1, r.y1].map(round2)));
      copy.delete(PDFName.of("QuadPoints"));
      added.push(context.register(copy));
    }
  }
  for (const index of [...drop].sort((a, b) => b - a)) annots.remove(index);
  for (const ref of added) annots.push(ref);
}

// Removes the original text of each translated block from the page content
// and draws the translation in its place, run by run in the original colors.
// Links move onto the translated words and their underlines are redrawn.
// Blocks whose text cannot be removed that way (form XObjects, invisible OCR
// text) are covered with their background color instead.
// deps: { PDFLib, fontkit, fontBytes, colors: { uid: { fill, ink } } }
async function injectPdfTexts(bytes, translations, metadata, deps) {
  const { PDFLib } = deps;
  let doc;
  try {
    doc = await PDFLib.PDFDocument.load(bytes, { updateMetadata: false });
  } catch (err) {
    if (err && /encrypt/i.test(err.message || err.name || "")) {
      throw new Error("暗号化された PDF には上書きできません。Word 出力を使ってください", { cause: err });
    }
    throw err;
  }
  let font;
  let boldFont;
  if (deps.fontBytes) {
    patchFontkitSubset(deps.fontkit, deps.fontBytes);
    doc.registerFontkit(deps.fontkit);
    font = await doc.embedFont(deps.fontBytes, { subset: true });
    if (deps.boldFontBytes) boldFont = await doc.embedFont(deps.boldFontBytes, { subset: true });
  } else {
    font = await doc.embedFont(PDFLib.StandardFonts.Helvetica);
    boldFont = await doc.embedFont(PDFLib.StandardFonts.HelveticaBold);
  }
  const fontFor = (run) => (run && run.bold && boldFont ? boldFont : font);
  const substitute = glyphSubstituter(boldFont ? [font, boldFont] : [font]);
  const pages = doc.getPages();
  const colors = deps.colors || {};
  let injected = 0;
  let missing = 0;
  const tagArtifacts = [];
  const overflowed = [];
  const flattened = [];
  const targets = [];
  for (const meta of metadata || []) {
    if (translations[meta.id] === undefined || !pages[meta.page]) {
      missing += 1;
      continue;
    }
    const styled = styledText(meta, translations[meta.id]);
    styled.text = substitute(styled.text);
    if (styled.flattened) flattened.push(meta.id);
    if (styled.tagArtifact) tagArtifacts.push(meta.id);
    targets.push({ meta, styled });
  }
  // Take the original text (and the underlines of links that move) out of
  // each page first; pdf-lib's own drawing is appended afterwards.
  const removed = new Set();
  const underlined = new Set(); // links whose underline was taken out
  const sharedForms = new Map();
  const byPage = groupBy(targets, (t) => t.meta.page);
  for (const [index, list] of byPage) {
    // links that move with a styled translation lose their old underline
    const links = [...new Set(list.flatMap(({ meta, styled }) => (
      styled.flattened ? [] : (meta.runs || []).map((r) => r.link).filter(Boolean)
    )))];
    const zones = links.map(({ rect: [x0, y0, x1, y1] }) => ({
      x0: Math.min(x0, x1), y0: Math.min(y0, y1), x1: Math.max(x0, x1), y1: Math.max(y0, y1),
    }));
    const result = rewrite.removePageText(PDFLib, pages[index], list.map((t) => t.meta), zones, sharedForms);
    for (const id of result.done) removed.add(id);
    for (const k of result.underlined) underlined.add(links[k]);
  }
  const blocksByPage = groupBy(metadata || [], (m) => m.page);
  const covered = [];
  const moves = new Map(); // page => Map(link => rects)
  for (const { meta, styled } of targets) {
    const page = pages[meta.page];
    const color = colors[meta.id] || {};
    if (!removed.has(meta.id)) {
      covered.push(meta.id);
      const pad = Math.max(1, meta.size * 0.08);
      page.drawRectangle({
        x: meta.x - pad,
        y: meta.y - pad,
        width: meta.w + pad * 2,
        height: meta.h + pad * 2,
        color: hexToRgb(PDFLib, color.fill, "FFFFFF"),
      });
    }
    const runs = meta.runs && meta.runs.length ? meta.runs : [{ color: null, link: null }];
    const box = page.getMediaBox();
    const maxWidth = box.x + box.width - meta.x - Math.min(36, box.width * 0.05);
    // with a rendered page, growth also stops where the background changes
    let growWidth = meta.lines === 1 ? freeWidth(meta, blocksByPage.get(meta.page), maxWidth) : 0;
    if (typeof color.room === "number") growWidth = Math.min(growWidth, meta.w + Math.max(0, color.room - meta.size * 0.3));
    // measure with each character's own font (bold runs are wider)
    const measure = (str, size, offset) => {
      let width = 0;
      let i = 0;
      while (i < str.length) {
        const style = styled.styles[(offset || 0) + i];
        let j = i + 1;
        while (j < str.length && styled.styles[(offset || 0) + j] === style) j += 1;
        width += fontFor(runs[style]).widthOfTextAtSize(str.slice(i, j), size);
        i = j;
      }
      return width;
    };
    const fit = fitBlock(styled.text, meta, measure, maxWidth, growWidth);
    if (fit.overflow) overflowed.push(meta.id);
    const fallbackInk = color.ink || "1E1E1E";
    // first baseline where the original first line sat, scaled with the size
    let baseline = meta.firstBaseline
      ? meta.y + meta.h - (meta.y + meta.h - meta.firstBaseline) * (fit.size / meta.size)
      : meta.y + meta.h - fit.size * 0.88;
    for (const range of fit.ranges) {
      let x = meta.x;
      let i = range.start;
      while (i < range.end) {
        const style = styled.styles[i];
        let j = i + 1;
        while (j < range.end && styled.styles[j] === style) j += 1;
        const piece = styled.text.slice(i, j);
        const run = runs[style] || runs[0];
        const pieceFont = fontFor(run);
        const width = pieceFont.widthOfTextAtSize(piece, fit.size);
        const ink = hexToRgb(PDFLib, run.color, fallbackInk);
        if (piece.trim()) page.drawText(piece, { x, y: baseline, size: fit.size, font: pieceFont, color: ink });
        if (run.link && !styled.flattened && piece.trim()) {
          if (!moves.has(meta.page)) moves.set(meta.page, new Map());
          const pageMoves = moves.get(meta.page);
          if (!pageMoves.has(run.link)) pageMoves.set(run.link, []);
          pageMoves.get(run.link).push({ x0: x, y0: baseline - fit.size * 0.25, x1: x + width, y1: baseline + fit.size * 0.9 });
          if (underlined.has(run.link)) {
            page.drawRectangle({
              x,
              y: baseline - fit.size * 0.12,
              width,
              height: Math.max(0.5, fit.size * 0.06),
              color: ink,
            });
          }
        }
        x += width;
        i = j;
      }
      baseline -= fit.lineHeight;
    }
    injected += 1;
  }
  for (const [index, pageMoves] of moves) relinkAnnotations(PDFLib, pages[index], pageMoves);
  const out = await doc.save();
  return { bytes: out, injected, missing, flattened, tagArtifacts, overflowed, covered };
}

// The most common text color. A per-channel median would mix a sentence's
// black, red and green words into a color none of them has.
function dominantColor(pixels, channel) {
  const bins = new Map();
  for (const p of pixels) {
    const key = (p[0] >> 5) * 64 + (p[1] >> 5) * 8 + (p[2] >> 5);
    if (!bins.has(key)) bins.set(key, []);
    bins.get(key).push(p);
  }
  let best = [];
  for (const members of bins.values()) if (members.length > best.length) best = members;
  return [0, 1, 2].map((i) => channel(best, i));
}

function groupBy(items, keyOf) {
  const groups = new Map();
  for (const item of items) {
    const key = keyOf(item);
    if (!groups.has(key)) groups.set(key, []);
    groups.get(key).push(item);
  }
  return groups;
}

// Background and text colors of each block, from a rendered page.
// image: { data, width, height } (RGBA), rect: pixel box of the block.
function sampleBlockColors(image, rect) {
  const { data, width, height } = image;
  const x0 = Math.max(0, Math.floor(rect.x0) - 2);
  const y0 = Math.max(0, Math.floor(rect.y0) - 2);
  const x1 = Math.min(width - 1, Math.ceil(rect.x1) + 2);
  const y1 = Math.min(height - 1, Math.ceil(rect.y1) + 2);
  if (x1 <= x0 || y1 <= y0) return null;
  const at = (x, y) => {
    const i = (y * width + x) * 4;
    return [data[i], data[i + 1], data[i + 2]];
  };
  const ring = [];
  for (let x = x0; x <= x1; x += 1) ring.push(at(x, y0), at(x, y1));
  for (let y = y0; y <= y1; y += 1) ring.push(at(x0, y), at(x1, y));
  const channel = (pixels, i) => median(pixels.map((p) => p[i]));
  const fill = [0, 1, 2].map((i) => channel(ring, i));
  const inkPixels = [];
  for (let y = y0 + 1; y < y1; y += 1) {
    for (let x = x0 + 1; x < x1; x += 1) {
      const p = at(x, y);
      if (Math.hypot(p[0] - fill[0], p[1] - fill[1], p[2] - fill[2]) > 60) inkPixels.push(p);
    }
  }
  const lum = 0.2126 * fill[0] + 0.7152 * fill[1] + 0.0722 * fill[2];
  const ink = inkPixels.length < 4
    ? (lum < 140 ? [255, 255, 255] : [30, 30, 30])
    : dominantColor(inkPixels, channel);
  const hex = (p) => p.map((n) => Math.round(n).toString(16).padStart(2, "0")).join("").toUpperCase();
  return { fill: hex(fill), ink: hex(ink) };
}

// How many pixels the block's background continues to its right before
// something else (a box edge, a picture, other text) starts.
function freeRoomRight(image, rect, fillHex) {
  const { data, width, height } = image;
  const fill = [0, 2, 4].map((i) => parseInt(fillHex.slice(i, i + 2), 16));
  const y0 = Math.max(0, Math.floor(rect.y0));
  const y1 = Math.min(height - 1, Math.ceil(rect.y1));
  const rows = [y0, Math.round((y0 + y1) / 2), y1];
  let x = Math.min(width - 1, Math.ceil(rect.x1) + 1);
  const start = x;
  for (; x < width; x += 1) {
    const differs = rows.some((y) => {
      const i = (y * width + x) * 4;
      return Math.hypot(data[i] - fill[0], data[i + 1] - fill[1], data[i + 2] - fill[2]) > 40;
    });
    if (differs) break;
  }
  return Math.max(0, x - start);
}

// Browser only: renders each page that has blocks and samples their colors.
async function samplePdfColors(pdf, metadata, onPage) {
  const byPage = groupBy(metadata, (m) => m.page);
  const colors = {};
  let done = 0;
  for (const [index, metas] of byPage) {
    done += 1;
    if (onPage) onPage(done, byPage.size);
    const page = await pdf.getPage(index + 1);
    const viewport = page.getViewport({ scale: 1.5 });
    const canvas = document.createElement("canvas");
    canvas.width = Math.ceil(viewport.width);
    canvas.height = Math.ceil(viewport.height);
    const ctx = canvas.getContext("2d", { willReadFrequently: true });
    ctx.fillStyle = "#ffffff";
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    await page.render({ canvasContext: ctx, viewport }).promise;
    const image = ctx.getImageData(0, 0, canvas.width, canvas.height);
    for (const meta of metas) {
      const [ax, ay, bx, by] = viewport.convertToViewportRectangle([meta.x, meta.y, meta.x + meta.w, meta.y + meta.h]);
      const sampled = sampleBlockColors(image, {
        x0: Math.min(ax, bx),
        y0: Math.min(ay, by),
        x1: Math.max(ax, bx),
        y1: Math.max(ay, by),
      });
      if (sampled) {
        if (meta.lines === 1) {
          sampled.room = freeRoomRight(image, {
            x0: Math.min(ax, bx), y0: Math.min(ay, by), x1: Math.max(ax, bx), y1: Math.max(ay, by),
          }, sampled.fill) / 1.5;
        }
        colors[meta.id] = sampled;
      }
    }
    canvas.width = 0;
    canvas.height = 0;
    if (page.cleanup) page.cleanup();
  }
  return colors;
}

function escapeXml(text) {
  return String(text)
    .replace(/[\u0000-\u0008\u000B\u000C\u000E-\u001F]/g, "")
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

function runXml(text, rPr) {
  const parts = String(text).split(/\r?\n/);
  const body = parts
    .map((part, i) => `${i ? "<w:br/>" : ""}<w:t xml:space="preserve">${escapeXml(part)}</w:t>`)
    .join("");
  return `<w:r>${rPr}${body}</w:r>`;
}

function fontXml(font) {
  if (!font) return "";
  const f = escapeXml(font);
  return `<w:rFonts w:ascii="${f}" w:hAnsi="${f}" w:eastAsia="${f}" w:cs="${f}"/>`;
}

// One paragraph per block, in page order, a page break between pages.
// Untranslated blocks keep the original text. Returns a JSZip.
function buildDocxFromPdf(JSZipCtor, extracted, translations, options) {
  const opts = options || {};
  const metadata = extracted.metadata || [];
  const firstPage = (extracted.pages && extracted.pages[0]) || { width: 595, height: 842 };
  const paras = [];
  let injected = 0;
  let missing = 0;
  const tagArtifacts = [];
  const flattened = [];
  const hyperlinks = [];
  let lastPage = metadata.length ? metadata[0].page : 0;
  for (const meta of metadata) {
    const translated = translations[meta.id];
    let styled;
    if (translated === undefined) {
      missing += 1;
      const runs = meta.runs && meta.runs.length ? meta.runs : [{ text: meta.text || "" }];
      styled = { text: "", styles: [] };
      runs.forEach((run, k) => {
        styled.text += run.text;
        for (let i = 0; i < run.text.length; i += 1) styled.styles.push(k);
      });
    } else {
      styled = styledText(meta, translated);
      if (styled.tagArtifact) tagArtifacts.push(meta.id);
      if (styled.flattened) flattened.push(meta.id);
      injected += 1;
    }
    const pageBreak = meta.page !== lastPage;
    lastPage = meta.page;
    const halfPoints = Math.max(16, Math.min(80, Math.round(meta.size * 2)));
    const font = meta.title ? opts.titleFont : opts.bodyFont;
    const runs = meta.runs && meta.runs.length ? meta.runs : [{ color: null, link: null }];
    const pPr = `<w:pPr>${pageBreak ? "<w:pageBreakBefore/>" : ""}${meta.title ? '<w:outlineLvl w:val="0"/>' : ""}<w:spacing w:after="120"/></w:pPr>`;
    let body = "";
    let i = 0;
    while (i < styled.text.length) {
      const style = styled.styles[i];
      let j = i + 1;
      while (j < styled.text.length && styled.styles[j] === style) j += 1;
      const run = runs[style] || runs[0];
      const color = run.color && run.color !== "000000" ? `<w:color w:val="${run.color}"/>` : "";
      const url = !styled.flattened && run.link && run.link.url;
      const underline = url ? '<w:u w:val="single"/>' : "";
      const rPr = `<w:rPr>${fontXml(font)}${meta.title || run.bold ? "<w:b/>" : ""}${color}${underline}<w:sz w:val="${halfPoints}"/><w:szCs w:val="${halfPoints}"/></w:rPr>`;
      const xml = runXml(styled.text.slice(i, j), rPr);
      if (url) {
        hyperlinks.push(url);
        body += `<w:hyperlink r:id="rIdLink${hyperlinks.length}">${xml}</w:hyperlink>`;
      } else {
        body += xml;
      }
      i = j;
    }
    paras.push(`<w:p>${pPr}${body}</w:p>`);
  }
  if (!paras.length) paras.push("<w:p/>");
  const twips = (pt) => Math.round(pt * 20);
  const sect = `<w:sectPr><w:pgSz w:w="${twips(firstPage.width)}" w:h="${twips(firstPage.height)}"${firstPage.width > firstPage.height ? ' w:orient="landscape"' : ""}/>` +
    '<w:pgMar w:top="1134" w:right="1134" w:bottom="1134" w:left="1134" w:header="567" w:footer="567" w:gutter="0"/></w:sectPr>';
  const documentXml = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n' +
    '<w:document xmlns:w="http://schemas.openxmlformats.org/wordprocessingml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">' +
    `<w:body>${paras.join("")}${sect}</w:body></w:document>`;
  const zip = new JSZipCtor();
  zip.file("[Content_Types].xml", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n' +
    '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">' +
    '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>' +
    '<Default Extension="xml" ContentType="application/xml"/>' +
    '<Override PartName="/word/document.xml" ContentType="application/vnd.openxmlformats-officedocument.wordprocessingml.document.main+xml"/>' +
    "</Types>");
  zip.file("_rels/.rels", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n' +
    '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">' +
    '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="word/document.xml"/>' +
    "</Relationships>");
  zip.file("word/document.xml", documentXml);
  zip.file("word/_rels/document.xml.rels", '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>\n' +
    '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">' +
    hyperlinks.map((url, k) => `<Relationship Id="rIdLink${k + 1}" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/hyperlink" Target="${escapeXml(url)}" TargetMode="External"/>`).join("") +
    "</Relationships>");
  return { zip, injected, missing, flattened, tagArtifacts };
}

const api = {
  PDF_FONT_URL,
  PDF_BOLD_FONT_URL,
  PDF_FONT_NAME,
  itemsToLines,
  linesToBlocks,
  extractPdfTexts,
  wrapText,
  wrapRanges,
  styledText,
  fitBlock,
  injectPdfTexts,
  sampleBlockColors,
  freeRoomRight,
  samplePdfColors,
  buildDocxFromPdf,
};

if (typeof module !== "undefined" && module.exports) module.exports = api;
if (typeof window !== "undefined") Object.assign(window, api);
})();
