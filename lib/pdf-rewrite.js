// Vendored from https://github.com/symmr/ppt-translation-supporter/blob/5638b5d/docs/pdf-rewrite.js
// (MIT License, Copyright (c) 2026 symmr). Update by copying the file again
// rather than editing it here.
// Removes the original text of translated blocks from a page's content
// stream, so the rewritten PDF no longer carries it (not drawn, not found by
// search or copy). Each removed string is replaced by a TJ advance of the
// same width, so text that follows on the same line keeps its position.
// Text in form XObjects and invisible text (OCR layers) is left alone; the
// caller covers those blocks instead.
(function () {
"use strict";

const WS = new Set([0, 9, 10, 12, 13, 32]);
const DELIM = new Set([40, 41, 60, 62, 91, 93, 123, 125, 47, 37]);
const IDENTITY = [1, 0, 0, 1, 0, 0];

function mul(m, n) {
  return [
    m[0] * n[0] + m[1] * n[2],
    m[0] * n[1] + m[1] * n[3],
    m[2] * n[0] + m[3] * n[2],
    m[2] * n[1] + m[3] * n[3],
    m[4] * n[0] + m[5] * n[2] + n[4],
    m[4] * n[1] + m[5] * n[3] + n[5],
  ];
}

function apply(m, x, y) {
  return [m[0] * x + m[2] * y + m[4], m[1] * x + m[3] * y + m[5]];
}

function latin1(bytes, start, end) {
  let out = "";
  for (let i = start; i < end; i += 1) out += String.fromCharCode(bytes[i]);
  return out;
}

// Content stream lexer. Tokens keep their byte range so untouched operators
// are copied through byte for byte.
function tokenize(bytes) {
  const tokens = [];
  const n = bytes.length;
  let i = 0;
  while (i < n) {
    const c = bytes[i];
    if (WS.has(c)) { i += 1; continue; }
    const start = i;
    if (c === 37) { // % comment
      while (i < n && bytes[i] !== 10 && bytes[i] !== 13) i += 1;
      continue;
    }
    if (c === 40) { // ( literal string )
      const out = [];
      let depth = 1;
      i += 1;
      while (i < n && depth > 0) {
        const ch = bytes[i];
        if (ch === 92) {
          const nx = bytes[i + 1];
          i += 2;
          if (nx === 110) out.push(10);
          else if (nx === 114) out.push(13);
          else if (nx === 116) out.push(9);
          else if (nx === 98) out.push(8);
          else if (nx === 102) out.push(12);
          else if (nx === 13) { if (bytes[i] === 10) i += 1; }
          else if (nx === 10) { /* line continuation */ }
          else if (nx >= 48 && nx <= 55) {
            let v = nx - 48;
            for (let k = 0; k < 2 && bytes[i] >= 48 && bytes[i] <= 55; k += 1) {
              v = v * 8 + (bytes[i] - 48);
              i += 1;
            }
            out.push(v & 255);
          } else if (nx !== undefined) out.push(nx);
          continue;
        }
        if (ch === 40) depth += 1;
        if (ch === 41) {
          depth -= 1;
          if (depth === 0) { i += 1; break; }
        }
        out.push(ch);
        i += 1;
      }
      tokens.push({ type: "str", value: Uint8Array.from(out), start, end: i });
      continue;
    }
    if (c === 60 && bytes[i + 1] === 60) { tokens.push({ type: "<<", start, end: i + 2 }); i += 2; continue; }
    if (c === 62 && bytes[i + 1] === 62) { tokens.push({ type: ">>", start, end: i + 2 }); i += 2; continue; }
    if (c === 60) { // <hex string>
      i += 1;
      let hex = "";
      while (i < n && bytes[i] !== 62) {
        const ch = bytes[i];
        if (!WS.has(ch)) hex += String.fromCharCode(ch);
        i += 1;
      }
      i += 1;
      if (hex.length % 2) hex += "0";
      const out = new Uint8Array(hex.length / 2);
      for (let k = 0; k < out.length; k += 1) out[k] = parseInt(hex.substr(k * 2, 2), 16) || 0;
      tokens.push({ type: "str", value: out, start, end: i });
      continue;
    }
    if (c === 91 || c === 93 || c === 123 || c === 125) {
      tokens.push({ type: String.fromCharCode(c), start, end: i + 1 });
      i += 1;
      continue;
    }
    if (c === 47) { // /Name
      i += 1;
      while (i < n && !WS.has(bytes[i]) && !DELIM.has(bytes[i])) i += 1;
      const raw = latin1(bytes, start + 1, i).replace(/#([0-9a-fA-F]{2})/g, (_, h) => String.fromCharCode(parseInt(h, 16)));
      tokens.push({ type: "name", value: raw, start, end: i });
      continue;
    }
    while (i < n && !WS.has(bytes[i]) && !DELIM.has(bytes[i])) i += 1;
    if (i === start) { i += 1; continue; } // stray delimiter such as ")"
    const word = latin1(bytes, start, i);
    if (/^[+-]?(\d+\.?\d*|\.\d+)$/.test(word)) {
      tokens.push({ type: "num", value: parseFloat(word), start, end: i });
      continue;
    }
    tokens.push({ type: "op", value: word, start, end: i });
    if (word === "ID") {
      // inline image data runs to the next whitespace-delimited EI
      let j = i + 1;
      while (j < n) {
        if (bytes[j] === 69 && bytes[j + 1] === 73 && WS.has(bytes[j - 1]) && (j + 2 >= n || WS.has(bytes[j + 2]))) break;
        j += 1;
      }
      tokens.push({ type: "op", value: "EI", start: j, end: Math.min(n, j + 2) });
      i = Math.min(n, j + 2);
    }
  }
  return tokens;
}

// Operators with their operand values and the byte range they span.
function parseOps(bytes) {
  const tokens = tokenize(bytes);
  const ops = [];
  let operands = [];
  let operandStart = -1;
  const stack = [];
  const push = (value, start) => {
    if (stack.length) stack[stack.length - 1].push(value);
    else {
      if (operandStart < 0) operandStart = start;
      operands.push(value);
    }
  };
  for (const tok of tokens) {
    if (tok.type === "[" || tok.type === "<<" || tok.type === "{") {
      if (!stack.length && operandStart < 0) operandStart = tok.start;
      stack.push([]);
      continue;
    }
    if (tok.type === "]" || tok.type === ">>" || tok.type === "}") {
      const value = stack.pop() || [];
      if (tok.type !== "]") value.dict = true;
      push(value, tok.start);
      continue;
    }
    if (tok.type === "op" && !stack.length) {
      ops.push({ op: tok.value, operands, start: operandStart < 0 ? tok.start : operandStart, end: tok.end });
      operands = [];
      operandStart = -1;
      continue;
    }
    if (tok.type === "op") { push({ keyword: tok.value }, tok.start); continue; }
    push(tok.type === "name" ? { name: tok.value } : tok.value, tok.start);
  }
  return ops;
}

// Glyph widths per font resource, in 1/1000 text space units.
// fonts: { [resourceName]: { twoByte, width(code) } }
function codesOf(font, bytes) {
  const codes = [];
  if (font && font.twoByte) {
    for (let i = 0; i + 1 < bytes.length; i += 2) codes.push((bytes[i] << 8) | bytes[i + 1]);
  } else {
    for (const b of bytes) codes.push(b);
  }
  return codes;
}

function stringAdvance(state, bytes) {
  const font = state.font;
  let tx = 0;
  for (const code of codesOf(font, bytes)) {
    const w0 = font ? font.width(code) : 500;
    const wordSpace = (!font || !font.twoByte) && code === 32 ? state.Tw : 0;
    tx += ((w0 / 1000) * state.Tfs + state.Tc + wordSpace) * state.Th;
  }
  return tx;
}

function fmt(n) {
  if (!Number.isFinite(n)) return "0";
  const s = n.toFixed(3).replace(/\.?0+$/, "");
  return s === "-0" ? "0" : s;
}

function hexOf(bytes) {
  let s = "<";
  for (const b of bytes) s += b.toString(16).padStart(2, "0");
  return `${s}>`;
}

function inRect(rects, x, y) {
  for (let k = 0; k < rects.length; k += 1) {
    const r = rects[k];
    if (x >= r.x0 && x <= r.x1 && y >= r.y0 && y <= r.y1) return k;
  }
  return -1;
}

function clamp01(v) {
  return Math.max(0, Math.min(1, typeof v === "number" ? v : 0));
}

function colorHex(values) {
  let rgb;
  if (values.length === 1) rgb = [values[0], values[0], values[0]];
  else if (values.length === 3) rgb = values;
  else if (values.length === 4) {
    const [c, m, y, k] = values.map(clamp01);
    rgb = [(1 - c) * (1 - k), (1 - m) * (1 - k), (1 - y) * (1 - k)];
  } else return null;
  return rgb.map((v) => Math.round(clamp01(v) * 255).toString(16).padStart(2, "0")).join("").toUpperCase();
}

const PATH_OPS = new Set(["m", "l", "c", "v", "y", "h", "re"]);
const PAINT_OPS = new Set(["S", "s", "f", "F", "f*", "B", "B*", "b", "b*", "n"]);

// Interprets a content stream. For every string shown, onString(seg) may
// return true to remove it (it becomes a TJ advance of the same width). For
// every painted path, onPath(path) may return true to remove it.
// seg: { x0, y0, x1, mx, my, size, color, visible, count, horizontal }
// path: { ops, paint, bbox, lineWidth }
// handlers.form(name) may resolve a form XObject drawn with Do into
// { bytes, fonts, matrix, nested, finish(result) }; its content is walked
// with the same handlers and finish() decides what to do with the edits.
function walkContent(bytes, fonts, handlers, initialGs, depth) {
  const ops = parseOps(bytes);
  const edits = [];
  let gs = initialGs ? { ...initialGs, ctm: initialGs.ctm.slice() } : {
    ctm: IDENTITY.slice(), Tc: 0, Tw: 0, Th: 1, TL: 0, Tfs: 0, font: null, rise: 0, Tr: 0, fill: "000000", lw: 1, alpha: 1,
  };
  const level = depth || 0;
  const gstates = handlers.gstates || {};
  const saved = [];
  let tm = IDENTITY.slice();
  let tlm = IDENTITY.slice();
  let path = null;
  let clip = false;
  const num = (v, d) => (typeof v === "number" ? v : d);
  const onString = handlers.onString || (() => false);
  const onPath = handlers.onPath || (() => false);

  // Shows one TJ-style array; returns the replacement elements, or null when
  // nothing in it was removed.
  const show = (elements) => {
    const out = [];
    let changed = false;
    for (const el of elements) {
      if (typeof el === "number") {
        out.push(el);
        tm = mul([1, 0, 0, 1, (-el / 1000) * gs.Tfs * gs.Th, 0], tm);
        continue;
      }
      if (!(el instanceof Uint8Array)) continue;
      const tx = stringAdvance(gs, el);
      const at = mul(tm, gs.ctm);
      const [x0, y0] = apply(at, 0, gs.rise);
      const [x1] = apply(at, tx, gs.rise);
      const [mx, my] = apply(at, tx / 2, gs.rise + gs.Tfs * 0.3);
      const scale = gs.Tfs * gs.Th;
      const seg = {
        x0, y0, x1, mx, my,
        size: Math.abs(gs.Tfs) * Math.hypot(at[2], at[3]),
        color: gs.fill,
        visible: gs.Tr !== 3 && gs.Tr !== 7 && gs.alpha > 0.02,
        count: codesOf(gs.font, el).length,
        font: (gs.font && gs.font.base) || "",
        horizontal: at[0] > 0 && Math.abs(at[1]) <= at[0] * 0.02 && Math.abs(at[2]) <= Math.abs(at[3]) * 0.02,
      };
      if (el.length && scale && onString(seg)) {
        out.push(-(tx / scale) * 1000);
        changed = true;
      } else {
        out.push(el);
      }
      tm = mul([1, 0, 0, 1, tx, 0], tm);
    }
    return changed ? out : null;
  };
  const serialize = (elements) => `[${elements.map((el) => (typeof el === "number" ? fmt(el) : hexOf(el))).join(" ")}] TJ`;
  const nextLine = () => {
    tlm = mul([1, 0, 0, 1, 0, -gs.TL], tlm);
    tm = tlm.slice();
  };
  const addPoint = (x, y) => {
    const [ux, uy] = apply(gs.ctm, x, y);
    const b = path.bbox;
    b.x0 = Math.min(b.x0, ux); b.y0 = Math.min(b.y0, uy);
    b.x1 = Math.max(b.x1, ux); b.y1 = Math.max(b.y1, uy);
  };
  const setFill = (values) => {
    const hex = values.every((v) => typeof v === "number") ? colorHex(values) : null;
    gs.fill = hex;
  };

  for (const { op, operands: a, start, end } of ops) {
    if (PATH_OPS.has(op)) {
      if (!path) path = { start, ops: [], bbox: { x0: Infinity, y0: Infinity, x1: -Infinity, y1: -Infinity } };
      path.ops.push(op);
      const n = a.map((v) => num(v, 0));
      if (op === "re" && n.length >= 4) {
        addPoint(n[0], n[1]); addPoint(n[0] + n[2], n[1]);
        addPoint(n[0], n[1] + n[3]); addPoint(n[0] + n[2], n[1] + n[3]);
      } else {
        for (let k = 0; k + 1 < n.length; k += 2) addPoint(n[k], n[k + 1]);
      }
      continue;
    }
    if (op === "W" || op === "W*") { clip = true; continue; }
    if (PAINT_OPS.has(op)) {
      if (path && !clip && op !== "n") {
        const lineWidth = gs.lw * Math.hypot(gs.ctm[0], gs.ctm[1]);
        if (onPath({ ops: path.ops, paint: op, bbox: path.bbox, lineWidth })) edits.push({ start: path.start, end, text: "" });
      }
      path = null;
      clip = false;
      continue;
    }
    switch (op) {
      case "q": saved.push({ ...gs, ctm: gs.ctm.slice() }); break;
      case "Q": if (saved.length) gs = saved.pop(); break;
      case "cm":
        if (a.length >= 6) gs.ctm = mul(a.slice(0, 6).map((v) => num(v, 0)), gs.ctm);
        break;
      case "w": gs.lw = num(a[0], 1); break;
      case "gs": {
        const state = a[0] && gstates[a[0].name];
        if (state && typeof state.ca === "number") gs.alpha = state.ca;
        break;
      }
      case "g": case "rg": case "k": setFill(a); break;
      case "sc": case "scn": setFill(a); break;
      case "cs": gs.fill = a[0] && a[0].name === "Pattern" ? null : "000000"; break;
      case "BT": tm = IDENTITY.slice(); tlm = IDENTITY.slice(); break;
      case "Tc": gs.Tc = num(a[0], 0); break;
      case "Tw": gs.Tw = num(a[0], 0); break;
      case "Tz": gs.Th = num(a[0], 100) / 100; break;
      case "TL": gs.TL = num(a[0], 0); break;
      case "Ts": gs.rise = num(a[0], 0); break;
      case "Tr": gs.Tr = num(a[0], 0); break;
      case "Tf":
        gs.font = (a[0] && fonts[a[0].name]) || null;
        gs.Tfs = num(a[1], 0);
        break;
      case "Td":
      case "TD":
        if (op === "TD") gs.TL = -num(a[1], 0);
        tlm = mul([1, 0, 0, 1, num(a[0], 0), num(a[1], 0)], tlm);
        tm = tlm.slice();
        break;
      case "Tm":
        if (a.length >= 6) {
          tlm = a.slice(0, 6).map((v) => num(v, 0));
          tm = tlm.slice();
        }
        break;
      case "T*": nextLine(); break;
      case "Do": {
        const form = handlers.form && level < 6 && a[0] && a[0].name ? handlers.form(a[0].name) : null;
        if (form) {
          const inner = { ...gs, ctm: mul(form.matrix, gs.ctm) };
          form.finish(walkContent(form.bytes, form.fonts, { ...handlers, form: form.nested, gstates: form.gstates }, inner, level + 1));
        }
        break;
      }
      case "Tj": {
        const out = a[0] instanceof Uint8Array ? show([a[0]]) : null;
        if (out) edits.push({ start, end, text: serialize(out) });
        break;
      }
      case "TJ": {
        const out = Array.isArray(a[0]) ? show(a[0]) : null;
        if (out) edits.push({ start, end, text: serialize(out) });
        break;
      }
      case "'": {
        nextLine();
        const out = a[0] instanceof Uint8Array ? show([a[0]]) : null;
        if (out) edits.push({ start, end, text: `T* ${serialize(out)}` });
        break;
      }
      case "\"": {
        gs.Tw = num(a[0], 0);
        gs.Tc = num(a[1], 0);
        nextLine();
        const out = a[2] instanceof Uint8Array ? show([a[2]]) : null;
        if (out) edits.push({ start, end, text: `${fmt(gs.Tw)} Tw ${fmt(gs.Tc)} Tc T* ${serialize(out)}` });
        break;
      }
      default:
        break;
    }
  }
  return { bytes: applyEdits(bytes, edits), removed: edits.length };
}

function applyEdits(bytes, edits) {
  if (!edits.length) return bytes;
  edits.sort((p, q) => p.start - q.start);
  const parts = [];
  let pos = 0;
  let size = 0;
  for (const edit of edits) {
    if (edit.start < pos) continue;
    const head = bytes.subarray(pos, edit.start);
    const body = Uint8Array.from(edit.text, (ch) => ch.charCodeAt(0));
    parts.push(head, body);
    size += head.length + body.length;
    pos = edit.end;
  }
  const tail = bytes.subarray(pos);
  parts.push(tail);
  size += tail.length;
  const out = new Uint8Array(size);
  let at = 0;
  for (const part of parts) {
    out.set(part, at);
    at += part.length;
  }
  return out;
}

// A thin horizontal bar (an underline) lying at the bottom of a zone.
function underlineZone(path, zones) {
  const b = path.bbox;
  if (!Number.isFinite(b.x0)) return -1;
  const height = b.y1 - b.y0;
  const width = b.x1 - b.x0;
  const straight = path.ops.every((op) => op === "m" || op === "l" || op === "h" || op === "re");
  const filledBar = straight && /^[fF]/.test(path.paint) && height <= 2.5;
  const strokedLine = straight && /^[Ss]$/.test(path.paint) && height <= 0.5 && path.lineWidth <= 2.5;
  if (!(filledBar || strokedLine) || width < 2) return -1;
  const cy = (b.y0 + b.y1) / 2;
  for (let k = 0; k < zones.length; k += 1) {
    const z = zones[k];
    if (b.x0 >= z.x0 - 2 && b.x1 <= z.x1 + 2 && cy >= z.y0 - 3 && cy <= z.y0 + (z.y1 - z.y0) * 0.35) return k;
  }
  return -1;
}

// bytes: decoded page content. rects: [{ x0, y0, x1, y1 }] in user space.
// zones: link rects whose underlines go too. Returns the new content, how
// many visible strings went per rect, and how many underlines per zone.
function removeTextInRects(bytes, rects, fonts, zones, form, gstates) {
  const hits = new Array(rects.length).fill(0);
  const underlines = new Array((zones || []).length).fill(0);
  const result = walkContent(bytes, fonts, {
    onString: (seg) => {
      const hit = inRect(rects, seg.mx, seg.my);
      if (hit < 0) return false;
      if (seg.visible) hits[hit] += 1;
      return true;
    },
    onPath: (path) => {
      if (!zones || !zones.length) return false;
      const zone = underlineZone(path, zones);
      if (zone < 0) return false;
      underlines[zone] += 1;
      return true;
    },
    form,
    gstates,
  });
  return { bytes: result.bytes, hits, underlines, removed: result.removed };
}

// Horizontal strings with their position, fill color and visibility.
function collectTextSegments(bytes, fonts, form, gstates) {
  const segments = [];
  walkContent(bytes, fonts, {
    onString: (seg) => {
      if (seg.horizontal) segments.push(seg);
      return false;
    },
    form,
    gstates,
  });
  return segments;
}

// --- pdf-lib side -----------------------------------------------------------

function numberOf(PDFLib, obj) {
  return obj instanceof PDFLib.PDFNumber ? obj.asNumber() : undefined;
}

function fontWidths(PDFLib, context, fontDict) {
  const { PDFName, PDFArray, PDFDict } = PDFLib;
  const subtype = fontDict.lookup(PDFName.of("Subtype"));
  if (subtype === PDFName.of("Type0")) {
    const descendants = fontDict.lookupMaybe(PDFName.of("DescendantFonts"), PDFArray);
    const cid = descendants && descendants.size() ? descendants.lookupMaybe(0, PDFDict) : null;
    const map = new Map();
    let dw = 1000;
    if (cid) {
      dw = numberOf(PDFLib, cid.lookup(PDFName.of("DW"))) ?? 1000;
      const w = cid.lookupMaybe(PDFName.of("W"), PDFArray);
      if (w) {
        let i = 0;
        while (i < w.size()) {
          const first = numberOf(PDFLib, w.lookup(i));
          const next = w.lookup(i + 1);
          if (first === undefined) break;
          if (next instanceof PDFArray) {
            for (let k = 0; k < next.size(); k += 1) map.set(first + k, numberOf(PDFLib, next.lookup(k)) ?? dw);
            i += 2;
          } else {
            const last = numberOf(PDFLib, next);
            const value = numberOf(PDFLib, w.lookup(i + 2)) ?? dw;
            if (last === undefined) break;
            for (let c = first; c <= last && c - first < 65536; c += 1) map.set(c, value);
            i += 3;
          }
        }
      }
    }
    // Identity-H and the other two-byte CMaps; CID = code for Identity
    return { twoByte: true, width: (code) => (map.has(code) ? map.get(code) : dw) };
  }
  const first = numberOf(PDFLib, fontDict.lookup(PDFName.of("FirstChar"))) ?? 0;
  const widths = fontDict.lookupMaybe(PDFName.of("Widths"), PDFArray);
  const descriptor = fontDict.lookupMaybe(PDFName.of("FontDescriptor"), PDFDict);
  const missing = (descriptor && numberOf(PDFLib, descriptor.lookup(PDFName.of("MissingWidth")))) || 500;
  const list = [];
  if (widths) for (let k = 0; k < widths.size(); k += 1) list.push(numberOf(PDFLib, widths.lookup(k)) ?? missing);
  if (!widths) {
    // the standard 14 fonts may leave out Widths; use their built-in metrics
    const base = fontDict.lookup(PDFName.of("BaseFont"));
    const name = base instanceof PDFName ? base.decodeText() : "";
    const standard = Object.values(PDFLib.StandardFonts || {}).find((f) => f === name.replace(/^[A-Z]{6}\+/, ""));
    if (standard && PDFLib.StandardFontEmbedder) {
      const embedder = PDFLib.StandardFontEmbedder.for(standard);
      const cache = new Map();
      return {
        twoByte: false,
        width: (code) => {
          if (!cache.has(code)) {
            let w = missing;
            try { w = embedder.widthOfTextAtSize(String.fromCharCode(code), 1000); } catch (_) { /* not encodable */ }
            cache.set(code, w);
          }
          return cache.get(code);
        },
      };
    }
  }
  return {
    twoByte: false,
    width: (code) => {
      const value = list[code - first];
      return value === undefined ? missing : value;
    },
  };
}

function pageFonts(PDFLib, page) {
  return resourceFonts(PDFLib, page.doc.context, page.node.Resources());
}

// Fill alpha (ca) of each ExtGState, to tell transparent text apart.
function resourceGStates(PDFLib, context, resources) {
  const { PDFName, PDFDict, PDFNumber } = PDFLib;
  const out = {};
  const dict = resources && resources.lookupMaybe(PDFName.of("ExtGState"), PDFDict);
  if (!dict) return out;
  for (const [key, value] of dict.entries()) {
    const state = context.lookupMaybe(value, PDFDict);
    const ca = state && state.lookup(PDFName.of("ca"));
    out[key.decodeText()] = { ca: ca instanceof PDFNumber ? ca.asNumber() : undefined };
  }
  return out;
}

function resourceFonts(PDFLib, context, resources) {
  const { PDFName, PDFDict } = PDFLib;
  const fonts = {};
  const fontRes = resources && resources.lookupMaybe(PDFName.of("Font"), PDFDict);
  if (!fontRes) return fonts;
  for (const [key, value] of fontRes.entries()) {
    const dict = context.lookupMaybe(value, PDFDict);
    if (!dict) continue;
    try {
      const info = fontWidths(PDFLib, context, dict);
      const base = dict.lookup(PDFLib.PDFName.of("BaseFont"));
      // "ABCDEF+Name": the subset prefix differs between subsets of one font
      info.base = base instanceof PDFLib.PDFName ? base.decodeText().replace(/^[A-Z]{6}\+/, "") : "";
      fonts[key.decodeText ? key.decodeText() : key.asString().slice(1)] = info;
    } catch (_) {
      // unreadable font dict: its text stays and the block gets covered
    }
  }
  return fonts;
}

function pageContentBytes(PDFLib, page) {
  const { PDFArray, PDFRawStream } = PDFLib;
  const contents = page.node.Contents();
  const streams = [];
  if (contents instanceof PDFArray) {
    for (let k = 0; k < contents.size(); k += 1) streams.push(contents.lookup(k));
  } else if (contents) {
    streams.push(contents);
  }
  const chunks = [];
  for (const stream of streams) {
    if (!(stream instanceof PDFRawStream)) return null;
    chunks.push(PDFLib.decodePDFRawStream(stream).decode());
  }
  let size = 0;
  for (const chunk of chunks) size += chunk.length + 1;
  const out = new Uint8Array(size);
  let at = 0;
  for (const chunk of chunks) {
    out.set(chunk, at);
    at += chunk.length;
    out[at] = 10; // operators never continue across stream boundaries
    at += 1;
  }
  return out;
}

// Resolves form XObjects for walkContent. shared (one Map per document)
// keeps each form, read once: its original content (so a header form drawn
// on every page is judged against the same bytes and rewritten once, in
// place, at its own reference), its fonts and its matrix. write=false only
// reads.
function formResolver(PDFLib, context, resources, shared, write) {
  const { PDFName, PDFDict, PDFArray, PDFRawStream, PDFNumber, PDFRef } = PDFLib;
  const xobjects = resources && resources.lookupMaybe(PDFName.of("XObject"), PDFDict);
  return (name) => {
    const ref = xobjects && xobjects.get(PDFName.of(name));
    if (!(ref instanceof PDFRef)) return null;
    const key = ref.toString();
    if (!shared.has(key)) shared.set(key, readForm(ref));
    const form = shared.get(key);
    if (!form) return null;
    return {
      ...form,
      // a form without its own resources uses the resources it is drawn with
      fonts: form.fonts || resourceFonts(PDFLib, context, resources),
      gstates: form.gstates || resourceGStates(PDFLib, context, resources),
      nested: form.nested || formResolver(PDFLib, context, resources, shared, write),
      finish: (result) => {
        if (!write || form.written || !result.removed) return;
        const dict = {};
        for (const [k, v] of form.stream.dict.entries()) {
          if (!["Filter", "DecodeParms", "Length"].includes(k.decodeText())) dict[k.decodeText()] = v;
        }
        context.assign(ref, context.flateStream(result.bytes, dict));
        form.written = true;
      },
    };
  };

  function readForm(ref) {
    const stream = context.lookup(ref);
    if (!(stream instanceof PDFRawStream) || stream.dict.lookup(PDFName.of("Subtype")) !== PDFName.of("Form")) return null;
    let bytes;
    try {
      bytes = PDFLib.decodePDFRawStream(stream).decode();
    } catch (_) {
      return null;
    }
    const own = stream.dict.lookupMaybe(PDFName.of("Resources"), PDFDict);
    const m = stream.dict.lookupMaybe(PDFName.of("Matrix"), PDFArray);
    return {
      stream,
      bytes,
      written: false,
      matrix: m && m.size() === 6 ? [0, 1, 2, 3, 4, 5].map((k) => numberOf(PDFLib, m.lookup(k)) || 0) : IDENTITY.slice(),
      fonts: own ? resourceFonts(PDFLib, context, own) : null,
      gstates: own ? resourceGStates(PDFLib, context, own) : null,
      nested: own ? formResolver(PDFLib, context, own, shared, write) : null,
    };
  }
}

// Rewrites one page. blocks: metadata entries; zones: link rects whose
// underlines should go too; shared: a Map kept across the pages of one
// document (form XObjects). Returns the ids whose original text was removed
// (the rest still need a cover) and the indexes of zones that lost an
// underline.
function removePageText(PDFLib, page, blocks, zones, shared) {
  const none = { done: new Set(), underlined: new Set() };
  if (!blocks.length) return none;
  let content;
  try {
    content = pageContentBytes(PDFLib, page);
  } catch (_) {
    content = null;
  }
  if (!content) return none;
  const rects = blocks.map((b) => ({
    x0: b.x - b.size * 0.5,
    y0: b.y - b.size * 0.3,
    x1: b.x + b.w + b.size * 0.3,
    y1: b.y + b.h + b.size * 0.2,
  }));
  const context = page.doc.context;
  const form = formResolver(PDFLib, context, page.node.Resources(), shared || new Map(), true);
  const gstates = resourceGStates(PDFLib, context, page.node.Resources());
  const result = removeTextInRects(content, rects, pageFonts(PDFLib, page), zones || [], form, gstates);
  const done = new Set();
  result.hits.forEach((count, k) => { if (count > 0) done.add(blocks[k].id); });
  const underlined = new Set();
  result.underlines.forEach((count, k) => { if (count > 0) underlined.add(k); });
  if (result.removed) {
    const ref = context.register(context.flateStream(result.bytes));
    page.node.set(PDFLib.PDFName.of("Contents"), ref);
  }
  return { done, underlined };
}

// Shown strings of one page with position and fill color, for extraction.
// shared: a Map kept across the pages of one document, so forms drawn on
// every page are read once.
function collectPageSegments(PDFLib, page, shared) {
  const content = pageContentBytes(PDFLib, page);
  if (!content) return [];
  const context = page.doc.context;
  const form = formResolver(PDFLib, context, page.node.Resources(), shared || new Map(), false);
  const gstates = resourceGStates(PDFLib, context, page.node.Resources());
  return collectTextSegments(content, pageFonts(PDFLib, page), form, gstates)
    .map(({ x0, y0, x1, color, count, font, visible }) => ({ x0, y0, x1, color, count, font, visible }));
}

// Decoded page content as text, for tests and debugging.
function pageContentText(PDFLib, page) {
  const bytes = pageContentBytes(PDFLib, page);
  return bytes ? latin1(bytes, 0, bytes.length) : "";
}

const api = { pageContentText, tokenize, parseOps, removeTextInRects, collectTextSegments, removePageText, collectPageSegments };

if (typeof module !== "undefined" && module.exports) module.exports = api;
if (typeof window !== "undefined") Object.assign(window, api);
})();
