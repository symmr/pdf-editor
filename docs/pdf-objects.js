// Drawn objects of a page that are not text: painted paths (lines, boxes,
// shapes) and images. collectPageObjects lists them with their position, and
// editPageObjects takes chosen ones out of the page content (or moves them), so the saved
// PDF no longer draws them there. Only what the page content stream itself draws is
// handled: objects inside form XObjects, inline images and shadings are left
// alone. Uses parseOps from pdf-rewrite.js.
(function () {
"use strict";

const IDENTITY = [1, 0, 0, 1, 0, 0];
const PATH_OPS = new Set(["m", "l", "c", "v", "y", "h", "re"]);
const PAINT_OPS = new Set(["S", "s", "f", "F", "f*", "B", "B*", "b", "b*"]);

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

const intersect = (a, b) => (a
  ? { x0: Math.max(a.x0, b.x0), y0: Math.max(a.y0, b.y0), x1: Math.min(a.x1, b.x1), y1: Math.min(a.y1, b.y1) }
  : { x0: b.x0, y0: b.y0, x1: b.x1, y1: b.y1 });

const apply = (m, x, y) => [m[0] * x + m[2] * y + m[4], m[1] * x + m[3] * y + m[5]];

// The decoded content of a page (its streams joined), or null when a stream
// cannot be read.
function contentBytes(PDFLib, page) {
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

// Names of the image XObjects the page can draw.
function imageNames(PDFLib, page) {
  const { PDFName, PDFDict } = PDFLib;
  const names = new Set();
  const resources = page.node.Resources() || page.node.getInheritableAttribute(PDFName.of("Resources"));
  const dict = resources && page.doc.context.lookupMaybe(resources, PDFDict);
  const xobjects = dict && dict.lookupMaybe(PDFName.of("XObject"), PDFDict);
  if (!xobjects) return names;
  for (const [key, value] of xobjects.entries()) {
    const stream = page.doc.context.lookup(value);
    const subtype = stream && stream.dict && stream.dict.lookup(PDFName.of("Subtype"));
    if (subtype === PDFName.of("Image")) names.add(key.decodeText());
  }
  return names;
}

// Walks the page content and returns its objects in drawing order:
// { id, kind: "path" | "image", x0, y0, x1, y1, start, end }, where id is the
// position in that order and start..end the bytes that draw it.
function walkObjects(bytes, images) {
  const objects = [];
  let ctm = IDENTITY.slice();
  const saved = [];
  let lineWidth = 1;
  let path = null;
  let clip = false;
  // The clip box in force (null: none) and whether the current fill and
  // stroke colors are patterns (a pattern stays put when the shape moves).
  let clipBox = null;
  let pat = { fill: false, stroke: false };
  const lockedOf = (m, pattern) => Math.abs(m[0] * m[3] - m[1] * m[2]) < 1e-9 || pattern;
  const num = (v) => (typeof v === "number" ? v : 0);

  const addPoint = (x, y) => {
    const [ux, uy] = apply(ctm, x, y);
    const b = path.bbox;
    b.x0 = Math.min(b.x0, ux);
    b.y0 = Math.min(b.y0, uy);
    b.x1 = Math.max(b.x1, ux);
    b.y1 = Math.max(b.y1, uy);
  };

  for (const { op, operands: a, start, end } of window.parseOps(bytes)) {
    if (PATH_OPS.has(op)) {
      if (!path) path = { start, bbox: { x0: Infinity, y0: Infinity, x1: -Infinity, y1: -Infinity } };
      const n = a.map(num);
      if (op === "re" && n.length >= 4) {
        addPoint(n[0], n[1]);
        addPoint(n[0] + n[2], n[1]);
        addPoint(n[0], n[1] + n[3]);
        addPoint(n[0] + n[2], n[1] + n[3]);
      } else {
        for (let k = 0; k + 1 < n.length; k += 2) addPoint(n[k], n[k + 1]);
      }
      continue;
    }
    if (op === "W" || op === "W*") {
      clip = true;
      continue;
    }
    if (op === "n") {
      if (clip && path && Number.isFinite(path.bbox.x0)) clipBox = intersect(clipBox, path.bbox);
      path = null;
      clip = false;
      continue;
    }
    if (PAINT_OPS.has(op)) {
      if (path && clip && Number.isFinite(path.bbox.x0)) clipBox = intersect(clipBox, path.bbox);
      if (path && !clip && Number.isFinite(path.bbox.x0)) {
        const b = { ...path.bbox };
        if (/^[SsBb]/.test(op)) {
          const pad = (lineWidth * Math.hypot(ctm[0], ctm[1])) / 2;
          b.x0 -= pad;
          b.y0 -= pad;
          b.x1 += pad;
          b.y1 += pad;
        }
        const filled = /[fFBb]/.test(op);
        const stroked = /^[SsBb]/.test(op);
        objects.push({
          id: objects.length,
          kind: "path",
          ...b,
          start: path.start,
          end,
          ctm: ctm.slice(),
          clip: clipBox && { ...clipBox },
          locked: lockedOf(ctm, (filled && pat.fill) || (stroked && pat.stroke)),
        });
      }
      path = null;
      clip = false;
      continue;
    }
    switch (op) {
      case "q": saved.push({ ctm: ctm.slice(), lineWidth, clipBox, pat: { ...pat } }); break;
      case "Q":
        if (saved.length) ({ ctm, lineWidth, clipBox, pat } = saved.pop());
        break;
      case "cs": pat.fill = !!(a[0] && a[0].name === "Pattern"); break;
      case "CS": pat.stroke = !!(a[0] && a[0].name === "Pattern"); break;
      case "scn": if (a.length && a[a.length - 1] && typeof a[a.length - 1] === "object" && a[a.length - 1].name) pat.fill = true; break;
      case "SCN": if (a.length && a[a.length - 1] && typeof a[a.length - 1] === "object" && a[a.length - 1].name) pat.stroke = true; break;
      case "g": case "rg": case "k": pat.fill = false; break;
      case "G": case "RG": case "K": pat.stroke = false; break;
      case "cm":
        if (a.length >= 6) ctm = mul(a.slice(0, 6).map(num), ctm);
        break;
      case "w": lineWidth = typeof a[0] === "number" ? a[0] : 1; break;
      case "Do":
        if (a[0] && images.has(a[0].name)) {
          const corners = [apply(ctm, 0, 0), apply(ctm, 1, 0), apply(ctm, 0, 1), apply(ctm, 1, 1)];
          const xs = corners.map((p) => p[0]);
          const ys = corners.map((p) => p[1]);
          objects.push({
            id: objects.length,
            kind: "image",
            x0: Math.min(...xs),
            y0: Math.min(...ys),
            x1: Math.max(...xs),
            y1: Math.max(...ys),
            start,
            end,
            ctm: ctm.slice(),
            clip: clipBox && { ...clipBox },
            locked: lockedOf(ctm, false),
          });
        }
        break;
      default:
        break;
    }
  }
  return objects;
}

// The objects of a page: [{ id, kind, x0, y0, x1, y1, clip, locked }] in user
// space. clip: the box the object is clipped to (null: none). locked: it
// cannot be moved (painted with a pattern, which would stay behind).
function collectPageObjects(PDFLib, page) {
  const bytes = contentBytes(PDFLib, page);
  if (!bytes) return [];
  return walkObjects(bytes, imageNames(PDFLib, page)).map(({ id, kind, x0, y0, x1, y1, clip, locked }) => ({ id, kind, x0, y0, x1, y1, clip, locked }));
}

// Changes objects of the page content. edits: [{ id, gone }] or
// [{ id, dx, dy }]: an object that is gone is no longer drawn, one with dx, dy
// is drawn that far (in page user space) from where it was. Returns the Set
// of ids changed (an object that cannot be moved is left as it is). An
// image's data stays in the file (the page's resources may be shared with
// other pages); it is only no longer drawn.
function editPageObjects(PDFLib, page, edits) {
  const applied = new Set();
  if (!edits.length) return applied;
  const byId = new Map(edits.map((e) => [e.id, e]));
  const bytes = contentBytes(PDFLib, page);
  if (!bytes) return applied;
  const cuts = walkObjects(bytes, imageNames(PDFLib, page)).filter((o) => byId.has(o.id));
  if (!cuts.length) return applied;
  const encoder = new TextEncoder();
  const parts = [];
  let pos = 0;
  let size = 0;
  const push = (part) => {
    parts.push(part);
    size += part.length;
  };
  for (const cut of cuts) {
    if (cut.start < pos) continue;
    const edit = byId.get(cut.id);
    push(bytes.subarray(pos, cut.start));
    if (!edit.gone && cut.locked) {
      push(bytes.subarray(cut.start, cut.end));
      pos = cut.end;
      continue;
    }
    if (!edit.gone) {
      // The shift is in page space; the object is drawn in the space the
      // current matrix leads to, so the shift is taken back through it.
      const [a, b, c, d] = cut.ctm;
      const det = a * d - b * c;
      if (Math.abs(det) < 1e-9) {
        push(bytes.subarray(cut.start, cut.end));
        pos = cut.end;
        continue;
      }
      const lx = (edit.dx * d - edit.dy * c) / det;
      const ly = (edit.dy * a - edit.dx * b) / det;
      push(encoder.encode(`q 1 0 0 1 ${lx.toFixed(4)} ${ly.toFixed(4)} cm\n`));
      push(bytes.subarray(cut.start, cut.end));
      push(encoder.encode("\nQ\n"));
    }
    pos = cut.end;
    applied.add(cut.id);
  }
  push(bytes.subarray(pos));
  const out = new Uint8Array(size);
  let at = 0;
  for (const part of parts) {
    out.set(part, at);
    at += part.length;
  }
  const context = page.doc.context;
  page.node.set(PDFLib.PDFName.of("Contents"), context.register(context.flateStream(out)));
  return applied;
}

const api = { collectPageObjects, editPageObjects };

if (typeof module !== "undefined" && module.exports) module.exports = api;
if (typeof window !== "undefined") Object.assign(window, api);
})();
