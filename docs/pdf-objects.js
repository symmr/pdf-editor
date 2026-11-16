// Drawn objects of a page that are not text: painted paths (lines, boxes,
// shapes) and images. collectPageObjects lists them with their position, and
// removePageObjects takes chosen ones out of the page content, so the saved
// PDF no longer draws them. Only what the page content stream itself draws is
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
      path = null;
      clip = false;
      continue;
    }
    if (PAINT_OPS.has(op)) {
      if (path && !clip && Number.isFinite(path.bbox.x0)) {
        const b = { ...path.bbox };
        if (/^[SsBb]/.test(op)) {
          const pad = (lineWidth * Math.hypot(ctm[0], ctm[1])) / 2;
          b.x0 -= pad;
          b.y0 -= pad;
          b.x1 += pad;
          b.y1 += pad;
        }
        objects.push({ id: objects.length, kind: "path", ...b, start: path.start, end });
      }
      path = null;
      clip = false;
      continue;
    }
    switch (op) {
      case "q": saved.push({ ctm: ctm.slice(), lineWidth }); break;
      case "Q":
        if (saved.length) ({ ctm, lineWidth } = saved.pop());
        break;
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
          });
        }
        break;
      default:
        break;
    }
  }
  return objects;
}

// The objects of a page: [{ id, kind, x0, y0, x1, y1 }] in user space.
function collectPageObjects(PDFLib, page) {
  const bytes = contentBytes(PDFLib, page);
  if (!bytes) return [];
  return walkObjects(bytes, imageNames(PDFLib, page)).map(({ id, kind, x0, y0, x1, y1 }) => ({ id, kind, x0, y0, x1, y1 }));
}

// Takes the objects whose ids are in the Set out of the page content.
// Returns how many were removed. An image's data stays in the file (the
// page's resources may be shared with other pages); it is only no longer drawn.
function removePageObjects(PDFLib, page, ids) {
  if (!ids.size) return 0;
  const bytes = contentBytes(PDFLib, page);
  if (!bytes) return 0;
  const cuts = walkObjects(bytes, imageNames(PDFLib, page)).filter((o) => ids.has(o.id));
  if (!cuts.length) return 0;
  const parts = [];
  let pos = 0;
  let size = 0;
  for (const cut of cuts) {
    if (cut.start < pos) continue;
    parts.push(bytes.subarray(pos, cut.start));
    size += cut.start - pos;
    pos = cut.end;
  }
  parts.push(bytes.subarray(pos));
  size += bytes.length - pos;
  const out = new Uint8Array(size);
  let at = 0;
  for (const part of parts) {
    out.set(part, at);
    at += part.length;
  }
  const context = page.doc.context;
  page.node.set(PDFLib.PDFName.of("Contents"), context.register(context.flateStream(out)));
  return cuts.length;
}

const api = { collectPageObjects, removePageObjects };

if (typeof module !== "undefined" && module.exports) module.exports = api;
if (typeof window !== "undefined") Object.assign(window, api);
})();
