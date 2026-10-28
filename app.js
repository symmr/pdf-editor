"use strict";

// Browser-only PDF editor: pdf.js renders the pages, pdf-lib writes the result.
// Everything the user adds is kept as an "annotation" in PDF user space, so it
// stays put when the page is rotated or zoomed, and is drawn straight into the
// page content when saving.

const PDFJS_URL = "https://cdn.jsdelivr.net/npm/pdfjs-dist@4.10.38/build/pdf.min.mjs";
const PDFJS_WORKER_URL = "https://cdn.jsdelivr.net/npm/pdfjs-dist@4.10.38/build/pdf.worker.min.mjs";
const PDF_LIB_URL = "https://cdn.jsdelivr.net/npm/pdf-lib@1.17.1/dist/pdf-lib.min.js";
const PDF_LIB_SRI = "sha384-weMABwrltA6jWR8DDe9Jp5blk+tZQh7ugpCsF3JwSA53WZM9/14PjS5LAJNHNjAI";
const FONTKIT_URL = "https://cdn.jsdelivr.net/npm/@pdf-lib/fontkit@1.1.1/dist/fontkit.umd.min.js";
const FONTKIT_SRI = "sha384-2p6U+1mmqF10USehFeRiyG2ESG9FwIqN+jxULn5w9jjQIihSn9Pt13dVCn/Hawjn";
// The same family the page loads from Google Fonts, so text looks the same on
// screen and in the saved file. Only the glyphs used are embedded. The URLs
// come from lib/pdf-text.js (PDF_FONT_URL, PDF_BOLD_FONT_URL).
const CANVAS_FONT = "\"Noto Sans JP\", sans-serif";

// Text boxes are laid out from their top-left corner: line i has its baseline
// at (i * lineHeight + baselineOffset(lineHeight)) * size. With Noto Sans JP
// (ascent 1.16, descent 0.288) this is where a textarea with the same
// line-height puts the baseline.
const LINE_HEIGHT = 1.3;
const baselineOffset = (lineHeight) => lineHeight / 2 + 0.436;
const HIGHLIGHT_OPACITY = 0.35;
const ZOOM_STEPS = [0.5, 0.67, 0.75, 0.9, 1, 1.1, 1.25, 1.5, 1.75, 2, 2.5, 3];
const THUMB_WIDTH = 132;
const HANDLE_SIZE = 9;
const MAX_UNDO = 100;
const TOOL_KEYS = { v: "select", e: "edit", t: "text", w: "whiteout", h: "highlight", r: "box", p: "pen" };
// Highlights keep their own color so switching tools does not turn them red.
const toolColors = { highlight: "#ffd400", other: "#d00000" };
const colorSlot = (name) => (name === "highlight" ? "highlight" : "other");

const pdfDrop = document.getElementById("pdfDrop");
const fileInput = document.getElementById("fileInput");
const fileMeta = document.getElementById("fileMeta");
const step1 = document.getElementById("step1");
const step2 = document.getElementById("step2");
const step3 = document.getElementById("step3");
const editMeta = document.getElementById("editMeta");
const toolButtons = [...document.querySelectorAll("[data-tool]")].filter((el) => el.tagName === "BUTTON");
const imageBtn = document.getElementById("imageBtn");
const imageInput = document.getElementById("imageInput");
const colorInput = document.getElementById("colorInput");
const boldBtn = document.getElementById("boldBtn");
const sizeInput = document.getElementById("sizeInput");
const widthInput = document.getElementById("widthInput");
const undoBtn = document.getElementById("undoBtn");
const redoBtn = document.getElementById("redoBtn");
const deleteBtn = document.getElementById("deleteBtn");
const prevBtn = document.getElementById("prevBtn");
const nextBtn = document.getElementById("nextBtn");
const pageLabel = document.getElementById("pageLabel");
const zoomOutBtn = document.getElementById("zoomOutBtn");
const zoomInBtn = document.getElementById("zoomInBtn");
const zoomLabel = document.getElementById("zoomLabel");
const thumbs = document.getElementById("thumbs");
const stage = document.getElementById("stage");
const pageWrap = document.getElementById("pageWrap");
const pdfCanvas = document.getElementById("pdfCanvas");
const overlay = document.getElementById("overlay");
const appendBtn = document.getElementById("appendBtn");
const appendInput = document.getElementById("appendInput");
const downloadBtn = document.getElementById("downloadBtn");
const downloadHint = document.getElementById("downloadHint");
const busyMsg = document.getElementById("busyMsg");
const errorMsg = document.getElementById("errorMsg");
const okMsg = document.getElementById("okMsg");

const doc = {
  sources: [], // { name, bytes, pdf }: bytes for pdf-lib, pdf for pdf.js
  pages: [], // { id, src, index, baseRotation, rotation, annots }
  images: new Map(), // key -> { dataUrl, mime }
};
let current = 0;
let tool = "select";
let zoom = 1;
let selectedId = null;
let undoStack = [];
let redoStack = [];
let view = null; // { pageId, pdfPage, vp, rotation } for the page on screen
let drag = null;
let editing = null;
let renderSeq = 0;
let renderTask = null;
let dragFrom = null;
let lastDown = null;
let busy = false;
let nextId = 1;
let baseName = "document";
let okTimer = null;
let savedUndoDepth = 0; // undo depth at the last save, for the leave-page warning

const loads = new Map();
const thumbCache = new Map(); // "src:index:rotation" -> Promise<canvas>
const thumbCanvases = [];
const imageElements = new Map();
const measureCtx = document.createElement("canvas").getContext("2d");
const pageBlocks = new Map(); // "src:index" -> Promise<blocks> of the original text
const loadedBlocks = new Map(); // same, once resolved
const libDocs = new Map(); // src -> Promise<pdf-lib PDFDocument>, read only
let hoverBlock = null;

// --- messages ---------------------------------------------------------------

function show(el, text) {
  el.textContent = text || "";
  el.hidden = !text;
}

function showError(text) {
  show(errorMsg, text);
  if (text) show(okMsg, "");
}

function showOk(text) {
  show(okMsg, text);
  if (text) show(errorMsg, "");
  clearTimeout(okTimer);
  okTimer = setTimeout(() => show(okMsg, ""), 5000);
}

function setBusy(on, label) {
  busy = on;
  document.body.classList.toggle("is-busy", on);
  for (const el of document.querySelectorAll("button")) el.disabled = on;
  show(busyMsg, on ? label || "処理中…" : "");
  if (!on) updateControls();
}

// --- library loading ----------------------------------------------------------

function loadScript(src, integrity) {
  return new Promise((resolve, reject) => {
    const script = document.createElement("script");
    script.src = src;
    if (integrity) script.integrity = integrity;
    script.crossOrigin = "anonymous";
    script.onload = resolve;
    script.onerror = () => reject(new Error(`${src} を読み込めませんでした`));
    document.head.appendChild(script);
  });
}

function loadOnce(name, start) {
  if (!loads.has(name)) {
    const promise = start();
    loads.set(name, promise);
    promise.catch(() => loads.delete(name));
  }
  return loads.get(name);
}

function loadPdfjs() {
  return loadOnce("pdfjs", async () => {
    const lib = await import(PDFJS_URL);
    lib.GlobalWorkerOptions.workerSrc = PDFJS_WORKER_URL;
    return lib;
  });
}

function loadPdfLib() {
  return loadOnce("pdf-lib", async () => {
    if (!window.PDFLib) await loadScript(PDF_LIB_URL, PDF_LIB_SRI);
    if (!window.fontkit) await loadScript(FONTKIT_URL, FONTKIT_SRI);
    return { PDFLib: window.PDFLib, fontkit: window.fontkit };
  });
}

function loadFont(url) {
  return loadOnce(url, async () => {
    const res = await fetch(url);
    if (!res.ok) throw new Error(`フォントを読み込めませんでした（${res.status}）`);
    return new Uint8Array(await res.arrayBuffer());
  });
}

// @pdf-lib/fontkit writes a short-format loca table for small subsets but
// does not pad glyphs to an even length, so every glyph after an odd-length
// one points at the wrong bytes and renders blank. Padding fixes the offsets.
// (Same fix as Translation Supporter's pdf-text.js.)
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

// --- document state -------------------------------------------------------------

const currentPage = () => doc.pages[current];
const rotationOf = (page) => (page.baseRotation + page.rotation) % 360;
const pdfPageOf = (page) => doc.sources[page.src].pdf.getPage(page.index + 1);

function selectedAnnot() {
  const page = currentPage();
  return page && selectedId != null ? page.annots.find((a) => a.id === selectedId) || null : null;
}

function snapshot() {
  const page = currentPage();
  return { pages: structuredClone(doc.pages), currentId: page ? page.id : null };
}

function pushUndo(snap) {
  undoStack.push(snap || snapshot());
  if (undoStack.length > MAX_UNDO) undoStack.shift();
  redoStack = [];
  updateControls();
}

function restore(snap) {
  doc.pages = snap.pages;
  const index = doc.pages.findIndex((p) => p.id === snap.currentId);
  current = index >= 0 ? index : Math.min(current, doc.pages.length - 1);
  selectedId = null;
  renderAll();
}

function undo() {
  commitEditor();
  if (!undoStack.length) return;
  redoStack.push(snapshot());
  restore(undoStack.pop());
}

function redo() {
  commitEditor();
  if (!redoStack.length) return;
  undoStack.push(snapshot());
  restore(redoStack.pop());
}

function annotCount() {
  return doc.pages.reduce((n, p) => n + p.annots.length, 0);
}

// --- opening files --------------------------------------------------------------

const isPdf = (file) => file.type === "application/pdf" || /\.pdf$/i.test(file.name);

async function openFiles(fileList, append) {
  if (busy) return;
  const files = [...fileList].filter(isPdf);
  if (!files.length) {
    showError("PDF ファイルを選んでください");
    return;
  }
  commitEditor();
  setBusy(true, "読み込み中…");
  showError("");
  try {
    const pdfjs = await loadPdfjs();
    const loaded = [];
    for (const file of append ? files : files.slice(0, 1)) {
      const bytes = new Uint8Array(await file.arrayBuffer());
      try {
        // pdf.js takes ownership of the buffer it is given, so it gets a copy.
        const pdf = await pdfjs.getDocument({ data: bytes.slice(), isEvalSupported: false }).promise;
        loaded.push({ name: file.name, bytes, pdf });
      } catch (err) {
        throw new Error(err && err.name === "PasswordException"
          ? `${file.name} はパスワード付きのため開けません`
          : `${file.name} を読み込めませんでした`);
      }
    }
    if (append) {
      pushUndo();
    } else {
      for (const s of doc.sources) s.pdf.destroy();
      doc.sources = [];
      doc.pages = [];
      doc.images.clear();
      thumbCache.clear();
      pageBlocks.clear();
      loadedBlocks.clear();
      libDocs.clear();
      undoStack = [];
      redoStack = [];
      selectedId = null;
      baseName = loaded[0].name.replace(/\.pdf$/i, "") || "document";
    }
    const firstNew = doc.pages.length;
    for (const source of loaded) {
      const src = doc.sources.push(source) - 1;
      for (let i = 0; i < source.pdf.numPages; i++) {
        const pdfPage = await source.pdf.getPage(i + 1);
        doc.pages.push({ id: nextId++, src, index: i, baseRotation: pdfPage.rotate, rotation: 0, annots: [] });
      }
    }
    current = firstNew;
    step2.hidden = false;
    step3.hidden = false;
    step1.classList.add("is-done");
    fileMeta.hidden = false;
    fileMeta.textContent = doc.sources.map((s) => s.name).join("、");
    if (!append) await fitZoom();
    renderAll();
    if (append) showOk(`${doc.pages.length - firstNew} ページを追加しました`);
  } catch (err) {
    showError(err.message || String(err));
  } finally {
    setBusy(false);
  }
}

async function fitZoom() {
  const page = currentPage();
  if (!page) return;
  const pdfPage = await pdfPageOf(page);
  const width = pdfPage.getViewport({ scale: 1, rotation: rotationOf(page) }).width;
  const available = stage.clientWidth - 40;
  zoom = Math.round(Math.min(1.5, Math.max(0.5, available / width)) * 100) / 100;
}

// --- rendering --------------------------------------------------------------------

function renderAll() {
  renderThumbs();
  renderPage();
  updateControls();
}

async function renderPage() {
  const seq = ++renderSeq;
  const page = currentPage();
  if (!page) return;
  const pdfPage = await pdfPageOf(page);
  if (renderTask) {
    renderTask.cancel();
    try { await renderTask.promise; } catch (_) {}
  }
  if (seq !== renderSeq) return;
  const rotation = rotationOf(page);
  const vp = pdfPage.getViewport({ scale: zoom, rotation });
  view = { pageId: page.id, pdfPage, vp, rotation };
  const dpr = window.devicePixelRatio || 1;
  pageWrap.style.width = `${Math.floor(vp.width)}px`;
  pageWrap.style.height = `${Math.floor(vp.height)}px`;
  for (const canvas of [pdfCanvas, overlay]) {
    canvas.width = Math.floor(vp.width * dpr);
    canvas.height = Math.floor(vp.height * dpr);
    canvas.style.width = `${Math.floor(vp.width)}px`;
    canvas.style.height = `${Math.floor(vp.height)}px`;
  }
  drawOverlay();
  const task = pdfPage.render({
    canvasContext: pdfCanvas.getContext("2d"),
    viewport: vp,
    transform: dpr !== 1 ? [dpr, 0, 0, dpr, 0, 0] : undefined,
  });
  renderTask = task;
  try {
    await task.promise;
  } catch (err) {
    if (!err || err.name !== "RenderingCancelledException") showError("ページを表示できませんでした");
  }
  if (renderTask === task) renderTask = null;
}

function viewReady() {
  const page = currentPage();
  return view && page && view.pageId === page.id && view.rotation === rotationOf(page);
}

function drawOverlay() {
  if (!viewReady()) return;
  const dpr = window.devicePixelRatio || 1;
  const ctx = overlay.getContext("2d");
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.clearRect(0, 0, overlay.width, overlay.height);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  drawAnnots(ctx, currentPage().annots, view.vp, view.rotation, editing && editing.annotId);
  if (tool === "edit") {
    loadBlocks(currentPage());
    drawBlockOutlines(ctx);
  }
  const sel = selectedAnnot();
  if (sel && !(editing && editing.annotId === sel.id)) drawSelection(ctx, sel);
}

// Edited text first hides the original: a cover in the background color
// sampled around it. Saving removes the original from the page content
// instead (see buildPdf), so the cover is only a preview.
function drawAnnots(ctx, annots, vp, rotation, skipId) {
  for (const a of annots) {
    if (a.type !== "text" || !a.replaces) continue;
    const r = viewRect(coverRect(a.replaces), vp);
    ctx.fillStyle = a.replaces.fill;
    ctx.fillRect(r.x, r.y, r.w, r.h);
  }
  for (const a of annots) {
    if (a.id !== skipId) drawAnnot(ctx, a, vp, rotation);
  }
}

// The original block's area in user space, with a little room for glyphs
// that reach past the measured box.
function coverRect(r) {
  const pad = r.size * 0.12;
  return { x1: r.x - pad, y1: r.y - pad, x2: r.x + r.w + pad, y2: r.y + r.h + pad };
}

function drawBlockOutlines(ctx) {
  const blocks = loadedBlocks.get(blockKey(currentPage()));
  if (!blocks) return;
  const accent = getComputedStyle(document.documentElement).getPropertyValue("--accent").trim() || "#2601fd";
  ctx.save();
  ctx.strokeStyle = accent;
  ctx.fillStyle = accent;
  ctx.lineWidth = 1;
  ctx.setLineDash([3, 3]);
  for (const block of blocks) {
    const r = viewRect(coverRect(block), view.vp);
    ctx.globalAlpha = block === hoverBlock ? 0.9 : 0.45;
    ctx.strokeRect(r.x, r.y, r.w, r.h);
    if (block === hoverBlock) {
      ctx.globalAlpha = 0.08;
      ctx.fillRect(r.x, r.y, r.w, r.h);
    }
  }
  ctx.restore();
}

// Angle (clockwise, degrees) at which an upright-created text box or image
// appears in a view with the given rotation.
const relativeAngle = (a, rotation) => (rotation - a.rotation + 360) % 360;

function drawAnnot(ctx, a, vp, rotation) {
  const s = vp.scale;
  ctx.save();
  if (a.type === "rect") {
    const r = viewRect(a, vp);
    if (a.kind === "whiteout") {
      ctx.fillStyle = "#fff";
      ctx.fillRect(r.x, r.y, r.w, r.h);
    } else if (a.kind === "highlight") {
      ctx.globalAlpha = HIGHLIGHT_OPACITY;
      ctx.fillStyle = a.color;
      ctx.fillRect(r.x, r.y, r.w, r.h);
    } else {
      ctx.strokeStyle = a.color;
      ctx.lineWidth = a.width * s;
      ctx.strokeRect(r.x, r.y, r.w, r.h);
    }
  } else if (a.type === "ink") {
    const pts = a.points.map(([x, y]) => vp.convertToViewportPoint(x, y));
    ctx.strokeStyle = a.color;
    ctx.fillStyle = a.color;
    ctx.lineWidth = a.width * s;
    ctx.lineCap = "round";
    ctx.lineJoin = "round";
    ctx.beginPath();
    if (pts.length === 1) {
      ctx.arc(pts[0][0], pts[0][1], (a.width * s) / 2, 0, Math.PI * 2);
      ctx.fill();
    } else {
      ctx.moveTo(pts[0][0], pts[0][1]);
      for (const [x, y] of pts.slice(1)) ctx.lineTo(x, y);
      ctx.stroke();
    }
  } else {
    const [x, y] = vp.convertToViewportPoint(a.x, a.y);
    ctx.translate(x, y);
    ctx.rotate((relativeAngle(a, rotation) * Math.PI) / 180);
    if (a.type === "text") {
      const lh = a.lineHeight || LINE_HEIGHT;
      ctx.font = fontSpec(a, a.size * s);
      ctx.fillStyle = a.color;
      ctx.textBaseline = "alphabetic";
      textLines(a).forEach((line, i) => {
        ctx.fillText(line, 0, (i * lh + baselineOffset(lh)) * a.size * s);
      });
    } else if (a.type === "image") {
      const img = imageElement(a.image);
      if (img.complete && img.naturalWidth) ctx.drawImage(img, 0, 0, a.w * s, a.h * s);
    }
  }
  ctx.restore();
}

function drawSelection(ctx, a) {
  const box = viewBox(a, view.vp, view.rotation);
  const accent = getComputedStyle(document.documentElement).getPropertyValue("--accent").trim() || "#2601fd";
  ctx.save();
  ctx.strokeStyle = accent;
  ctx.lineWidth = 1;
  ctx.setLineDash([4, 3]);
  ctx.strokeRect(box.x - 3, box.y - 3, box.w + 6, box.h + 6);
  if (hasHandle(a)) {
    const [hx, hy] = handleCenter(box);
    ctx.setLineDash([]);
    ctx.fillStyle = "#fff";
    ctx.fillRect(hx - HANDLE_SIZE / 2, hy - HANDLE_SIZE / 2, HANDLE_SIZE, HANDLE_SIZE);
    ctx.strokeRect(hx - HANDLE_SIZE / 2, hy - HANDLE_SIZE / 2, HANDLE_SIZE, HANDLE_SIZE);
  }
  ctx.restore();
}

function imageElement(key) {
  let img = imageElements.get(key);
  if (!img) {
    img = new Image();
    img.onload = () => {
      drawOverlay();
      drawThumb(current);
    };
    img.src = doc.images.get(key).dataUrl;
    imageElements.set(key, img);
  }
  return img;
}

// Make sure the web font has the glyphs before the canvas draws them; canvas
// text falls back silently, so redraw once the font slices arrive.
const requestedGlyphs = new Set();

function ensureGlyphs(text) {
  const missing = [...new Set(text)].filter((ch) => !requestedGlyphs.has(ch));
  if (!missing.length) return;
  for (const ch of missing) requestedGlyphs.add(ch);
  const chars = missing.join("");
  Promise.all([
    document.fonts.load(`16px ${CANVAS_FONT}`, chars),
    document.fonts.load(`700 16px ${CANVAS_FONT}`, chars),
  ]).then(() => {
    textLayouts.clear();
    drawOverlay();
    thumbCanvases.forEach((_, i) => drawThumb(i));
  }, () => {});
}

// --- geometry ------------------------------------------------------------------------

function viewRect(a, vp) {
  const [x1, y1] = vp.convertToViewportPoint(a.x1, a.y1);
  const [x2, y2] = vp.convertToViewportPoint(a.x2, a.y2);
  return { x: Math.min(x1, x2), y: Math.min(y1, y2), w: Math.abs(x2 - x1), h: Math.abs(y2 - y1) };
}

const fontSpec = (a, px) => `${a.bold ? "700 " : ""}${px}px ${CANVAS_FONT}`;

function measureAt(a) {
  measureCtx.font = fontSpec(a, a.size);
  return (str) => measureCtx.measureText(str).width;
}

// Lines of a text box: its own line breaks, plus wrapping at the box width
// when it has one (wrapText from lib/pdf-text.js keeps Japanese line-break
// rules). The same lines are drawn on screen and written to the PDF.
const textLayouts = new Map();

function textLines(a) {
  if (!a.boxWidth) return a.text.split("\n");
  const key = `${a.bold ? 1 : 0}|${a.size}|${a.boxWidth}|${a.text}`;
  if (!textLayouts.has(key)) {
    if (textLayouts.size > 500) textLayouts.clear();
    textLayouts.set(key, wrapText(a.text, a.boxWidth, measureAt(a)));
  }
  return textLayouts.get(key);
}

// Size in PDF points of a text box or image, before rotation.
function localSize(a) {
  if (a.type === "image") return { w: a.w, h: a.h };
  const lines = textLines(a);
  const measure = measureAt(a);
  const w = a.boxWidth || Math.max(...lines.map(measure), a.size * 0.5);
  return { w, h: Math.max(1, lines.length) * (a.lineHeight || LINE_HEIGHT) * a.size };
}

// Axis-aligned bounding box in view (CSS pixel) coordinates.
function viewBox(a, vp, rotation) {
  const s = vp.scale;
  if (a.type === "rect") return viewRect(a, vp);
  if (a.type === "ink") {
    const pts = a.points.map(([x, y]) => vp.convertToViewportPoint(x, y));
    const pad = (a.width * s) / 2;
    const xs = pts.map((p) => p[0]);
    const ys = pts.map((p) => p[1]);
    const x = Math.min(...xs) - pad;
    const y = Math.min(...ys) - pad;
    return { x, y, w: Math.max(...xs) + pad - x, h: Math.max(...ys) + pad - y };
  }
  const { w, h } = localSize(a);
  const [ax, ay] = vp.convertToViewportPoint(a.x, a.y);
  const angle = (relativeAngle(a, rotation) * Math.PI) / 180;
  const cos = Math.round(Math.cos(angle));
  const sin = Math.round(Math.sin(angle));
  const corners = [[0, 0], [w * s, 0], [0, h * s], [w * s, h * s]]
    .map(([cx, cy]) => [ax + cx * cos - cy * sin, ay + cx * sin + cy * cos]);
  const xs = corners.map((p) => p[0]);
  const ys = corners.map((p) => p[1]);
  const x = Math.min(...xs);
  const y = Math.min(...ys);
  return { x, y, w: Math.max(...xs) - x, h: Math.max(...ys) - y };
}

const hasHandle = (a) => a.type !== "ink";
const handleCenter = (box) => [box.x + box.w + 3, box.y + box.h + 3];

function onHandle(a, pt) {
  const [hx, hy] = handleCenter(viewBox(a, view.vp, view.rotation));
  return Math.abs(pt[0] - hx) <= HANDLE_SIZE && Math.abs(pt[1] - hy) <= HANDLE_SIZE;
}

function distToSegment(p, a, b) {
  const dx = b[0] - a[0];
  const dy = b[1] - a[1];
  const len = dx * dx + dy * dy;
  const t = len ? Math.max(0, Math.min(1, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / len)) : 0;
  return Math.hypot(p[0] - (a[0] + t * dx), p[1] - (a[1] + t * dy));
}

function hits(a, pt) {
  if (a.type === "ink") {
    const pts = a.points.map(([x, y]) => view.vp.convertToViewportPoint(x, y));
    const reach = Math.max(5, (a.width * view.vp.scale) / 2 + 2);
    if (pts.length === 1) return Math.hypot(pt[0] - pts[0][0], pt[1] - pts[0][1]) <= reach;
    return pts.some((p, i) => i > 0 && distToSegment(pt, pts[i - 1], p) <= reach);
  }
  const box = viewBox(a, view.vp, view.rotation);
  const pad = 4;
  return pt[0] >= box.x - pad && pt[0] <= box.x + box.w + pad && pt[1] >= box.y - pad && pt[1] <= box.y + box.h + pad;
}

function hitTest(pt, filter) {
  const annots = currentPage().annots;
  for (let i = annots.length - 1; i >= 0; i--) {
    const a = annots[i];
    if ((!filter || filter(a)) && hits(a, pt)) return a;
  }
  return null;
}

function translateAnnot(a, orig, dx, dy) {
  if (a.type === "rect") {
    a.x1 = orig.x1 + dx;
    a.y1 = orig.y1 + dy;
    a.x2 = orig.x2 + dx;
    a.y2 = orig.y2 + dy;
  } else if (a.type === "ink") {
    a.points = orig.points.map(([x, y]) => [x + dx, y + dy]);
  } else {
    a.x = orig.x + dx;
    a.y = orig.y + dy;
  }
}

// --- pointer input ---------------------------------------------------------------------

function pointerPos(event) {
  const r = overlay.getBoundingClientRect();
  return [event.clientX - r.left, event.clientY - r.top];
}

const toPdf = (pt) => view.vp.convertToPdfPoint(pt[0], pt[1]);

overlay.addEventListener("pointerdown", (event) => {
  if (!viewReady() || busy || event.button !== 0) return;
  event.preventDefault();
  if (editing) {
    commitEditor();
    return;
  }
  const pt = pointerPos(event);
  const page = currentPage();
  if (tool === "select") {
    const sel = selectedAnnot();
    if (sel && hasHandle(sel) && onHandle(sel, pt)) {
      drag = { mode: "resize", annot: sel, orig: structuredClone(sel), box: viewBox(sel, view.vp, view.rotation), before: snapshot(), moved: false };
    } else {
      const hit = hitTest(pt);
      // pointerdown's default is prevented, so double clicks are detected here
      // rather than with a dblclick listener.
      const now = performance.now();
      const isDouble = hit && lastDown && lastDown.id === hit.id && now - lastDown.time < 400;
      lastDown = hit ? { id: hit.id, time: now } : null;
      if (isDouble && hit.type === "text") {
        lastDown = null;
        openEditor(hit, pt);
        return;
      }
      selectedId = hit ? hit.id : null;
      if (hit) {
        syncStyleInputs(hit);
        drag = { mode: "move", annot: hit, orig: structuredClone(hit), start: pt, startPdf: toPdf(pt), before: snapshot(), moved: false };
      }
      drawOverlay();
      updateControls();
    }
  } else if (tool === "edit") {
    startBlockEdit(pt);
  } else if (tool === "text") {
    openEditor(hitTest(pt, (a) => a.type === "text"), pt);
  } else if (tool === "pen") {
    pushUndo();
    const a = { id: nextId++, type: "ink", points: [toPdf(pt)], color: colorInput.value, width: Number(widthInput.value) || 2 };
    page.annots.push(a);
    drag = { mode: "ink", annot: a, last: pt };
    drawOverlay();
  } else {
    pushUndo();
    const [x, y] = toPdf(pt);
    const a = { id: nextId++, type: "rect", kind: tool, x1: x, y1: y, x2: x, y2: y, color: colorInput.value, width: Number(widthInput.value) || 2 };
    page.annots.push(a);
    drag = { mode: "draw", annot: a };
  }
  if (drag) overlay.setPointerCapture(event.pointerId);
});

overlay.addEventListener("pointermove", (event) => {
  const pt = pointerPos(event);
  if (!drag) {
    if (tool === "edit" && viewReady()) {
      const blocks = loadedBlocks.get(blockKey(currentPage()));
      const block = blocks ? blockAt(blocks, pt) : null;
      overlay.style.cursor = block ? "text" : "";
      if (block !== hoverBlock) {
        hoverBlock = block;
        drawOverlay();
      }
      return;
    }
    if (tool !== "select" || !viewReady()) return;
    const sel = selectedAnnot();
    overlay.style.cursor = sel && hasHandle(sel) && onHandle(sel, pt) ? "nwse-resize" : hitTest(pt) ? "move" : "";
    return;
  }
  const a = drag.annot;
  if (drag.mode === "move") {
    if (!drag.moved) {
      if (Math.hypot(pt[0] - drag.start[0], pt[1] - drag.start[1]) < 3) return;
      drag.moved = true;
      pushUndo(drag.before);
    }
    const [x, y] = toPdf(pt);
    translateAnnot(a, drag.orig, x - drag.startPdf[0], y - drag.startPdf[1]);
  } else if (drag.mode === "resize") {
    if (!drag.moved) {
      drag.moved = true;
      pushUndo(drag.before);
    }
    const { box, orig } = drag;
    if (a.type === "rect") {
      const [x1, y1] = toPdf([box.x, box.y]);
      const [x2, y2] = toPdf([Math.max(box.x + 2, pt[0]), Math.max(box.y + 2, pt[1])]);
      Object.assign(a, { x1, y1, x2, y2 });
    } else {
      const f = Math.max(0.05, (pt[0] - box.x) / box.w, (pt[1] - box.y) / box.h);
      if (a.type === "image") {
        a.w = orig.w * f;
        a.h = orig.h * f;
      } else {
        // Text keeps its size; the handle sets the box width and the text
        // wraps inside it.
        const sideways = relativeAngle(a, view.rotation) % 180 !== 0;
        const span = sideways ? pt[1] - box.y : pt[0] - box.x;
        a.boxWidth = Math.max(a.size, Math.round((span / view.vp.scale) * 10) / 10);
      }
    }
  } else if (drag.mode === "draw") {
    [a.x2, a.y2] = toPdf(pt);
  } else if (drag.mode === "ink") {
    if (Math.hypot(pt[0] - drag.last[0], pt[1] - drag.last[1]) < 1.5) return;
    a.points.push(toPdf(pt));
    drag.last = pt;
  }
  drawOverlay();
});

function endDrag() {
  if (!drag) return;
  const { annot, mode } = drag;
  drag = null;
  if (mode === "draw") {
    const box = viewRect(annot, view.vp);
    if (box.w < 3 || box.h < 3) {
      const annots = currentPage().annots;
      annots.splice(annots.indexOf(annot), 1);
      undoStack.pop();
    }
  }
  drawOverlay();
  drawThumb(current);
  updateControls();
}

overlay.addEventListener("pointerup", endDrag);
overlay.addEventListener("pointerleave", () => {
  if (!hoverBlock) return;
  hoverBlock = null;
  drawOverlay();
});
overlay.addEventListener("pointercancel", endDrag);

// --- text editing -------------------------------------------------------------------------

// created: the annotation was made for this edit (an original text block
// taken over), so finishing without a change undoes it.
function openEditor(annot, pt, created) {
  const page = currentPage();
  const s = view.vp.scale;
  const [x, y] = annot ? [annot.x, annot.y] : toPdf(pt);
  const size = annot ? annot.size : Number(sizeInput.value) || 14;
  const color = annot ? annot.color : colorInput.value;
  const bold = annot ? Boolean(annot.bold) : boldBtn.getAttribute("aria-pressed") === "true";
  const lineHeight = (annot && annot.lineHeight) || LINE_HEIGHT;
  const boxWidth = annot && annot.boxWidth;
  const [vx, vy] = view.vp.convertToViewportPoint(x, y);
  const el = document.createElement("textarea");
  el.className = "text-editor";
  el.value = annot ? annot.text : "";
  el.spellcheck = false;
  el.setAttribute("aria-label", "テキスト");
  Object.assign(el.style, {
    left: `${vx}px`,
    top: `${vy}px`,
    fontSize: `${size * s}px`,
    fontWeight: bold ? "700" : "400",
    lineHeight: String(lineHeight),
    whiteSpace: boxWidth ? "pre-wrap" : "pre",
    color,
  });
  const autosize = () => {
    el.style.width = "0px";
    el.style.width = boxWidth ? `${boxWidth * s + 2}px` : `${el.scrollWidth + size * s}px`;
    el.style.height = "0px";
    el.style.height = `${el.scrollHeight}px`;
  };
  el.addEventListener("input", autosize);
  el.addEventListener("keydown", (event) => {
    if (event.key === "Escape" || (event.key === "Enter" && (event.ctrlKey || event.metaKey))) {
      event.preventDefault();
      commitEditor();
    }
  });
  el.addEventListener("blur", () => commitEditor());
  pageWrap.appendChild(el);
  editing = { annotId: annot ? annot.id : null, pageId: page.id, x, y, size, color, bold, el, created: Boolean(created) };
  if (annot) {
    selectedId = annot.id;
    syncStyleInputs(annot);
  }
  autosize();
  drawOverlay();
  // pointerdown's default is prevented, so nothing takes the focus back.
  el.focus({ preventScroll: true });
}

function commitEditor() {
  if (!editing) return;
  const e = editing;
  editing = null;
  const text = e.el.value.replace(/\t/g, "    ").replace(/\s+$/, "");
  e.el.remove();
  const page = doc.pages.find((p) => p.id === e.pageId);
  if (page) {
    const existing = e.annotId != null ? page.annots.find((a) => a.id === e.annotId) : null;
    if (existing && e.created) {
      // the undo step was pushed when the block was taken over
      if (text === existing.text) {
        page.annots.splice(page.annots.indexOf(existing), 1);
        undoStack.pop();
        selectedId = null;
      } else {
        existing.text = text;
      }
    } else if (existing) {
      if (text !== existing.text) {
        pushUndo();
        const a = page.annots.find((x) => x.id === e.annotId);
        // An edited original block stays even when emptied: its original
        // text is still removed, which erases it.
        if (text || a.replaces) {
          a.text = text;
        } else {
          page.annots.splice(page.annots.indexOf(a), 1);
          selectedId = null;
        }
      }
    } else if (text) {
      pushUndo();
      const a = { id: nextId++, type: "text", x: e.x, y: e.y, text, size: e.size, color: e.color, bold: e.bold, rotation: rotationOf(page) };
      page.annots.push(a);
      selectedId = a.id;
    }
    ensureGlyphs(text);
    drawThumb(doc.pages.indexOf(page));
  }
  drawOverlay();
  updateControls();
}

// --- style inputs ------------------------------------------------------------------------

function syncStyleInputs(a) {
  if (a.color) colorInput.value = a.color;
  if (a.type === "text") {
    sizeInput.value = a.size;
    boldBtn.setAttribute("aria-pressed", String(Boolean(a.bold)));
  }
  if (a.width) widthInput.value = a.width;
}

function applyStyle(prop, value) {
  const a = selectedAnnot();
  if (!a || !(prop in a) || a[prop] === value) return;
  if (a.type === "rect" && a.kind === "whiteout") return;
  pushUndo();
  a[prop] = value;
  drawOverlay();
  drawThumb(current);
}

boldBtn.addEventListener("click", () => {
  const a = selectedAnnot();
  if (a && a.type === "text") {
    pushUndo();
    a.bold = !a.bold;
    boldBtn.setAttribute("aria-pressed", String(a.bold));
    ensureGlyphs(a.text);
    drawOverlay();
    drawThumb(current);
  } else {
    boldBtn.setAttribute("aria-pressed", String(boldBtn.getAttribute("aria-pressed") !== "true"));
  }
});

colorInput.addEventListener("change", () => {
  if (selectedAnnot()) applyStyle("color", colorInput.value);
  else toolColors[colorSlot(tool)] = colorInput.value;
});
sizeInput.addEventListener("change", () => {
  const size = Number(sizeInput.value);
  if (size >= 1) applyStyle("size", size);
});
widthInput.addEventListener("change", () => {
  const width = Number(widthInput.value);
  if (width > 0) applyStyle("width", width);
});

// --- thumbnails & page operations ---------------------------------------------------------

function renderThumbs() {
  thumbs.textContent = "";
  thumbCanvases.length = 0;
  doc.pages.forEach((page, i) => {
    const item = document.createElement("div");
    item.className = "thumb";
    item.classList.toggle("is-current", i === current);
    item.draggable = true;
    const canvas = document.createElement("canvas");
    const foot = document.createElement("div");
    foot.className = "thumb-foot";
    const num = document.createElement("span");
    num.className = "thumb-num";
    num.textContent = String(i + 1);
    foot.append(num,
      thumbButton("⟲", "左に回転", () => rotatePage(i, -90)),
      thumbButton("⟳", "右に回転", () => rotatePage(i, 90)),
      thumbButton("✕", "このページを削除", () => deletePage(i)));
    item.append(canvas, foot);
    item.addEventListener("click", (event) => {
      if (!event.target.closest("button")) goTo(i);
    });
    item.addEventListener("dragstart", (event) => {
      dragFrom = i;
      event.dataTransfer.effectAllowed = "move";
      event.dataTransfer.setData("text/plain", String(i));
    });
    item.addEventListener("dragover", (event) => {
      if (dragFrom == null) return;
      event.preventDefault();
      const after = dropAfter(item, event);
      item.classList.toggle("is-drop-before", !after);
      item.classList.toggle("is-drop-after", after);
    });
    item.addEventListener("dragleave", () => item.classList.remove("is-drop-before", "is-drop-after"));
    item.addEventListener("drop", (event) => {
      if (dragFrom == null) return;
      event.preventDefault();
      event.stopPropagation();
      item.classList.remove("is-drop-before", "is-drop-after");
      movePage(dragFrom, i + (dropAfter(item, event) ? 1 : 0));
    });
    item.addEventListener("dragend", () => { dragFrom = null; });
    thumbs.appendChild(item);
    thumbCanvases.push(canvas);
    drawThumb(i);
  });
}

function thumbButton(label, title, onClick) {
  const button = document.createElement("button");
  button.type = "button";
  button.textContent = label;
  button.title = title;
  button.setAttribute("aria-label", title);
  button.disabled = busy;
  button.addEventListener("click", onClick);
  return button;
}

function dropAfter(item, event) {
  const r = item.getBoundingClientRect();
  return getComputedStyle(thumbs).flexDirection === "row"
    ? event.clientX > r.left + r.width / 2
    : event.clientY > r.top + r.height / 2;
}

async function drawThumb(i) {
  const page = doc.pages[i];
  const canvas = thumbCanvases[i];
  if (!page || !canvas) return;
  const pdfPage = await pdfPageOf(page);
  const rotation = rotationOf(page);
  const scale = THUMB_WIDTH / pdfPage.getViewport({ scale: 1, rotation }).width;
  const vp = pdfPage.getViewport({ scale, rotation });
  const dpr = window.devicePixelRatio || 1;
  const key = `${page.src}:${page.index}:${rotation}`;
  if (!thumbCache.has(key)) {
    thumbCache.set(key, (async () => {
      const c = document.createElement("canvas");
      c.width = Math.ceil(vp.width * dpr);
      c.height = Math.ceil(vp.height * dpr);
      await pdfPage.render({ canvasContext: c.getContext("2d"), viewport: vp, transform: [dpr, 0, 0, dpr, 0, 0] }).promise;
      return c;
    })());
  }
  let bitmap;
  try {
    bitmap = await thumbCache.get(key);
  } catch (_) {
    thumbCache.delete(key);
    return;
  }
  if (thumbCanvases[i] !== canvas) return;
  canvas.width = bitmap.width;
  canvas.height = bitmap.height;
  const ctx = canvas.getContext("2d");
  ctx.drawImage(bitmap, 0, 0);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  drawAnnots(ctx, page.annots, vp, rotation);
}

function goTo(i) {
  if (i < 0 || i >= doc.pages.length) return;
  commitEditor();
  current = i;
  selectedId = null;
  [...thumbs.children].forEach((el, j) => el.classList.toggle("is-current", j === i));
  if (thumbs.children[i]) thumbs.children[i].scrollIntoView({ block: "nearest", inline: "nearest" });
  stage.scrollTop = 0;
  renderPage();
  updateControls();
}

function rotatePage(i, delta) {
  commitEditor();
  pushUndo();
  const page = doc.pages[i];
  page.rotation = (page.rotation + delta + 360) % 360;
  drawThumb(i);
  if (i === current) renderPage();
}

function deletePage(i) {
  if (doc.pages.length <= 1) {
    showError("最後の 1 ページは削除できません");
    return;
  }
  commitEditor();
  pushUndo();
  doc.pages.splice(i, 1);
  if (current > i || current >= doc.pages.length) current--;
  selectedId = null;
  renderAll();
}

function movePage(from, to) {
  if (to > from) to--;
  if (to === from) return;
  commitEditor();
  pushUndo();
  const currentId = currentPage().id;
  const [page] = doc.pages.splice(from, 1);
  doc.pages.splice(to, 0, page);
  current = doc.pages.findIndex((p) => p.id === currentId);
  renderAll();
}

// --- editing the original text ------------------------------------------------------------

const blockKey = (page) => `${page.src}:${page.index}`;

function libDocOf(src) {
  if (!libDocs.has(src)) {
    const promise = loadPdfLib().then(({ PDFLib }) =>
      PDFLib.PDFDocument.load(doc.sources[src].bytes, { ignoreEncryption: true, updateMetadata: false }));
    libDocs.set(src, promise);
    promise.catch(() => libDocs.delete(src));
  }
  return libDocs.get(src);
}

// Text blocks (lines joined into paragraphs) of a page's original text, in
// user space: { index, x, y, w, h, size, leading, lines, firstBaseline, text,
// runs }. PDFs have no text boxes; extractPdfTexts (lib/pdf-text.js) groups
// the shown strings by position, as Translation Supporter does.
function loadBlocks(page) {
  const key = blockKey(page);
  if (!pageBlocks.has(key)) {
    const promise = (async () => {
      const pdfPage = await pdfPageOf(page);
      // The fill colors come from the page content, read with pdf-lib.
      let segments = [];
      try {
        const { PDFLib } = await loadPdfLib();
        const libDoc = await libDocOf(page.src);
        if (!libDoc.isEncrypted) segments = collectPageSegments(PDFLib, libDoc.getPage(page.index), new Map());
      } catch (_) {
        segments = [];
      }
      const onePage = {
        numPages: 1,
        getPage: async () => ({
          view: pdfPage.view,
          getTextContent: () => pdfPage.getTextContent(),
          getAnnotations: async () => [],
        }),
      };
      const { metadata } = await extractPdfTexts(onePage, null, { segmentsFor: () => segments });
      return metadata.map((m, index) => ({ ...m, index }));
    })();
    pageBlocks.set(key, promise);
    show(busyMsg, "文字を読み取り中…");
    promise.then((blocks) => {
      loadedBlocks.set(key, blocks);
      if (tool === "edit" && currentPage() && blockKey(currentPage()) === key) {
        drawOverlay();
        if (!blocks.length) showError("このページには編集できる文字がありません（スキャンした画像の PDF など）");
      }
    }, () => {
      pageBlocks.delete(key);
      showError("文字を読み取れませんでした");
    }).finally(() => { if (!busy) show(busyMsg, ""); });
  }
  return pageBlocks.get(key);
}

function blockAt(blocks, pt) {
  let best = null;
  let bestArea = Infinity;
  for (const block of blocks) {
    const r = viewRect(coverRect(block), view.vp);
    if (pt[0] < r.x || pt[0] > r.x + r.w || pt[1] < r.y || pt[1] > r.y + r.h) continue;
    if (r.w * r.h < bestArea) {
      best = block;
      bestArea = r.w * r.h;
    }
  }
  return best;
}

// Background and text color around a block, read from the rendered page.
function sampleBackground(block) {
  const dpr = window.devicePixelRatio || 1;
  const r = viewRect(coverRect(block), view.vp);
  const x0 = Math.max(0, Math.floor((r.x - 3) * dpr));
  const y0 = Math.max(0, Math.floor((r.y - 3) * dpr));
  const x1 = Math.min(pdfCanvas.width, Math.ceil((r.x + r.w + 3) * dpr));
  const y1 = Math.min(pdfCanvas.height, Math.ceil((r.y + r.h + 3) * dpr));
  if (x1 - x0 < 6 || y1 - y0 < 6) return null;
  const image = pdfCanvas.getContext("2d").getImageData(x0, y0, x1 - x0, y1 - y0);
  return sampleBlockColors(image, { x0: 2, y0: 2, x1: image.width - 3, y1: image.height - 3 });
}

// The color and weight most of the block's text has.
function mainStyle(runs) {
  const colors = new Map();
  let bold = 0;
  let total = 0;
  for (const run of runs || []) {
    const n = run.text.length;
    total += n;
    if (run.bold) bold += n;
    if (run.color) colors.set(run.color, (colors.get(run.color) || 0) + n);
  }
  const color = [...colors].sort((p, q) => q[1] - p[1])[0];
  return { color: color ? color[0] : null, bold: total > 0 && bold * 2 > total };
}

// Takes over an original text block: a text annotation with the same text,
// position, size and color replaces it, and the editor opens on it.
function startBlockEdit(pt) {
  const page = currentPage();
  const blocks = loadedBlocks.get(blockKey(page));
  const block = blocks && blockAt(blocks, pt);
  if (!block) return;
  const taken = page.annots.find((a) => a.type === "text" && a.replaces && a.replaces.block === block.index);
  if (taken) {
    openEditor(taken);
    return;
  }
  const sampled = sampleBackground(block);
  const style = mainStyle(block.runs);
  const ink = style.color || (sampled && sampled.ink) || "000000";
  const lineHeight = block.lines > 1 && block.leading > 0
    ? Math.round((block.leading / block.size) * 1000) / 1000
    : LINE_HEIGHT;
  pushUndo();
  const a = {
    id: nextId++,
    type: "text",
    text: block.text,
    x: block.x,
    y: block.firstBaseline + baselineOffset(lineHeight) * block.size,
    size: block.size,
    color: `#${ink.toLowerCase()}`,
    bold: style.bold,
    lineHeight,
    // A paragraph keeps its width (with a little slack, as the replacement
    // font may run wider) and rewraps; a single line just grows.
    boxWidth: block.lines > 1 ? Math.round(block.w * 1.04 * 10) / 10 : null,
    rotation: 0, // block positions are in unrotated user space
    replaces: {
      block: block.index,
      x: block.x,
      y: block.y,
      w: block.w,
      h: block.h,
      size: block.size,
      fill: `#${((sampled && sampled.fill) || "FFFFFF").toLowerCase()}`,
    },
  };
  page.annots.push(a);
  ensureGlyphs(a.text);
  openEditor(a, null, true);
}

// --- images -------------------------------------------------------------------------------

function readAsDataUrl(file) {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onload = () => resolve(reader.result);
    reader.onerror = () => reject(new Error(`${file.name} を読み込めませんでした`));
    reader.readAsDataURL(file);
  });
}

function decodeImage(src) {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.onload = () => resolve(img);
    img.onerror = () => reject(new Error("画像を読み込めませんでした"));
    img.src = src;
  });
}

async function insertImage(file) {
  if (!viewReady()) return;
  commitEditor();
  try {
    let dataUrl = await readAsDataUrl(file);
    const img = await decodeImage(dataUrl);
    let mime = file.type === "image/jpeg" ? "image/jpeg" : "image/png";
    // pdf-lib embeds PNG and JPEG only; other formats (and huge images) are
    // redrawn to a PNG of at most 2000px.
    const limit = 2000;
    const shrink = Math.min(1, limit / Math.max(img.naturalWidth, img.naturalHeight));
    if (shrink < 1 || (file.type !== "image/png" && file.type !== "image/jpeg")) {
      const c = document.createElement("canvas");
      c.width = Math.round(img.naturalWidth * shrink);
      c.height = Math.round(img.naturalHeight * shrink);
      c.getContext("2d").drawImage(img, 0, 0, c.width, c.height);
      dataUrl = c.toDataURL(mime);
    }
    const key = `img${nextId++}`;
    doc.images.set(key, { dataUrl, mime });
    const s = view.vp.scale;
    // Start at 1px = 0.75pt, capped to half the page width.
    const maxW = view.vp.width / s / 2;
    const ratio = img.naturalHeight / img.naturalWidth;
    const w = Math.min(img.naturalWidth * 0.75, maxW);
    const h = w * ratio;
    const [x, y] = toPdf([view.vp.width / 2 - (w * s) / 2, view.vp.height / 2 - (h * s) / 2]);
    pushUndo();
    const a = { id: nextId++, type: "image", image: key, x, y, w, h, rotation: view.rotation };
    currentPage().annots.push(a);
    selectedId = a.id;
    setTool("select");
    drawOverlay();
    drawThumb(current);
  } catch (err) {
    showError(err.message || String(err));
  }
}

imageBtn.addEventListener("click", () => imageInput.click());
imageInput.addEventListener("change", () => {
  if (imageInput.files[0]) insertImage(imageInput.files[0]);
  imageInput.value = "";
});

// --- saving ---------------------------------------------------------------------------------

function hexToRgb(rgb, hex) {
  const n = parseInt(hex.slice(1), 16);
  return rgb(((n >> 16) & 255) / 255, ((n >> 8) & 255) / 255, (n & 255) / 255);
}

async function buildPdf(PDFLib, fontkit) {
  const { PDFDocument, rgb, degrees, BlendMode, LineCapStyle } = PDFLib;
  const out = await PDFDocument.create();
  out.registerFontkit(fontkit);

  // One copyPages call per source keeps resources shared between its pages.
  const copied = new Map();
  for (let src = 0; src < doc.sources.length; src++) {
    const pages = doc.pages.filter((p) => p.src === src);
    if (!pages.length) continue;
    const source = await PDFDocument.load(doc.sources[src].bytes, { ignoreEncryption: true });
    const copies = await out.copyPages(source, pages.map((p) => p.index));
    pages.forEach((p, i) => copied.set(p.id, copies[i]));
  }

  const texts = doc.pages.flatMap((p) => p.annots.filter((a) => a.type === "text" && a.text));
  const fonts = {}; // keyed by bold
  if (texts.length) {
    setBusy(true, "日本語フォントを読み込み中…");
    for (const bold of [false, true]) {
      if (!texts.some((a) => Boolean(a.bold) === bold)) continue;
      const fontBytes = await loadFont(bold ? PDF_BOLD_FONT_URL : PDF_FONT_URL);
      patchFontkitSubset(fontkit, fontBytes);
      fonts[bold] = await out.embedFont(fontBytes, { subset: true });
    }
    setBusy(true, "PDF を作成中…");
  }
  const forms = new Map(); // form XObjects already rewritten, for removePageText

  const images = new Map();
  const embedImage = async (key) => {
    if (!images.has(key)) {
      const { dataUrl, mime } = doc.images.get(key);
      images.set(key, mime === "image/jpeg" ? await out.embedJpg(dataUrl) : await out.embedPng(dataUrl));
    }
    return images.get(key);
  };

  for (const page of doc.pages) {
    const pg = copied.get(page.id);
    out.addPage(pg);
    pg.setRotation(degrees(rotationOf(page)));
    const pdfPage = await pdfPageOf(page);
    // Edited blocks: take the original strings out of the page content
    // (lib/pdf-rewrite.js). This has to come before pdf-lib draws anything,
    // as it replaces the page's content streams. Text it cannot find (inside
    // an image, an unreadable font) is covered instead.
    const edits = page.annots.filter((a) => a.type === "text" && a.replaces);
    if (edits.length) {
      const { done } = removePageText(PDFLib, pg, edits.map((a) => ({ id: a.id, ...a.replaces })), [], forms);
      for (const a of edits) {
        if (done.has(a.id)) continue;
        const r = coverRect(a.replaces);
        pg.drawRectangle({ x: r.x1, y: r.y1, width: r.x2 - r.x1, height: r.y2 - r.y1, color: hexToRgb(rgb, a.replaces.fill) });
      }
    }
    for (const a of page.annots) {
      const color = a.color ? hexToRgb(rgb, a.color) : undefined;
      if (a.type === "rect") {
        const x = Math.min(a.x1, a.x2);
        const y = Math.min(a.y1, a.y2);
        const box = { x, y, width: Math.abs(a.x2 - a.x1), height: Math.abs(a.y2 - a.y1) };
        if (a.kind === "whiteout") {
          pg.drawRectangle({ ...box, color: rgb(1, 1, 1) });
        } else if (a.kind === "highlight") {
          pg.drawRectangle({ ...box, color, opacity: HIGHLIGHT_OPACITY, blendMode: BlendMode.Multiply });
        } else {
          pg.drawRectangle({ ...box, borderColor: color, borderWidth: a.width });
        }
      } else if (a.type === "ink") {
        if (a.points.length === 1) {
          pg.drawCircle({ x: a.points[0][0], y: a.points[0][1], size: a.width / 2, color });
        } else {
          // drawSvgPath flips y, so the path is written with y negated.
          const path = a.points.map(([x, y], i) => `${i ? "L" : "M"}${x.toFixed(2)} ${(-y).toFixed(2)}`).join(" ");
          pg.drawSvgPath(path, { x: 0, y: 0, borderColor: color, borderWidth: a.width, borderLineCap: LineCapStyle.Round });
        }
      } else {
        // Lay the box out in the view it was created in, where it is upright.
        const vp = pdfPage.getViewport({ scale: 1, rotation: a.rotation });
        const [vx, vy] = vp.convertToViewportPoint(a.x, a.y);
        if (a.type === "text") {
          const lh = a.lineHeight || LINE_HEIGHT;
          textLines(a).forEach((line, i) => {
            if (!line) return;
            const [x, y] = vp.convertToPdfPoint(vx, vy + (i * lh + baselineOffset(lh)) * a.size);
            pg.drawText(line, { x, y, size: a.size, font: fonts[Boolean(a.bold)], color, rotate: degrees(a.rotation) });
          });
        } else if (a.type === "image") {
          const [x, y] = vp.convertToPdfPoint(vx, vy + a.h);
          pg.drawImage(await embedImage(a.image), { x, y, width: a.w, height: a.h, rotate: degrees(a.rotation) });
        }
      }
    }
  }
  return out.save();
}

// Inside a claude.ai Artifact the page may not start downloads itself; the
// viewer's "downloads" capability asks them to save the file instead.
// Returns false when the viewer declined.
async function saveFile(filename, blob) {
  const downloads = window.claude && window.claude.use ? await window.claude.use("downloads") : null;
  if (downloads) {
    try {
      await downloads.save({ filename, data: blob });
      return true;
    } catch (err) {
      if (err && err.code === "declined") return false;
      throw new Error((err && err.message) || "ファイルを保存できませんでした");
    }
  }
  const url = URL.createObjectURL(blob);
  const link = document.createElement("a");
  link.href = url;
  link.download = filename;
  document.body.appendChild(link);
  link.click();
  link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 60000);
  return true;
}

async function download() {
  if (busy || !doc.pages.length) return;
  commitEditor();
  setBusy(true, "PDF を作成中…");
  try {
    const { PDFLib, fontkit } = await loadPdfLib();
    const bytes = await buildPdf(PDFLib, fontkit);
    const filename = `${baseName}_edited.pdf`;
    if (!(await saveFile(filename, new Blob([bytes], { type: "application/pdf" })))) return;
    savedUndoDepth = undoStack.length;
    showOk(`${filename} を保存しました`);
  } catch (err) {
    showError(`保存できませんでした: ${err.message || err}`);
  } finally {
    setBusy(false);
  }
}


// --- controls -------------------------------------------------------------------------------

function setTool(name) {
  commitEditor();
  tool = name;
  pageWrap.dataset.tool = name;
  if (name !== "select") colorInput.value = toolColors[colorSlot(name)];
  overlay.style.cursor = "";
  for (const button of toolButtons) button.setAttribute("aria-pressed", String(button.dataset.tool === name));
  hoverBlock = null;
  if (name !== "select") selectedId = null;
  drawOverlay();
  updateControls();
}

function setZoom(next) {
  commitEditor();
  zoom = next;
  renderPage();
  updateControls();
}

function updateControls() {
  const count = doc.pages.length;
  pageLabel.textContent = count ? `${current + 1} / ${count}` : "– / –";
  zoomLabel.textContent = `${Math.round(zoom * 100)}%`;
  editMeta.textContent = count ? `${count} ページ · 書き込み ${annotCount()} 件` : "";
  downloadHint.textContent = count ? `${baseName}_edited.pdf` : "";
  if (busy) return;
  undoBtn.disabled = !undoStack.length;
  redoBtn.disabled = !redoStack.length;
  deleteBtn.disabled = !selectedAnnot();
  prevBtn.disabled = current <= 0;
  nextBtn.disabled = current >= count - 1;
  zoomOutBtn.disabled = zoom <= ZOOM_STEPS[0];
  zoomInBtn.disabled = zoom >= ZOOM_STEPS[ZOOM_STEPS.length - 1];
}

function deleteSelected() {
  const a = selectedAnnot();
  if (!a) return;
  pushUndo();
  const annots = currentPage().annots;
  annots.splice(annots.indexOf(a), 1);
  selectedId = null;
  drawOverlay();
  drawThumb(current);
  updateControls();
}

for (const button of toolButtons) button.addEventListener("click", () => setTool(button.dataset.tool));
undoBtn.addEventListener("click", undo);
redoBtn.addEventListener("click", redo);
deleteBtn.addEventListener("click", deleteSelected);
prevBtn.addEventListener("click", () => goTo(current - 1));
nextBtn.addEventListener("click", () => goTo(current + 1));
zoomOutBtn.addEventListener("click", () => setZoom([...ZOOM_STEPS].reverse().find((z) => z < zoom - 0.001) || ZOOM_STEPS[0]));
zoomInBtn.addEventListener("click", () => setZoom(ZOOM_STEPS.find((z) => z > zoom + 0.001) || ZOOM_STEPS[ZOOM_STEPS.length - 1]));
appendBtn.addEventListener("click", () => appendInput.click());
appendInput.addEventListener("change", () => {
  openFiles(appendInput.files, true);
  appendInput.value = "";
});
downloadBtn.addEventListener("click", download);

document.addEventListener("keydown", (event) => {
  if (step2.hidden || busy || event.target.closest("input, textarea, select")) return;
  const key = event.key.toLowerCase();
  const mod = event.ctrlKey || event.metaKey;
  if (mod && key === "z") {
    event.preventDefault();
    if (event.shiftKey) redo();
    else undo();
  } else if (mod && key === "y") {
    event.preventDefault();
    redo();
  } else if (mod || event.altKey) {
    return;
  } else if (key === "delete" || key === "backspace") {
    if (selectedAnnot()) {
      event.preventDefault();
      deleteSelected();
    }
  } else if (TOOL_KEYS[key]) {
    setTool(TOOL_KEYS[key]);
  } else if (key === "pageup" || (key === "arrowleft" && !selectedAnnot())) {
    goTo(current - 1);
  } else if (key === "pagedown" || (key === "arrowright" && !selectedAnnot())) {
    goTo(current + 1);
  } else if (key === "escape") {
    selectedId = null;
    drawOverlay();
    updateControls();
  }
});

// --- file pickers & drag-and-drop ------------------------------------------------------------

pdfDrop.addEventListener("click", () => fileInput.click());
pdfDrop.addEventListener("keydown", (event) => {
  if (event.key === "Enter" || event.key === " ") {
    event.preventDefault();
    fileInput.click();
  }
});
fileInput.addEventListener("change", () => {
  if (fileInput.files.length) openFiles(fileInput.files, false);
  fileInput.value = "";
});

const hasFiles = (event) => event.dataTransfer && [...event.dataTransfer.types].includes("Files");

pdfDrop.addEventListener("dragover", (event) => {
  if (!hasFiles(event)) return;
  event.preventDefault();
  pdfDrop.classList.add("is-drag");
});
pdfDrop.addEventListener("dragleave", () => pdfDrop.classList.remove("is-drag"));
pdfDrop.addEventListener("drop", (event) => {
  event.preventDefault();
  event.stopPropagation();
  pdfDrop.classList.remove("is-drag");
  openFiles(event.dataTransfer.files, false);
});

// A PDF dropped on the editor is appended; anywhere else it is just kept from
// replacing the page.
document.addEventListener("dragover", (event) => {
  if (hasFiles(event)) event.preventDefault();
});
document.addEventListener("drop", (event) => {
  if (!hasFiles(event)) return;
  event.preventDefault();
  if (!step2.hidden && step2.contains(event.target)) openFiles(event.dataTransfer.files, true);
});

window.addEventListener("beforeunload", (event) => {
  if (undoStack.length !== savedUndoDepth) event.preventDefault();
});

updateControls();
