"use strict";

// Browser-only PDF editor: pdf.js renders the pages, pdf-lib writes the result.
// Everything the user adds is kept as an "annotation" in PDF user space, so it
// stays put when the page is rotated or zoomed, and is drawn straight into the
// page content when saving.

const PDFJS_URL = "https://cdn.jsdelivr.net/npm/pdfjs-dist@4.10.38/build/pdf.min.mjs";
const PDFJS_WORKER_URL = "https://cdn.jsdelivr.net/npm/pdfjs-dist@4.10.38/build/pdf.worker.min.mjs";
// The maintained pdf-lib fork: same API, and it can decrypt, which pdf-lib
// 1.17 cannot (it copied encrypted streams as they were, garbling the page).
const PDF_LIB_URL = "https://cdn.jsdelivr.net/npm/@cantoo/pdf-lib@2.11.1/dist/pdf-lib.min.js";
const PDF_LIB_SRI = "sha384-BcRbGROz3cx4LSKcOw2L5YxAxiJPWIEmXRMrYbXu87aSiU5uMQ4qB9v8FEjrBhhq";
// The fontkit fork the pdf-lib fork is written for. With @pdf-lib/fontkit the
// fork's subset call fails ("reading 'pos'") when saving any added text.
const FONTKIT_URL = "https://cdn.jsdelivr.net/npm/@cantoo/fontkit@2.0.12/dist/fontkit.umd.min.js";
const FONTKIT_SRI = "sha384-5amnpiVitOi3dI0QSR7Gg6X10VnzSww9bE/+GZ0ngGWcglIrBP0CzTlvOMbR97Gc";
// Typefaces text is written in. The fonts in a PDF usually hold only the
// glyphs it uses, so edited text cannot keep its own font; it gets the one
// of these that looks like it (guessFont). Each is the family the page loads
// from Google Fonts, so text looks the same on screen and in the saved file,
// and only the glyphs used are embedded. The sans URLs come from
// lib/pdf-text.js (PDF_FONT_URL, PDF_BOLD_FONT_URL). mid is (ascent -
// descent) / 2 of the font, for baselineOffset.
const FONTS = {
  sans: {
    css: "\"Noto Sans JP\", sans-serif",
    regular: PDF_FONT_URL,
    bold: PDF_BOLD_FONT_URL,
    mid: 0.436,
  },
  serif: {
    css: "\"Noto Serif JP\", serif",
    regular: "https://cdn.jsdelivr.net/npm/@expo-google-fonts/noto-serif-jp@0.4.1/400Regular/NotoSerifJP_400Regular.ttf",
    bold: "https://cdn.jsdelivr.net/npm/@expo-google-fonts/noto-serif-jp@0.4.1/700Bold/NotoSerifJP_700Bold.ttf",
    mid: 0.4325,
  },
};
// Fonts installed on this computer, matched to the names of the fonts a PDF
// draws its text in (Local Font Access API: Chromium browsers, after the
// user allows it). Edited text can then keep its own font. Entries are keyed
// "local:<PostScript name>" and look like FONTS entries; fallback is the
// FONTS key used when the font cannot be embedded or lacks a character.
const localFonts = new Map();
let localList = null; // FontData[] once allowed, [] when not
let localReady = null; // promise of localList

const fontOf = (a) => FONTS[a.font] || localFonts.get(a.font) || FONTS.sans;

// Text boxes are laid out from their top-left corner: line i has its baseline
// at (i * lineHeight + baselineOffset(lineHeight, a)) * size. With the font's
// ascent and descent (Noto Sans JP: 1.16 and 0.288) this is where a textarea
// with the same line-height puts the baseline.
const LINE_HEIGHT = 1.3;
const baselineOffset = (lineHeight, a) => lineHeight / 2 + fontOf(a).mid;
const HIGHLIGHT_OPACITY = 0.35;
const ZOOM_STEPS = [0.5, 0.67, 0.75, 0.9, 1, 1.1, 1.25, 1.5, 1.75, 2, 2.5, 3];
const THUMB_WIDTH = 132;
const HANDLE_SIZE = 9;
const MAX_UNDO = 100;
const TOOL_KEYS = { v: "select", e: "edit", t: "text", f: "fill", h: "highlight", r: "box", p: "pen" };
// Highlights keep their own color so switching tools does not turn them red.
const toolColors = { highlight: "#ffd400", fill: "#ffffff", other: "#d00000" };
const colorSlot = (name) => (name === "highlight" || name === "fill" ? name : "other");

const pdfDrop = document.getElementById("pdfDrop");
const fileInput = document.getElementById("fileInput");
const fileMeta = document.getElementById("fileMeta");
const step1 = document.getElementById("step1");
const step2 = document.getElementById("step2");
const step3 = document.getElementById("step3");
const toolButtons = [...document.querySelectorAll("[data-tool]")].filter((el) => el.tagName === "BUTTON");
const imageBtn = document.getElementById("imageBtn");
const imageInput = document.getElementById("imageInput");
const colorInput = document.getElementById("colorInput");
const boldBtn = document.getElementById("boldBtn");
const fontInput = document.getElementById("fontInput");
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
const busyMsg = document.getElementById("busyMsg");
const errorMsg = document.getElementById("errorMsg");
const okMsg = document.getElementById("okMsg");

const doc = {
  sources: [], // { name, bytes, pdf, restricted }: bytes for pdf-lib, pdf for pdf.js
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
// Every change gets a new version number and undo/redo bring the old one
// back, so the leave-page warning knows whether the state on screen is the
// one last saved (the undo depth cannot tell: undo then a new change, or a
// full undo stack, keep the same depth).
let version = 0;
let lastVersion = 0;
let savedVersion = 0;

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
  return { pages: structuredClone(doc.pages), currentId: page ? page.id : null, version };
}

function pushUndo(snap) {
  undoStack.push(snap || snapshot());
  if (undoStack.length > MAX_UNDO) undoStack.shift();
  redoStack = [];
  version = ++lastVersion;
  updateControls();
}

// Takes back the step just pushed, when the change it was for did not happen.
function dropUndo() {
  version = undoStack.pop().version;
}

function restore(snap) {
  doc.pages = snap.pages;
  version = snap.version;
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
        // Opened without a password but encrypted: printing or editing is
        // restricted. Saving decrypts it, which lifts the restrictions.
        const restricted = (await pdf.getPermissions()) !== null;
        loaded.push({ name: file.name, bytes, pdf, restricted });
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
      for (const s of stripped.values()) s.pdf.destroy();
      stripped.clear();
      strippedWanted.clear();
      if (guess) guess.pdf.destroy();
      guess = null;
      guessWanted = "";
      loadedBlocks.clear();
      libDocs.clear();
      undoStack = [];
      redoStack = [];
      savedVersion = version;
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
    fileMeta.textContent = doc.sources.map((s) => `${s.name} · ${(s.bytes.length / 1024).toFixed(1)} KB`).join("、");
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
  const bare = strippedFor(page);
  const dpr = window.devicePixelRatio || 1;
  if (view && view.pageId === page.id) view.target = bare;
  const width = Math.floor(vp.width * dpr);
  const height = Math.floor(vp.height * dpr);
  // Drawing the same page again (its text was stripped): render aside and
  // swap, as resizing the canvas would blank it for a moment.
  if (view && view.pageId === page.id && view.rotation === rotation && view.vp.scale === vp.scale &&
      pdfCanvas.width === width && pdfCanvas.height === height) {
    if (bare && bare.canvas && bare.scale === vp.scale && bare.canvas.width === width && bare.canvas.height === height) {
      pdfCanvas.getContext("2d").drawImage(bare.canvas, 0, 0);
      view.stripped = bare;
      drawOverlay();
      return;
    }
    const aside = document.createElement("canvas");
    aside.width = width;
    aside.height = height;
    const task = (bare ? bare.pdfPage : pdfPage).render({
      canvasContext: aside.getContext("2d"),
      viewport: vp,
      transform: dpr !== 1 ? [dpr, 0, 0, dpr, 0, 0] : undefined,
    });
    renderTask = task;
    try {
      await task.promise;
      if (seq === renderSeq) {
        pdfCanvas.getContext("2d").drawImage(aside, 0, 0);
        view.stripped = bare;
        drawOverlay();
      }
    } catch (err) {
      if (!err || err.name !== "RenderingCancelledException") showError("ページを表示できませんでした");
    }
    if (renderTask === task) renderTask = null;
    return;
  }
  view = { pageId: page.id, pdfPage, vp, rotation, stripped: null, target: bare };
  pageWrap.style.width = `${Math.floor(vp.width)}px`;
  pageWrap.style.height = `${Math.floor(vp.height)}px`;
  for (const canvas of [pdfCanvas, overlay]) {
    canvas.width = Math.floor(vp.width * dpr);
    canvas.height = Math.floor(vp.height * dpr);
    canvas.style.width = `${Math.floor(vp.width)}px`;
    canvas.style.height = `${Math.floor(vp.height)}px`;
  }
  drawOverlay();
  const task = (bare ? bare.pdfPage : pdfPage).render({
    canvasContext: pdfCanvas.getContext("2d"),
    viewport: vp,
    transform: dpr !== 1 ? [dpr, 0, 0, dpr, 0, 0] : undefined,
  });
  renderTask = task;
  try {
    await task.promise;
    if (bare && seq === renderSeq) {
      view.stripped = bare;
      drawOverlay();
    }
  } catch (err) {
    if (!err || err.name !== "RenderingCancelledException") showError("ページを表示できませんでした");
  }
  if (renderTask === task) renderTask = null;
}

// --- the page without the text being edited -------------------------------------------------
// Saving takes an edited block's original text out of the page content, so
// nothing needs painting over it. To show the same on screen, a one-page copy
// of the page is rewritten the same way and rendered instead of the original.

const stripped = new Map(); // page id -> { sig, entries: Map(block -> json), done: Set(block), pdf, pdfPage }
const strippedWanted = new Map(); // page id -> sig being built (or built last)
let guess = null; // built ahead for the block under the pointer: { pageId, sig, ... }
let guessWanted = "";

const editsOf = (page) => page.annots.filter((a) => a.type === "text" && a.replaces);
const replacesJson = (r) => JSON.stringify({ ...r, fill: undefined });
const sigOf = (list) => JSON.stringify([...list].sort((p, q) => p.block - q.block).map((r) => [r.block, replacesJson(r)]));
const originalOf = (block) => ({ block: block.index, x: block.x, y: block.y, w: block.w, h: block.h, size: block.size });

// The stripped page, while it still matches the page's edits (it may have
// been made for fewer of them).
function strippedFor(page) {
  const s = stripped.get(page.id);
  if (!s || !s.entries.size) return null;
  const edits = editsOf(page);
  const ok = [...s.entries].every(([block, json]) => edits.some((a) => a.replaces.block === block && replacesJson(a.replaces) === json));
  return ok ? s : null;
}

function useStripped(page, made) {
  const old = stripped.get(page.id);
  stripped.set(page.id, made);
  if (old) old.pdf.destroy();
  if (currentPage() && currentPage().id === page.id) renderPage();
}

function ensureStripped(page) {
  // The page on screen was drawn for other edits (one was undone, or taken
  // back by leaving its text as it was): draw it again.
  if (viewReady() && view.target !== strippedFor(page)) renderPage();
  const edits = editsOf(page);
  if (!edits.length) return;
  const sig = sigOf(edits.map((a) => a.replaces));
  const s = stripped.get(page.id);
  if ((s && s.sig === sig) || strippedWanted.get(page.id) === sig) return;
  if (guess && guess.pageId === page.id && guess.sig === sig) {
    // built ahead while the pointer was over the block
    strippedWanted.set(page.id, sig);
    const made = guess;
    guess = null;
    useStripped(page, made);
    return;
  }
  strippedWanted.set(page.id, sig);
  buildStripped(page, edits.map((a) => a.replaces)).then((made) => {
    if (strippedWanted.get(page.id) !== sig) {
      made.pdf.destroy();
      return;
    }
    useStripped(page, made);
  }, () => {}); // the cover stays
}

// The size the page on screen is drawn at, for rendering ahead.
function aheadView() {
  if (!viewReady()) return null;
  const dpr = window.devicePixelRatio || 1;
  return { vp: view.vp, dpr, width: Math.floor(view.vp.width * dpr), height: Math.floor(view.vp.height * dpr) };
}
// Builds the stripped page for the edits plus the block under the pointer,
// so that opening it for editing finds the page ready.
let guessTimer = 0;
function guessStripped(block) {
  clearTimeout(guessTimer);
  if (!block) return;
  guessTimer = setTimeout(() => {
    const page = currentPage();
    if (!page || tool !== "edit") return;
    const list = editsOf(page).map((a) => a.replaces);
    if (list.some((r) => r.block === block.index)) return;
    list.push(originalOf(block));
    const sig = sigOf(list);
    if (guessWanted === `${page.id}:${sig}`) return;
    guessWanted = `${page.id}:${sig}`;
    buildStripped(page, list, aheadView()).then((made) => {
      if (guessWanted !== `${page.id}:${sig}`) {
        made.pdf.destroy();
        return;
      }
      if (strippedWanted.get(page.id) === sig) { // opened meanwhile: that build serves
        made.pdf.destroy();
        return;
      }
      if (guess) guess.pdf.destroy();
      guess = { pageId: page.id, ...made };
    }, () => {});
  }, 120);
}

async function buildStripped(page, list, ahead) {
  const [{ PDFLib }, pdfjs, libDoc] = await Promise.all([loadPdfLib(), loadPdfjs(), libDocOf(page.src)]);
  const tmp = await PDFLib.PDFDocument.create();
  const [copy] = await tmp.copyPages(libDoc, [page.index]);
  tmp.addPage(copy);
  const { done } = removePageText(PDFLib, copy, list.map((r) => ({ id: r.block, ...r })), [], new Map());
  const bytes = await tmp.save();
  const pdf = await pdfjs.getDocument({ data: bytes, isEvalSupported: false }).promise;
  const pdfPage = await pdf.getPage(1);
  const original = await pdfPageOf(page);
  const same = pdfPage.view.every((v, i) => Math.abs(v - original.view[i]) < 0.01);
  // Rendering is the slow part: for a page built ahead it is done here too,
  // at the size on screen.
  let canvas = null;
  if (ahead && same) {
    canvas = document.createElement("canvas");
    canvas.width = ahead.width;
    canvas.height = ahead.height;
    await pdfPage.render({
      canvasContext: canvas.getContext("2d"),
      viewport: ahead.vp,
      transform: ahead.dpr !== 1 ? [ahead.dpr, 0, 0, ahead.dpr, 0, 0] : undefined,
    }).promise;
  }
  // Different page boxes would shift everything: keep the cover.
  return {
    sig: sigOf(list),
    entries: same ? new Map(list.map((r) => [r.block, replacesJson(r)])) : new Map(),
    done,
    pdf,
    pdfPage,
    canvas,
    scale: ahead ? ahead.vp.scale : 0,
  };
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
  const page = currentPage();
  ensureStripped(page);
  // Blocks whose text the page on screen no longer has need no cover.
  let bare = view.stripped && strippedFor(page) === view.stripped ? view.stripped.done : null;
  // A block just opened for editing still reads as the original text, which
  // is on the page already: a cover would only flash until the stripped page
  // arrives.
  const open = editing && page.annots.find((a) => a.id === editing.annotId);
  if (open && open.replaces) {
    const blocks = loadedBlocks.get(blockKey(page));
    const block = blocks && blocks.find((b) => b.index === open.replaces.block);
    if (block && block.text === open.text) bare = new Set([...(bare || []), open.replaces.block]);
  }
  drawAnnots(ctx, page.annots, view.vp, view.rotation, editing && editing.annotId, bare);
  if (tool === "edit") {
    loadBlocks(currentPage());
    drawBlockOutlines(ctx);
  }
  const sel = selectedAnnot();
  if (sel && !(editing && editing.annotId === sel.id)) drawSelection(ctx, sel);
}

// Edited text first hides the original: a cover in the background color
// sampled around it. Saving removes the original from the page content
// instead (see buildPdf), so the cover is only a preview, and only for text
// the page on screen still has (bare: ids of blocks it no longer has).
function drawAnnots(ctx, annots, vp, rotation, skipId, bare) {
  for (const a of annots) {
    if (a.type !== "text" || !a.replaces || (bare && bare.has(a.replaces.block))) continue;
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
    if (a.kind === "fill") {
      ctx.fillStyle = a.color;
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
      const layout = textLayout(a);
      layout.lines.forEach((line, i) => {
        ctx.fillText(line, layout.offsets[i] * s, (i * lh + baselineOffset(lh, a)) * a.size * s);
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

function ensureGlyphs(text, a) {
  const { css } = fontOf(a);
  const missing = [...new Set(text)].filter((ch) => !requestedGlyphs.has(`${css}|${ch}`));
  if (!missing.length) return;
  for (const ch of missing) requestedGlyphs.add(`${css}|${ch}`);
  const chars = missing.join("");
  Promise.all([
    document.fonts.load(`16px ${css}`, chars),
    document.fonts.load(`700 16px ${css}`, chars),
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

const fontSpec = (a, px) => `${a.bold ? "700 " : ""}${px}px ${fontOf(a).css}`;

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
  const key = `${a.font}|${a.bold ? 1 : 0}|${a.size}|${a.boxWidth}|${a.text}`;
  if (!textLayouts.has(key)) {
    if (textLayouts.size > 500) textLayouts.clear();
    textLayouts.set(key, wrapText(a.text, a.boxWidth, measureAt(a)));
  }
  return textLayouts.get(key);
}

// Where each line of a text box starts, relative to a.x. Lines are aligned
// within the box width, else within refWidth (the width the text had before
// it was edited, so a centered label stays centered whatever it now says),
// else within the widest line. dx and w are the extent of what is drawn.
const ALIGN_FACTOR = { left: 0, center: 0.5, right: 1 };

function textLayout(a) {
  const lines = textLines(a);
  const measure = measureAt(a);
  const widths = lines.map(measure);
  const f = ALIGN_FACTOR[a.align] || 0;
  const widest = Math.max(...widths, a.size * 0.5);
  const within = a.boxWidth || a.refWidth || widest;
  const offsets = widths.map((w) => (within - w) * f);
  const h = Math.max(1, lines.length) * (a.lineHeight || LINE_HEIGHT) * a.size;
  if (a.boxWidth) return { lines, offsets, dx: 0, w: a.boxWidth, h };
  const dx = Math.min(...offsets);
  const right = Math.max(...offsets.map((o, i) => o + widths[i]));
  return { lines, offsets, dx, w: Math.max(right - dx, a.size * 0.5), h };
}

// Size in PDF points of a text box or image, before rotation; dx is how far
// the drawn text starts to the right of a.x.
function localSize(a) {
  if (a.type === "image") return { w: a.w, h: a.h, dx: 0 };
  const { dx, w, h } = textLayout(a);
  return { w, h, dx };
}

// Moves a text box so it starts where its text is drawn, and lets go of
// refWidth. Done before resizing by hand, which sets the box width.
function bakeAlignment(a) {
  if (a.type !== "text" || a.boxWidth || a.refWidth === undefined) return;
  const { dx } = textLayout(a);
  delete a.refWidth;
  if (!dx) return;
  const s = view.vp.scale;
  const [vx, vy] = view.vp.convertToViewportPoint(a.x, a.y);
  const angle = (relativeAngle(a, view.rotation) * Math.PI) / 180;
  [a.x, a.y] = view.vp.convertToPdfPoint(vx + dx * s * Math.cos(angle), vy + dx * s * Math.sin(angle));
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
  const { w, h, dx } = localSize(a);
  const [ax, ay] = vp.convertToViewportPoint(a.x, a.y);
  const angle = (relativeAngle(a, rotation) * Math.PI) / 180;
  const cos = Math.round(Math.cos(angle));
  const sin = Math.round(Math.sin(angle));
  const corners = [[dx * s, 0], [(dx + w) * s, 0], [dx * s, h * s], [(dx + w) * s, h * s]]
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
      bakeAlignment(sel);
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
        guessStripped(block);
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
      dropUndo();
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
// What the text box is written on: the page's own background for an edited
// block, else white or a dark tone, whichever the text color reads against.
function editorBackground(color, annot) {
  if (annot && annot.replaces && /^#[0-9a-f]{6}$/i.test(annot.replaces.fill)) return annot.replaces.fill;
  const c = /^#[0-9a-f]{6}$/i.test(color) ? rgbOf(color.slice(1)) : [0, 0, 0];
  const lum = 0.2126 * c[0] + 0.7152 * c[1] + 0.0722 * c[2];
  return lum > 150 ? "rgba(20, 20, 30, 0.85)" : "rgba(255, 255, 255, 0.85)";
}
function openEditor(annot, pt, created) {
  const page = currentPage();
  const s = view.vp.scale;
  const [x, y] = annot ? [annot.x, annot.y] : toPdf(pt);
  const size = annot ? annot.size : Number(sizeInput.value) || 14;
  const color = annot ? annot.color : colorInput.value;
  const bold = annot ? Boolean(annot.bold) : boldBtn.getAttribute("aria-pressed") === "true";
  const font = annot ? annot.font : fontInput.value;
  const lineHeight = (annot && annot.lineHeight) || LINE_HEIGHT;
  const boxWidth = annot && annot.boxWidth;
  const align = annot ? annot.align || "left" : defaultAlign;
  const refWidth = annot && !boxWidth ? annot.refWidth : undefined;
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
    fontFamily: fontOf({ font }).css,
    fontWeight: bold ? "700" : "400",
    lineHeight: String(lineHeight),
    whiteSpace: boxWidth ? "pre-wrap" : "pre",
    textAlign: align,
    color,
    background: editorBackground(color, annot),
  });
  const autosize = () => {
    el.style.width = "0px";
    const width = boxWidth ? boxWidth * s + 2 : el.scrollWidth + size * s;
    el.style.width = `${width}px`;
    // text aligned within a reference width grows around its anchor
    if (refWidth !== undefined) el.style.left = `${vx + (refWidth * s - width) * (ALIGN_FACTOR[align] || 0)}px`;
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
  editing = { annotId: annot ? annot.id : null, pageId: page.id, x, y, size, color, bold, font, align, el, created: Boolean(created) };
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
        dropUndo();
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
      const a = { id: nextId++, type: "text", x: e.x, y: e.y, text, size: e.size, color: e.color, bold: e.bold, font: e.font, align: e.align === "left" ? undefined : e.align, rotation: rotationOf(page) };
      page.annots.push(a);
      selectedId = a.id;
    }
    ensureGlyphs(text, e);
    drawThumb(doc.pages.indexOf(page));
  }
  drawOverlay();
  updateControls();
}

// --- style inputs ------------------------------------------------------------------------

const alignButtons = [...document.querySelectorAll("[data-align]")];
let defaultAlign = "left";

function showAlign(value) {
  for (const button of alignButtons) button.setAttribute("aria-pressed", String(button.dataset.align === value));
}

for (const button of alignButtons) {
  button.addEventListener("click", () => {
    const value = button.dataset.align;
    const a = selectedAnnot();
    if (a && a.type === "text") {
      if ((a.align || "left") !== value) {
        pushUndo();
        a.align = value === "left" ? undefined : value;
        drawOverlay();
        drawThumb(current);
      }
    } else {
      defaultAlign = value;
    }
    showAlign(value);
  });
}

function syncStyleInputs(a) {
  if (a.color) colorInput.value = a.color;
  if (a.type === "text") {
    showAlign(a.align || "left");
    sizeInput.value = a.size;
    boldBtn.setAttribute("aria-pressed", String(Boolean(a.bold)));
    fontInput.value = a.font || "sans";
  }
  if (a.width) widthInput.value = a.width;
}

function applyStyle(prop, value) {
  const a = selectedAnnot();
  if (!a || !(prop in a) || a[prop] === value) return;
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
    ensureGlyphs(a.text, a);
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
fontInput.addEventListener("change", () => {
  const a = selectedAnnot();
  if (a && a.type === "text") ensureGlyphs(a.text, { font: fontInput.value });
  applyStyle("font", fontInput.value);
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

// pdf-lib document of a source, decrypted. The empty password opens what
// pdf.js opened without one: files that only restrict printing or editing.
async function loadLibDoc(PDFLib, src) {
  const { name, bytes } = doc.sources[src];
  const libDoc = await PDFLib.PDFDocument.load(bytes, { password: "", updateMetadata: false });
  // An encryption pdf-lib cannot undo leaves it encrypted; copying its
  // streams as they are would garble the pages.
  if (libDoc.isEncrypted) throw new Error(`${name} の暗号化を解除できませんでした`);
  return libDoc;
}

function libDocOf(src) {
  if (!libDocs.has(src)) {
    const promise = loadPdfLib().then(({ PDFLib }) => loadLibDoc(PDFLib, src));
    libDocs.set(src, promise);
    promise.catch(() => libDocs.delete(src));
  }
  return libDocs.get(src);
}

// Text blocks (lines joined into paragraphs) of a page's original text, in
// user space: { index, x, y, w, h, size, leading, lines, firstBaseline, text,
// runs }. PDFs have no text boxes; extractPdfTexts (lib/pdf-text.js) groups
// the shown strings by position.
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
        segments = collectPageSegments(PDFLib, libDoc.getPage(page.index), new Map());
      } catch (_) {
        segments = [];
      }
      let content = null;
      const onePage = {
        numPages: 1,
        getPage: async () => ({
          view: pdfPage.view,
          getTextContent: async () => (content = await pdfPage.getTextContent()),
          getAnnotations: async () => [],
        }),
      };
      const { metadata } = await extractPdfTexts(onePage, null, { segmentsFor: () => segments });
      await localReady; // the installed fonts, if the user allowed them
      const pageFont = fontByName(segments, null);
      return metadata.map((m, index) => ({
        ...m,
        index,
        font: guessFont(m, segments, content, pageFont),
        lineAlign: m.lines > 1 ? alignOfLines(m, content.items) : null,
      }));
    })();
    pageBlocks.set(key, promise);
    show(busyMsg, "文字を読み取り中…");
    promise.then((blocks) => {
      loadedBlocks.set(key, blocks);
      if (tool === "edit" && currentPage() && blockKey(currentPage()) === key) {
        drawOverlay();
        if (!blocks.length) showError("編集できる文字がありません");
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
  const sampled = sampleBlockColors(image, { x0: 2, y0: 2, x1: image.width - 3, y1: image.height - 3 });
  if (!sampled) return null;
  return { ...sampled, ink: strongestInk(image, sampled.fill) || sampled.ink };
}

const rgbOf = (hex) => [0, 2, 4].map((i) => parseInt(hex.slice(i, i + 2), 16));
const colorGap = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1], a[2] - b[2]);

// The text color seen on the page: the mean of the pixels farthest from the
// background. Thin strokes are blended with it at their edges, so the
// commonest ink pixel is usually paler than the real color.
function strongestInk(image, fillHex) {
  const fill = rgbOf(fillHex);
  const { data } = image;
  const gaps = [];
  for (let i = 0; i < data.length; i += 4) {
    const gap = colorGap([data[i], data[i + 1], data[i + 2]], fill);
    if (gap > 60) gaps.push([gap, i]);
  }
  if (gaps.length < 4) return null;
  gaps.sort((p, q) => q[0] - p[0]);
  const top = gaps.slice(0, Math.max(4, Math.round(gaps.length * 0.12)));
  const sum = [0, 0, 0];
  for (const [, i] of top) for (let k = 0; k < 3; k++) sum[k] += data[i + k];
  return sum.map((v) => Math.round(v / top.length).toString(16).padStart(2, "0")).join("").toUpperCase();
}

// The color a block's text is written in. The page content says so when it
// can; that is not believed when the color would be invisible on the
// background the page shows (black set before a dark fill, say), and it is
// missing for patterns and unusual color spaces. Then the rendered page tells.
function inkOf(contentColor, sampled) {
  const fill = (sampled && sampled.fill) || "FFFFFF";
  if (contentColor && colorGap(rgbOf(contentColor), rgbOf(fill)) >= 90) return contentColor;
  if (sampled && sampled.ink) return sampled.ink;
  return contentColor || (colorGap(rgbOf(fill), [0, 0, 0]) < 200 ? "FFFFFF" : "1E1E1E");
}

// Typeface (a key of FONTS) for a block's replacement text. The names of the
// fonts drawn in the block decide (Mincho, Times: serif; Gothic, Arial: sans);
// when they say nothing, the fonts of the rest of the page (pageFont), and
// then pdf.js's own guess from the font's flags.
function guessFont(block, segments, content, pageFont) {
  return installedFontByName(segments, block) || fontByName(segments, block) || pageFont ||
    fontByPdfjs(content, block) || "sans";
}

// --- installed fonts ---------------------------------------------------------------------

// Asks (once) to read the list of installed fonts. Needs a user gesture, so
// it runs when the edit tool is chosen.
function startLocalFonts() {
  if (localReady) return;
  localReady = window.queryLocalFonts
    ? window.queryLocalFonts().then((list) => { localList = list; }, () => { localList = []; })
    : Promise.resolve().then(() => { localList = []; });
}

const normName = (s) => String(s || "").toLowerCase().replace(/[^a-z0-9]/g, "");
const STYLE_TAIL_RE = /(regular|bold|italic|oblique|medium|light|semibold|demibold|black|thin|book|roman|mt|ps)+$/;
const isStyle = (face, re) => re.test(face.style || "");

// The installed face a PDF font name (subset prefix already gone, as in
// "MeiryoUI" or "YuGothic-Regular") stands for.
function matchInstalled(pdfName) {
  if (!localList || !localList.length || !pdfName || /[^\x20-\x7e]/.test(pdfName)) return null;
  const n = normName(pdfName);
  if (!n) return null;
  const exact = localList.find((f) => normName(f.postscriptName) === n) ||
    localList.find((f) => normName(f.fullName) === n);
  if (exact) return exact;
  const base = n.replace(STYLE_TAIL_RE, "");
  const family = base ? localList.filter((f) => normName(f.family) === base) : [];
  return family.find((f) => isStyle(f, /^(regular|normal|book|roman)$/i)) || family[0] || null;
}

// Registers the family of an installed face for use as a text font and
// returns its key.
function registerInstalled(face, fallback) {
  const siblings = localList.filter((f) => f.family === face.family);
  const regular = siblings.find((f) => isStyle(f, /^(regular|normal|book|roman)$/i)) ||
    (isStyle(face, /bold/i) ? null : face) || face;
  const bold = siblings.find((f) => isStyle(f, /^bold$/i)) || (isStyle(face, /^bold$/i) ? face : null);
  const key = `local:${regular.postscriptName}`;
  if (!localFonts.has(key)) {
    const css = `"${face.family}", ${FONTS[fallback].css}`;
    measureCtx.font = `100px ${css}`;
    const m = measureCtx.measureText("あAg");
    localFonts.set(key, {
      family: face.family,
      css,
      regular,
      bold,
      fallback,
      mid: m.fontBoundingBoxAscent ? (m.fontBoundingBoxAscent - m.fontBoundingBoxDescent) / 200 : FONTS[fallback].mid,
    });
    const option = document.createElement("option");
    option.value = key;
    option.textContent = face.family;
    fontInput.appendChild(option);
  }
  return key;
}

// The installed font the block's text is drawn in: the font name most
// glyphs use, when this computer has it.
function installedFontByName(segments, block) {
  if (!localList || !localList.length) return null;
  const votes = new Map();
  for (const seg of segments) {
    if (!seg.visible || !seg.font || !inBlock(block, (seg.x0 + seg.x1) / 2, seg.y0)) continue;
    votes.set(seg.font, (votes.get(seg.font) || 0) + (seg.count || 1));
  }
  const [name] = [...votes].sort((p, q) => q[1] - p[1])[0] || [];
  const face = matchInstalled(name);
  if (!face) return null;
  return registerInstalled(face, fontFromName(name) || fontFromName(face.family) || "sans");
}

// Sans first: "Sans Serif", "Century Gothic". Japanese names may be stored
// as Shift_JIS or UTF-8 bytes (fontNameText).
const SANS_FONT_RE = /Sans|Gothic|ゴシック|Kaku|Maru|KozGo|Meiryo|メイリオ|Arial|Helvetica|Verdana|Tahoma|Segoe|Calibri|Roboto|Myriad|Frutiger|Futura|Gill|Trebuchet/i;
const SERIF_FONT_RE = /Serif|Mincho|Minchou|明朝|HiraMin|Ryumin|KozMin|Ming|Song|Batang|Myungjo|Times|Roman|Georgia|Garamond|Cambria|Century|Palatino|Antiqua|Baskerville|Bodoni|Caslon|Didot|Minion|Charter/i;

function fontNameText(name) {
  if (!/[\x80-\xff]/.test(name)) return name;
  const bytes = Uint8Array.from(name, (ch) => ch.charCodeAt(0) & 255);
  for (const encoding of ["utf-8", "shift_jis"]) {
    try {
      return new TextDecoder(encoding, { fatal: true }).decode(bytes);
    } catch (_) {
      // try the next one
    }
  }
  return name;
}

function fontFromName(name) {
  const text = fontNameText(name || "");
  if (SANS_FONT_RE.test(text)) return "sans";
  if (SERIF_FONT_RE.test(text)) return "serif";
  return null;
}

// Whether a baseline at (x, y) lies in the block (the whole page without one).
const inBlock = (block, x, y) => !block ||
  (x >= block.x - 1 && x <= block.x + block.w + 1 && y >= block.y - block.size * 0.5 && y <= block.y + block.h + 1);

// The typeface most glyphs in the block are drawn in, judged by font name.
function fontByName(segments, block) {
  const votes = { sans: 0, serif: 0 };
  for (const seg of segments) {
    if (!seg.visible || !inBlock(block, (seg.x0 + seg.x1) / 2, seg.y0)) continue;
    const font = fontFromName(seg.font);
    if (font) votes[font] += seg.count || 1;
  }
  if (!votes.sans && !votes.serif) return null;
  return votes.serif > votes.sans ? "serif" : "sans";
}

// pdf.js picks a fallback family for every font from its flags and name.
function fontByPdfjs(content, block) {
  if (!content) return null;
  const votes = { sans: 0, serif: 0 };
  for (const item of content.items) {
    if (!item.str || !item.str.trim() || !item.transform) continue;
    if (!inBlock(block, item.transform[4] + (item.width || 0) / 2, item.transform[5])) continue;
    const style = content.styles[item.fontName];
    const family = style && style.fontFamily;
    if (family === "serif") votes.serif += item.str.length;
    else if (family === "sans-serif") votes.sans += item.str.length;
  }
  if (!votes.sans && !votes.serif) return null;
  return votes.serif > votes.sans ? "serif" : "sans";
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

// --- alignment of original text -------------------------------------------------------------

// A PDF stores where each string starts, not how the paragraph was aligned.
// Several lines tell: equal left edges (left), equal right edges (right) or
// equal centers (center). null when they do not agree, or all lines are as
// wide as the block.
function alignOfLines(block, items) {
  const rows = [];
  for (const item of items || []) {
    const [a, b, , d, x, y] = item.transform || [];
    if (!item.str || !item.str.trim() || !(a > 0 && d > 0) || Math.abs(b) > a * 0.02) continue;
    if (x < block.x - 2 || x > block.x + block.w + 2) continue;
    if (y < block.y - block.size * 0.3 || y > block.y + block.h + block.size * 0.3) continue;
    let row = rows.find((r) => Math.abs(r.y - y) < 0.35 * block.size);
    if (!row) rows.push((row = { y, x0: x, x1: x }));
    row.x0 = Math.min(row.x0, x);
    row.x1 = Math.max(row.x1, x + (item.width || 0));
  }
  if (rows.length < 2) return null;
  const tol = block.size * 0.2;
  const same = (values) => values.every((v) => Math.abs(v - values[0]) <= tol);
  const left = same(rows.map((r) => r.x0));
  const right = same(rows.map((r) => r.x1));
  const center = same(rows.map((r) => (r.x0 + r.x1) / 2));
  if (left) return right && center ? null : "left";
  if (right) return "right";
  if (center) return "center";
  return null;
}

// Free background to the left and right of a block, in points, read from the
// rendered page: how far the block's background color goes before something
// else (a box edge, other text, a picture) starts.
function roomsAround(block, fillHex) {
  const dpr = window.devicePixelRatio || 1;
  const scale = view.vp.scale * dpr;
  const r = viewRect({ x1: block.x, y1: block.y, x2: block.x + block.w, y2: block.y + block.h }, view.vp);
  const y0 = Math.max(0, Math.floor((r.y + r.h * 0.2) * dpr));
  const y1 = Math.min(pdfCanvas.height, Math.ceil((r.y + r.h * 0.8) * dpr));
  const width = pdfCanvas.width;
  if (y1 <= y0 || !/^[0-9a-f]{6}$/i.test(fillHex)) return null;
  const rows = y1 - y0;
  const { data } = pdfCanvas.getContext("2d").getImageData(0, y0, width, rows);
  const fill = [0, 2, 4].map((i) => parseInt(fillHex.slice(i, i + 2), 16));
  const differs = (x) => {
    let n = 0;
    for (let y = 0; y < rows; y += 1) {
      const i = (y * width + x) * 4;
      if (Math.abs(data[i] - fill[0]) + Math.abs(data[i + 1] - fill[1]) + Math.abs(data[i + 2] - fill[2]) > 90) n += 1;
    }
    return n >= Math.max(1, rows * 0.06);
  };
  const pad = Math.max(2, Math.round(block.size * scale * 0.15));
  const from = Math.floor(r.x * dpr) - pad;
  const to = Math.ceil((r.x + r.w) * dpr) + pad;
  let left = Math.max(0, from);
  while (left > 0 && !differs(left - 1)) left -= 1;
  let right = Math.min(width - 1, to);
  while (right < width - 1 && !differs(right + 1)) right += 1;
  return { left: (from - left) / scale, right: (right - to) / scale };
}

// Alignment to keep when a block is replaced: the lines say it for a
// paragraph; for a single line the room on each side does. Equal room means
// centered, no room on the right means right-aligned, anything else left.
function guessAlign(block, fillHex) {
  if (block.lineAlign) return block.lineAlign;
  const rooms = viewReady() ? roomsAround(block, fillHex) : null;
  if (!rooms) return "left";
  const { left, right } = rooms;
  const near = block.size * 1.5;
  if (left < near && right < near) return "left";
  if (Math.abs(left - right) <= Math.max(block.size * 0.6, (left + right + block.w) * 0.08)) return "center";
  // other objects on the same row (a logo, a page number) cut the rooms
  // short; text centered on the page is still centered
  const [vx0, , vx1] = view.vp.viewBox;
  if (Math.abs(block.x + block.w / 2 - (vx0 + vx1) / 2) <= Math.max(block.size * 0.4, 2)) return "center";
  // a short line in the right half that ends near the page edge
  const nearEdge = vx1 - (block.x + block.w) <= Math.max(block.size * 2.5, (vx1 - vx0) * 0.04);
  if ((right < near && left > right) || (block.x + block.w / 2 > (vx0 + vx1) / 2 && nearEdge)) return "right";
  return "left";
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
  const ink = inkOf(style.color, sampled);
  const lineHeight = block.lines > 1 && block.leading > 0
    ? Math.round((block.leading / block.size) * 1000) / 1000
    : LINE_HEIGHT;
  const align = guessAlign(block, (sampled && sampled.fill) || "FFFFFF");
  // A paragraph keeps its width (with a little slack, as the replacement
  // font may run wider) and rewraps inside it, aligned the way it was. A
  // single line is aligned within its original width, so a longer or shorter
  // text grows or shrinks around the same left edge, center or right edge.
  const boxWidth = block.lines > 1 ? Math.round(block.w * 1.04 * 10) / 10 : null;
  const slack = boxWidth ? boxWidth - block.w : 0;
  pushUndo();
  const a = {
    id: nextId++,
    type: "text",
    text: block.text,
    x: block.x - slack * (ALIGN_FACTOR[align] || 0),
    y: block.firstBaseline + baselineOffset(lineHeight, block) * block.size,
    size: block.size,
    color: `#${ink.toLowerCase()}`,
    bold: style.bold,
    font: block.font,
    lineHeight,
    boxWidth,
    refWidth: boxWidth ? undefined : block.w,
    align: align === "left" ? undefined : align,
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
  ensureGlyphs(a.text, a);
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

// Puts the document's pages in this order. The tree is rebuilt flat with
// the pages' inherited attributes moved onto them, as pdf-lib's removePage
// would delete the page objects that are reused here. The original pages left
// out are deleted: bookmarks and form fields that point at them would
// otherwise keep their content in the file.
function setPageOrder(PDFLib, out, pages, original) {
  const { PDFName, PDFNumber, PDFPageLeaf } = PDFLib;
  for (const pg of pages) {
    for (const key of PDFPageLeaf.InheritableEntries) {
      const name = PDFName.of(key);
      const value = pg.node.getInheritableAttribute(name);
      if (value && !pg.node.get(name)) pg.node.set(name, value);
    }
  }
  const rootRef = out.catalog.get(PDFName.of("Pages"));
  for (const pg of pages) pg.node.setParent(rootRef);
  const root = out.catalog.Pages();
  root.set(PDFName.of("Kids"), out.context.obj(pages.map((pg) => pg.ref)));
  root.set(PDFName.of("Count"), PDFNumber.of(pages.length));
  const kept = new Set(pages);
  for (const pg of original) if (!kept.has(pg)) out.context.delete(pg.ref);
  // pdf-lib caches the page list and count
  out.pageCount = pages.length;
  out.pageCache.invalidate();
}

// Leaves out of the file the objects nothing refers to any more: the content
// streams removePageText replaced (they still hold the original text) and the
// page tree setPageOrder replaced. Fonts and images are embedded by save(),
// after this.
function dropUnreachable(PDFLib, out) {
  const { PDFRef, PDFDict, PDFArray, PDFStream } = PDFLib;
  const { context } = out;
  const seen = new Set();
  const stack = [context.trailerInfo.Root, context.trailerInfo.Info];
  while (stack.length) {
    let obj = stack.pop();
    if (obj instanceof PDFRef) {
      if (seen.has(obj)) continue;
      seen.add(obj);
      obj = context.lookup(obj);
    }
    if (obj instanceof PDFStream) obj = obj.dict;
    if (obj instanceof PDFDict) {
      for (const [, value] of obj.entries()) stack.push(value);
    } else if (obj instanceof PDFArray) {
      stack.push(...obj.asArray());
    }
  }
  for (const [ref] of context.enumerateIndirectObjects()) {
    if (!seen.has(ref)) context.delete(ref);
  }
}

// The fonts saved text is written in. An edited block keeps the installed
// font it was drawn in when that font is TrueType, may be embedded and has
// every character; otherwise it gets the Noto font the preview falls back
// to (counted in fontFallbacks). Returns a function from annotation to
// embedded font.
let fontFallbacks = 0;
const isCollection = (bytes) => bytes[0] === 0x74 && bytes[1] === 0x74 && bytes[2] === 0x63 && bytes[3] === 0x66; // "ttcf"

async function embedFonts(out, fontkit, texts) {
  let wanted; // PostScript name of the face to take from a .ttc
  const open = (bytes) => fontkit.create(bytes, isCollection(bytes) ? wanted : undefined);
  out.registerFontkit({ create: open });
  const parsed = new Map(); // installed face -> { bytes, font } or null
  const faces = new Map(); // key -> installed face
  const keys = new Map(); // annotation -> key of its font
  fontFallbacks = 0;

  const usable = async (face) => {
    if (!parsed.has(face)) {
      let entry = null;
      try {
        const bytes = new Uint8Array(await (await face.blob()).arrayBuffer());
        wanted = face.postscriptName;
        const font = open(bytes);
        const os2 = font["OS/2"];
        const restricted = os2 && (os2.fsType & 0x2) && !(os2.fsType & 0xc);
        if (font.directory.tables.glyf && !restricted) entry = { bytes, font };
      } catch (_) {
        entry = null;
      }
      parsed.set(face, entry);
    }
    return parsed.get(face);
  };

  for (const a of texts) {
    const local = localFonts.get(a.font);
    let key = null;
    if (local) {
      const face = (a.bold && local.bold) || local.regular;
      const entry = await usable(face);
      if (entry && [...a.text].every((ch) => /\s/.test(ch) || entry.font.hasGlyphForCodePoint(ch.codePointAt(0)))) {
        key = `local:${face.postscriptName}`;
        faces.set(key, face);
      } else {
        fontFallbacks += 1;
      }
    }
    if (!key) {
      const web = local ? FONTS[local.fallback] : fontOf(a);
      key = a.bold ? web.bold : web.regular;
    }
    keys.set(a, key);
  }

  const embedded = new Map();
  for (const key of new Set(keys.values())) {
    if (faces.has(key)) {
      const face = faces.get(key);
      wanted = face.postscriptName;
      embedded.set(key, await out.embedFont(parsed.get(face).bytes, { subset: true }));
    } else {
      const bytes = await loadFont(key);
      embedded.set(key, await out.embedFont(bytes, { subset: true }));
    }
  }
  return (a) => embedded.get(keys.get(a));
}

async function buildPdf(PDFLib, fontkit) {
  const { rgb, degrees, BlendMode, LineCapStyle } = PDFLib;
  // The first file is edited in place rather than copied page by page into a
  // new document, so what belongs to the whole document (form fields,
  // bookmarks, links between pages, metadata) stays.
  const out = await loadLibDoc(PDFLib, 0);
  const original = out.getPages();

  // One copyPages call per source keeps resources shared between its pages.
  const copied = new Map();
  for (let src = 0; src < doc.sources.length; src++) {
    const pages = doc.pages.filter((p) => p.src === src);
    if (!pages.length) continue;
    if (src === 0) {
      pages.forEach((p) => copied.set(p.id, original[p.index]));
      continue;
    }
    const source = await loadLibDoc(PDFLib, src);
    const copies = await out.copyPages(source, pages.map((p) => p.index));
    pages.forEach((p, i) => copied.set(p.id, copies[i]));
  }
  setPageOrder(PDFLib, out, doc.pages.map((p) => copied.get(p.id)), original);

  const texts = doc.pages.flatMap((p) => p.annots.filter((a) => a.type === "text" && a.text));
  let fontFor = () => null;
  if (texts.length) {
    setBusy(true, "日本語フォントを読み込み中…");
    fontFor = await embedFonts(out, fontkit, texts);
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
        if (a.kind === "fill") {
          pg.drawRectangle({ ...box, color });
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
          const layout = textLayout(a);
          layout.lines.forEach((line, i) => {
            if (!line) return;
            const [x, y] = vp.convertToPdfPoint(vx + layout.offsets[i], vy + (i * lh + baselineOffset(lh, a)) * a.size);
            pg.drawText(line, { x, y, size: a.size, font: fontFor(a), color, rotate: degrees(a.rotation) });
          });
        } else if (a.type === "image") {
          const [x, y] = vp.convertToPdfPoint(vx, vy + a.h);
          pg.drawImage(await embedImage(a.image), { x, y, width: a.w, height: a.h, rotate: degrees(a.rotation) });
        }
      }
    }
  }
  out.setModificationDate(new Date());
  dropUnreachable(PDFLib, out);
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
    savedVersion = version;
    const notes = [];
    if (doc.sources.some((s) => s.restricted)) notes.push("印刷・編集の制限は外れています");
    if (fontFallbacks) notes.push(`${fontFallbacks} 件は元のフォントに文字がないため Noto で書きました`);
    showOk([`${filename} を保存しました`, ...notes].join("。"));
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
  if (name === "edit") startLocalFonts();
  placeFillTip();
  drawOverlay();
  updateControls();
}

// The fill warning sits above the 矩形塗り button, or below it when the
// toolbar is stuck at the top of the window and there is no room above.
const fillTip = document.getElementById("fillTip");
function placeFillTip() {
  fillTip.hidden = tool !== "fill";
  if (fillTip.hidden) return;
  const button = toolButtons.find((b) => b.dataset.tool === "fill");
  const bar = fillTip.parentElement.getBoundingClientRect();
  const rect = button.getBoundingClientRect();
  const above = rect.top - fillTip.offsetHeight - 6 >= 0;
  fillTip.style.left = `${Math.max(0, rect.left - bar.left)}px`;
  fillTip.style.top = above
    ? `${rect.top - bar.top - fillTip.offsetHeight - 6}px`
    : `${rect.bottom - bar.top + 6}px`;
}
window.addEventListener("scroll", placeFillTip, { passive: true });
window.addEventListener("resize", placeFillTip);

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
  if (version !== savedVersion) event.preventDefault();
});

updateControls();

(async function showAppVersion() {
  try {
    const res = await fetch("version.json", { cache: "no-store" });
    if (!res.ok) return;
    const data = await res.json();
    if (!data.version) return;
    document.getElementById("appVersion").textContent = `v${data.version}`;
    document.getElementById("appVersionLine").hidden = false;
  } catch (_) {}
})();

(async function showAppNav() {
  const nav = document.getElementById("appNav");
  if (!nav) return;
  try {
    const res = await fetch("apps.json", { cache: "no-store" });
    if (!res.ok) return;
    const apps = await res.json();
    if (!Array.isArray(apps) || apps.length === 0) return;
    const currentId = document.documentElement.dataset.app || "";
    const path = location.pathname.replace(/\/+$/, "");
    const nodes = [];
    for (const app of apps) {
      if (!app || !app.title || !app.url) continue;
      const current =
        (app.id && app.id === currentId) ||
        (app.id && path.endsWith(`/${app.id}`));
      if (nodes.length) nodes.push(document.createTextNode(" · "));
      if (current) {
        const span = document.createElement("span");
        span.textContent = app.title;
        nodes.push(span);
      } else {
        const a = document.createElement("a");
        a.href = app.url;
        a.textContent = app.title;
        nodes.push(a);
      }
    }
    if (!nodes.length) return;
    nav.replaceChildren(document.createTextNode("他サービス："), ...nodes);
    nav.hidden = false;
  } catch (_) {}
})();
