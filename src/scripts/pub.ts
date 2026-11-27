// /pub/: my word opens the shelf; files go up one by one into the folder I pick
import {
  ID_LENGTH,
  MAX_FILE_BYTES,
  PUB_URL,
  WORD_HEADER,
  bytes,
  extensionOf,
  roundBytes,
  type Count,
  type Put,
  type Shelf,
  type ShelfFolder,
} from "../utils/pub";
import { TRACK_LENGTH, fileIcon } from "../utils/send-ink";

const WORD_KEY = "pub:word";
const FOLDER_KEY = "pub:folder";
const COPIED_FOR_MS = 1400;
const MS_PER_SECOND = 1000;
const SECONDS_PER_MINUTE = 60;
const PERCENT = 100;
const SPEED_AFTER_MS = 1500;
const TILTS = ["-1.5deg", "0.9deg", "-0.6deg", "1.3deg"];
const NUMBER_WORDS = [
  "no",
  "one",
  "two",
  "three",
  "four",
  "five",
  "six",
  "seven",
  "eight",
  "nine",
  "ten",
];
const UNKNOWN_ID = "·".repeat(ID_LENGTH);
const TOP = "";
const SVG = "http://www.w3.org/2000/svg";

const $ = <T extends Element>(selector: string) => document.querySelector<T>(selector)!;

const unlockForm = $<HTMLFormElement>("[data-unlock]");
const wordEl = $<HTMLInputElement>("[data-word]");
const unlockError = $<HTMLElement>("[data-unlock-error]");
const countEl = $<HTMLElement>("[data-count]");
const form = $<HTMLFormElement>("[data-form]");
const fields = $<HTMLFieldSetElement>("[data-fields]");
const treeEl = $<HTMLUListElement>("[data-tree]");
const folderTemplate = $<HTMLTemplateElement>("[data-folder]");
const intoEl = $<HTMLElement>("[data-into]");
const newInEl = $<HTMLElement>("[data-new-in]");
const newNameEl = $<HTMLInputElement>("[data-new-name]");
const tray = $<HTMLElement>("[data-tray]");
const freeEl = $<HTMLElement>("[data-free]");
const freeBar = $<HTMLElement>("[data-free-bar]");
const queueEl = $<HTMLUListElement>("[data-queue]");
const rowTemplate = $<HTMLTemplateElement>("[data-row]");
const drop = $<HTMLElement>("[data-drop]");
const filesEl = $<HTMLInputElement>("[data-files]");
const keptEl = $<HTMLInputElement>("[data-kept]");
const sendLabel = $<HTMLElement>("[data-send-label]");
const progress = $<HTMLElement>("[data-progress]");
const progressName = $<HTMLElement>("[data-progress-name]");
const progressWhich = $<HTMLElement>("[data-progress-which]");
const pctEl = $<HTMLElement>("[data-pct]");
const inkEl = $<SVGRectElement>("[data-ink]");
const blot = $<HTMLElement>("[data-blot]");
const progressMeta = $<HTMLElement>("[data-progress-meta]");
const stopEl = $<HTMLButtonElement>("[data-stop]");
const errorEl = $<HTMLElement>("[data-error]");
const done = $<HTMLElement>("[data-done]");
const doneHead = $<HTMLElement>("[data-done-head]");
const linksEl = $<HTMLUListElement>("[data-links]");
const linkTemplate = $<HTMLTemplateElement>("[data-link]");
const doneStopped = $<HTMLElement>("[data-done-stopped]");
const copyAllEl = $<HTMLButtonElement>("[data-copy-all]");
const doneMeta = $<HTMLElement>("[data-done-meta]");

interface Entry {
  file: File;
  row: HTMLLIElement;
}

let word = "";
let shelf: Shelf | null = null;
let picked = TOP;
let queue: Entry[] = [];
let request: XMLHttpRequest | null = null;

class Stopped extends Error {}

function stored(key: string): string | null {
  try {
    return sessionStorage.getItem(key);
  } catch {
    return null;
  }
}

function store(key: string, value: string | null) {
  try {
    if (value === null) sessionStorage.removeItem(key);
    else sessionStorage.setItem(key, value);
  } catch {}
}

const shown = (path: string) => `/${path}`;
const counted = (count: number, one: string) => `${count} ${count === 1 ? one : `${one}s`}`;
const spelled = (count: number) => NUMBER_WORDS[count] ?? String(count);

function showError(target: HTMLElement, message: string) {
  target.textContent = message;
  target.hidden = false;
}

// the word fits, or it doesn't: the Worker's answer on every call
async function call(path: string, init: RequestInit = {}): Promise<Response> {
  return fetch(`${PUB_URL}${path}`, {
    ...init,
    headers: { ...init.headers, [WORD_HEADER]: word },
  });
}

function wrong(response: Response): string {
  if (response.status === 403) return "The password does not fit.";
  if (response.status === 429) return "Too many tries; wait a minute.";
  return "";
}

async function showCount() {
  try {
    const response = await fetch(`${PUB_URL}/~count`);
    if (!response.ok) return;
    const { folders, files, used, store: room }: Count = await response.json();
    countEl.textContent = [
      "up there now",
      counted(folders, "folder"),
      counted(files, "file"),
      `${bytes(used)} of ${roundBytes(room)}`,
    ].join(" · ");
  } catch {}
}

// the folders, each under its parent, the picked one with ink in its ring
function drawTree() {
  if (!shelf) return;
  if (!shelf.folders.some((folder) => folder.path === picked)) picked = TOP;
  treeEl.replaceChildren(...shelf.folders.map(folderRow));
  intoEl.textContent = shown(picked);
  newInEl.textContent = shown(picked);
}

function folderRow(folder: ShelfFolder): HTMLLIElement {
  const item = folderTemplate.content.firstElementChild!.cloneNode(true) as HTMLLIElement;
  const depth = folder.path === TOP ? 0 : folder.path.split("/").length - 1;
  const name = folder.path === TOP ? "/ the top" : folder.path.slice(0, -1).split("/").pop() + "/";
  const inside = [
    ...(folder.folders > 0 ? [counted(folder.folders, "folder")] : []),
    ...(folder.files > 0 || folder.folders === 0 ? [counted(folder.files, "file")] : []),
  ].join(", ");
  item.querySelector<HTMLElement>(".folder")!.style.setProperty("--depth", String(depth));
  item.querySelector("[data-folder-name]")!.textContent = name;
  item.querySelector("[data-folder-count]")!.textContent = inside;
  item.querySelector<HTMLElement>("[data-folder-kept]")!.hidden = !folder.kept;
  const pick = item.querySelector<HTMLInputElement>("[data-folder-pick]")!;
  pick.value = folder.path;
  pick.checked = folder.path === picked;
  pick.setAttribute("aria-label", folder.path === TOP ? "the top" : shown(folder.path));
  pick.addEventListener("change", () => {
    picked = folder.path;
    store(FOLDER_KEY, picked);
    intoEl.textContent = shown(picked);
    newInEl.textContent = shown(picked);
  });
  return item;
}

function free(): number {
  return shelf ? shelf.store - shelf.used : 0;
}

function showFree() {
  if (!shelf) return;
  freeEl.textContent = `${bytes(shelf.used)} of ${roundBytes(shelf.store)} used · ${bytes(MAX_FILE_BYTES)} a file at most`;
  freeBar.style.width = `${(shelf.used / shelf.store) * PERCENT}%`;
}

async function openShelf(): Promise<boolean> {
  const response = await call("/~shelf");
  const problem = wrong(response);
  if (problem) {
    store(WORD_KEY, null);
    showError(unlockError, problem);
    return false;
  }
  if (!response.ok) {
    showError(unlockError, `The shelf did not open: ${await response.text()}`);
    return false;
  }
  shelf = await response.json();
  store(WORD_KEY, word);
  drawTree();
  showFree();
  unlockForm.hidden = true;
  form.hidden = false;
  done.hidden = true;
  return true;
}

function closeShelf() {
  store(WORD_KEY, null);
  word = "";
  shelf = null;
  queue = [];
  redraw();
  wordEl.value = "";
  form.hidden = true;
  done.hidden = true;
  unlockForm.hidden = false;
  showCount();
  wordEl.focus();
}

function makeRow(file: File): HTMLLIElement {
  const row = rowTemplate.content.firstElementChild!.cloneNode(true) as HTMLLIElement;
  row.dataset.state = "queued";
  row.querySelector("[data-row-icon]")!.setAttribute("d", fileIcon(file.type));
  row.querySelector("[data-row-name]")!.textContent = file.name;
  row.querySelector("[data-row-ext]")!.textContent = extensionOf(file.name);
  row.querySelector("[data-row-size]")!.textContent = bytes(file.size);
  const out = row.querySelector<HTMLButtonElement>("[data-row-out]")!;
  out.setAttribute("aria-label", `take ${file.name} out`);
  out.addEventListener("click", () => {
    queue = queue.filter((entry) => entry.row !== row);
    redraw();
    filesEl.focus();
  });
  return row;
}

function redraw() {
  queueEl.replaceChildren(...queue.map((entry) => entry.row));
  tray.toggleAttribute("data-filled", queue.length > 0);
}

function addFiles(list: FileList | File[] | null) {
  if (!list) return;
  errorEl.hidden = true;
  const picked = [...list].filter((file) => file.size > 0 || file.type !== "");
  const tooBig = picked.filter((file) => file.size > MAX_FILE_BYTES);
  queue.push(
    ...picked
      .filter((file) => file.size <= MAX_FILE_BYTES)
      .map((file) => ({ file, row: makeRow(file) })),
  );
  redraw();
  if (tooBig.length > 0)
    showError(
      errorEl,
      `Left out, over ${bytes(MAX_FILE_BYTES)}: ${tooBig.map((file) => `${file.name} (${bytes(file.size)})`).join(", ")}.`,
    );
}

async function makeFolder() {
  const name = newNameEl.value.trim().replace(/^\/+|\/+$/g, "");
  if (!name) return;
  errorEl.hidden = true;
  const response = await call("/~folder", {
    method: "POST",
    headers: { "content-type": "application/json" },
    body: JSON.stringify({ path: `${picked}${name}` }),
  });
  if (!response.ok) return showError(errorEl, wrong(response) || (await response.text()));
  const { path, ...answer }: Shelf & { path: string } = await response.json();
  shelf = answer;
  picked = path;
  store(FOLDER_KEY, picked);
  newNameEl.value = "";
  drawTree();
}

function seconds(total: number): string {
  const rounded = Math.ceil(total);
  if (rounded < SECONDS_PER_MINUTE) return `${rounded} s`;
  return `${Math.ceil(rounded / SECONDS_PER_MINUTE)} min`;
}

function showProgress(sent: number, total: number, startedAt: number) {
  const share = total === 0 ? 1 : sent / total;
  const pct = Math.floor(share * PERCENT);
  pctEl.textContent = `${pct} %`;
  progress.setAttribute("aria-valuenow", String(pct));
  inkEl.setAttribute("width", String(share * TRACK_LENGTH));
  blot.style.left = `${share * PERCENT}%`;
  const elapsed = Date.now() - startedAt;
  const speed = elapsed > SPEED_AFTER_MS ? sent / (elapsed / MS_PER_SECOND) : 0;
  progressMeta.textContent = [
    `${bytes(sent)} of ${bytes(total)}`,
    ...(speed > 0 ? [`${bytes(speed)}/s`, `about ${seconds((total - sent) / speed)} left`] : []),
  ].join(" · ");
}

// XHR, because fetch cant tell how much of a body has gone
function put(file: File, folder: string, kept: boolean, moved: (loaded: number) => void) {
  return new Promise<Put>((resolve, reject) => {
    const query = new URLSearchParams({ folder, name: file.name, kept: kept ? "1" : "0" });
    request = new XMLHttpRequest();
    request.open("PUT", `${PUB_URL}/~file?${query}`);
    request.setRequestHeader(WORD_HEADER, word);
    request.upload.onprogress = (event) => moved(event.loaded);
    request.onload = function () {
      if (this.status < 300) resolve(JSON.parse(this.responseText));
      else reject(new Error(this.responseText || `${this.status}`));
    };
    request.onerror = () => reject(new Error("the connection dropped"));
    request.onabort = () => reject(new Stopped());
    request.send(file);
  });
}

function busy(on: boolean) {
  fields.disabled = on;
  sendLabel.textContent = on ? "putting up…" : "put them up";
  progress.hidden = !on;
}

function thumb(target: HTMLElement, put: Put) {
  if (put.type.startsWith("image/")) {
    target.append(Object.assign(new Image(), { src: put.link, alt: "", loading: "lazy" }));
    return;
  }
  if (put.type.startsWith("video/")) {
    const video = document.createElement("video");
    Object.assign(video, { src: put.link, muted: true, preload: "metadata" });
    target.append(video);
    return;
  }
  const svg = document.createElementNS(SVG, "svg");
  svg.setAttribute("viewBox", "0 0 24 24");
  svg.setAttribute("aria-hidden", "true");
  const path = document.createElementNS(SVG, "path");
  path.setAttribute("d", fileIcon(put.type));
  svg.append(path);
  target.append(svg);
}

function linkRow(put: Put, index: number): HTMLLIElement {
  const item = linkTemplate.content.firstElementChild!.cloneNode(true) as HTMLLIElement;
  const box = item.querySelector<HTMLElement>("[data-thumb]")!;
  box.style.setProperty("--tilt", TILTS[index % TILTS.length]);
  thumb(box, put);
  item.querySelector<HTMLAnchorElement>("[data-link-url]")!.href = put.link;
  item.querySelector("[data-link-id]")!.textContent = put.id;
  item.querySelector("[data-link-ext]")!.textContent = extensionOf(put.name);
  item.querySelector("[data-link-name]")!.textContent = `${put.name} · ${bytes(put.size)}`;
  item.querySelector<HTMLAnchorElement>("[data-link-open]")!.href = put.link;
  const copy = item.querySelector<HTMLButtonElement>("[data-link-copy]")!;
  copy.setAttribute("aria-label", `copy the link to ${put.name}`);
  copy.addEventListener("click", () => copied(copy, put.link, "copy"));
  return item;
}

async function copied(button: HTMLButtonElement, text: string, label: string) {
  await navigator.clipboard.writeText(text);
  button.textContent = "copied";
  setTimeout(() => (button.textContent = label), COPIED_FOR_MS);
}

// what unfolds in a chat, said plainly
function unfolds(puts: Put[]): string {
  const images = puts.filter((put) => put.type.startsWith("image/")).length;
  const clips = puts.filter((put) => put.type.startsWith("video/")).length;
  const kinds = [
    ...(images > 0 ? [images === 1 ? "the image" : "images"] : []),
    ...(clips > 0 ? [clips === 1 ? "the clip" : "the clips"] : []),
  ];
  return kinds.length === 0 ? "" : `${kinds.join(" and ")} unfold in chats`;
}

function showDone(puts: Put[], folder: string, kept: boolean, left: number) {
  const folderLink = Object.assign(document.createElement("a"), {
    href: `${PUB_URL}/${folder}`,
    target: "_blank",
    rel: "noopener",
    textContent: `${shown(folder)} ↗`,
  });
  doneHead.replaceChildren(
    `up · ${counted(puts.length, "file")} in `,
    folderLink,
    kept ? ", kept for good" : "",
  );
  linksEl.replaceChildren(...puts.map(linkRow));
  const all = puts.length === 1 ? "copy the link" : `copy all ${spelled(puts.length)} links`;
  copyAllEl.textContent = all;
  copyAllEl.onclick = () => copied(copyAllEl, puts.map((put) => put.link).join("\n"), all);
  doneStopped.hidden = left === 0;
  doneStopped.textContent = `Stopped before the rest: ${counted(left, "file")} did not go up and wait on the shelf.`;
  doneMeta.textContent = [
    "a link shows the file itself",
    ...(unfolds(puts) ? [unfolds(puts)] : []),
    ...(shelf ? [`${bytes(shelf.used)} of ${roundBytes(shelf.store)} used`] : []),
  ].join(" · ");
  form.hidden = true;
  done.hidden = false;
  copyAllEl.focus();
}

async function putUp() {
  const folder = picked;
  const kept = keptEl.checked;
  const total = queue.reduce((sum, entry) => sum + entry.file.size, 0);
  const startedAt = Date.now();
  const puts: Put[] = [];
  let before = 0;
  queue.forEach((entry) => (entry.row.dataset.state = "waiting"));
  showProgress(0, total, startedAt);

  let failure: Error | null = null;
  for (const [index, entry] of [...queue].entries()) {
    const { file, row } = entry;
    row.dataset.state = "now";
    progressName.textContent = file.name;
    progressWhich.textContent = `${index + 1} of ${queue.length + puts.length}`;
    try {
      const answer = await put(file, folder, kept, (loaded) => {
        const own = `${Math.floor((loaded / (file.size || 1)) * PERCENT)}%`;
        row.querySelector<HTMLElement>("[data-row-bar]")!.style.width = own;
        row.querySelector("[data-row-pct]")!.textContent = own;
        showProgress(before + loaded, total, startedAt);
      });
      puts.push(answer);
      before += file.size;
      row.dataset.state = "sent";
      row.querySelector("[data-row-id]")!.textContent = answer.id;
      queue = queue.filter((other) => other !== entry);
      if (shelf) shelf.used += file.size;
    } catch (error) {
      failure = error as Error;
      break;
    }
  }
  request = null;
  queue.forEach((entry) => {
    entry.row.dataset.state = "queued";
    entry.row.querySelector("[data-row-id]")!.textContent = UNKNOWN_ID;
  });
  redraw();

  if (puts.length > 0) return showDone(puts, folder, kept, queue.length);
  if (failure instanceof Stopped) return showError(errorEl, "Stopped. Nothing went up.");
  if (failure) showError(errorEl, `It did not go up: ${failure.message}`);
}

function invalid(): string | null {
  if (queue.length === 0) return "Nothing to put up yet.";
  const total = queue.reduce((sum, entry) => sum + entry.file.size, 0);
  if (total > free()) return `No room: ${bytes(total)} asked, ${bytes(free())} free.`;
  return null;
}

unlockForm.addEventListener("submit", async (event) => {
  event.preventDefault();
  unlockError.hidden = true;
  word = wordEl.value;
  try {
    await openShelf();
  } catch {
    showError(unlockError, "The shelf did not answer.");
  }
});

form.addEventListener("submit", async (event) => {
  event.preventDefault();
  errorEl.hidden = true;
  const problem = invalid();
  if (problem) return showError(errorEl, problem);
  busy(true);
  try {
    await putUp();
  } finally {
    busy(false);
    showFree();
  }
});

// ctrl + enter puts them up from anywhere in the form
form.addEventListener("keydown", (event) => {
  if (event.key !== "Enter") return;
  if (event.target === newNameEl) {
    event.preventDefault();
    if (!event.ctrlKey && !event.metaKey) return void makeFolder();
  }
  if (!(event.ctrlKey || event.metaKey)) return;
  event.preventDefault();
  if (!fields.disabled) form.requestSubmit();
});

stopEl.addEventListener("click", () => request?.abort());

// leaving mid-upload loses the file on its way
window.addEventListener("beforeunload", (event) => {
  if (request) event.preventDefault();
});

$("[data-close]").addEventListener("click", closeShelf);

$("[data-again]").addEventListener("click", async () => {
  done.hidden = true;
  form.hidden = false;
  try {
    await openShelf();
  } catch {}
  filesEl.focus();
});

filesEl.addEventListener("change", () => {
  addFiles(filesEl.files);
  filesEl.value = "";
});

// files dropped anywhere on the tray join the queue
tray.addEventListener("dragover", (event) => {
  if (fields.disabled || !event.dataTransfer?.types.includes("Files")) return;
  event.preventDefault();
  drop.toggleAttribute("data-over", true);
});
tray.addEventListener("dragleave", (event) => {
  if (!tray.contains(event.relatedTarget as Node)) drop.toggleAttribute("data-over", false);
});
tray.addEventListener("drop", (event) => {
  event.preventDefault();
  drop.toggleAttribute("data-over", false);
  if (!fields.disabled) addFiles(event.dataTransfer?.files ?? null);
});

// a screenshot pasted anywhere on the open shelf
document.addEventListener("paste", (event) => {
  if (form.hidden || fields.disabled) return;
  const pasted = event.clipboardData?.files;
  if (!pasted || pasted.length === 0) return;
  event.preventDefault();
  addFiles(pasted);
});

word = stored(WORD_KEY) ?? "";
picked = stored(FOLDER_KEY) ?? TOP;
if (word) {
  openShelf().catch(() => {
    unlockForm.hidden = false;
    showCount();
  });
} else {
  showCount();
}
