// The raw pages of pub.*: no CSS at all, only what the browser draws by itself.
// A table on a computer, lines with small pictures on a phone.

import { ID_PATTERN, STORE_BYTES, bytes, extensionOf, roundBytes } from "../../../src/utils/pub";
import { lastPart, parentOf, TOP, type FileRow, type Shelf } from "./store";

const HOST = "pub.szymon-wilczek.me";
const PUT_UP = "https://szymon-wilczek.me/pub/";
const ADMIN = "/~/";
const THUMB_HEIGHT = 56;
const PREVIEW_HEIGHT = 120;
const DATE_LENGTH = "2026-11-28".length;
const DEFAULT_OLDER_DAYS = 180;
export const MS_PER_DAY = 24 * 60 * 60 * 1000;

export type Layout = "table" | "lines";

const escape = (value: string) =>
  value.replace(
    /[&<>"']/g,
    (char) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[char]!,
  );

// a path as it goes into an href: each part encoded, the slashes kept
const href = (path: string) => path.split("/").map(encodeURIComponent).join("/");

export const day = (time: number) => new Date(time).toISOString().slice(0, DATE_LENGTH);
export const linkOf = (file: FileRow) => `/${file.id}${extensionOf(file.name)}`;
const shown = (path: string) => `/${path}`;

export function counted(count: number, one: string): string {
  return `${count} ${count === 1 ? one : `${one}s`}`;
}

export function page(title: string, body: string): string {
  return `<!doctype html>
<html lang="en">
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="color-scheme" content="light dark">
<title>${escape(title)}</title>
<body>
${body}
</body>
</html>
`;
}

function tag(type: string): string {
  if (type.startsWith("image/")) return "[IMG]";
  if (type.startsWith("video/")) return "[VID]";
  if (type.startsWith("audio/")) return "[SND]";
  if (type === "application/pdf") return "[PDF]";
  if (type.startsWith("text/") || type === "application/json") return "[TXT]";
  return "[   ]";
}

// a small picture of what the file is, when the browser can draw one
function picture(file: FileRow, height: number, still: boolean): string {
  const src = escape(linkOf(file));
  if (file.type.startsWith("image/"))
    return `<img src="${src}" height="${height}" alt="${escape(file.name)}" loading="lazy">`;
  if (file.type.startsWith("video/"))
    return still
      ? `<video src="${src}" height="${height}" preload="metadata" muted></video>`
      : `<video src="${src}" height="${height}" preload="metadata" controls></video>`;
  return "";
}

// one row of a listing, a folder or a file, the same for both layouts
interface Row {
  tag: string;
  name: string;
  open: string;
  link: string;
  size: string;
  date: string;
  kept: boolean;
  edit: string;
  drop: string;
  file?: FileRow;
}

function rows(shelf: Shelf, path: string, admin: boolean): Row[] {
  const base = admin ? ADMIN : "/";
  const folders = shelf.childFolders(path).map((folder): Row => {
    const inside = [
      ...(shelf.childFolders(folder.path).length > 0
        ? [counted(shelf.childFolders(folder.path).length, "folder")]
        : []),
      counted(shelf.filesIn(folder.path).length, "file"),
    ].join(", ");
    return {
      tag: "[DIR]",
      name: lastPart(folder.path),
      open: base + href(folder.path),
      link: "",
      size: inside,
      date: day(shelf.lastChange(folder.path)),
      kept: shelf.folderKept(folder.path),
      edit: `${ADMIN}${href(folder.path)}?edit`,
      drop: `${ADMIN}${href(folder.path)}?delete`,
    };
  });
  const files = shelf.filesIn(path).map(
    (file): Row => ({
      tag: tag(file.type),
      name: file.name,
      open: linkOf(file),
      link: linkOf(file),
      size: bytes(file.size),
      date: day(file.created),
      kept: shelf.fileKept(file),
      edit: `${ADMIN}${file.id}`,
      drop: `${ADMIN}${file.id}?delete`,
      file,
    }),
  );
  return [...folders, ...files];
}

const actions = (row: Row) =>
  row.kept
    ? `<b>kept</b> <a href="${escape(row.edit)}">[edit]</a>`
    : `<a href="${escape(row.edit)}">[edit]</a> <a href="${escape(row.drop)}">[X]</a>`;

function table(list: Row[], up: string | null, admin: boolean): string {
  const columns = admin ? 6 : 5;
  const rule = `<tr><th colspan="${columns}"><hr></th></tr>`;
  const extra = admin ? "<td></td>" : "";
  const lines = list.map(
    (row) =>
      `<tr><td>${row.tag}</td><td><a href="${escape(row.open)}">${escape(row.name)}</a></td><td>${escape(row.link)}</td><td align="right">${escape(row.size)}</td><td>${row.date}</td>${admin ? `<td>${actions(row)}</td>` : ""}</tr>`,
  );
  return [
    "<table>",
    `<tr><th></th><th>Name</th><th>Link</th><th>Size</th><th>Date</th>${admin ? "<th></th>" : ""}</tr>`,
    rule,
    ...(up === null
      ? []
      : [
          `<tr><td>[UP]</td><td><a href="${escape(up)}">Parent Directory</a></td><td></td><td>-</td><td></td>${extra}</tr>`,
        ]),
    ...lines,
    rule,
    "</table>",
  ].join("\n");
}

function lines(list: Row[], up: string | null, upName: string, admin: boolean): string {
  const items = list.map((row) => {
    const thumb = row.file ? picture(row.file, THUMB_HEIGHT, true) : "";
    const meta = row.file ? `${row.link} · ${row.size} · ${row.date}` : `${row.size} · ${row.date}`;
    return [
      "<p>",
      thumb ? `${thumb} ` : `${row.tag} `,
      `<a href="${escape(row.open)}">${escape(row.name)}</a>`,
      admin ? ` ${actions(row)}` : "",
      "<br>",
      `<small>${escape(meta)}</small>`,
      "</p>",
    ].join("");
  });
  return [
    ...(up === null ? [] : [`<p><a href="${escape(up)}">../</a> up to ${escape(upName)}</p>`]),
    ...items,
    "<hr>",
  ].join("\n");
}

function summary(shelf: Shelf, path: string): string {
  const folders = shelf.childFolders(path).length;
  const here = shelf.filesIn(path);
  if (path === TOP)
    return [
      counted(folders, "folder"),
      `${counted(here.length, "file")} here`,
      `${shelf.files.length} in all`,
    ].join(" · ");
  return [
    ...(folders > 0 ? [counted(folders, "folder")] : []),
    counted(here.length, "file"),
    bytes(here.reduce((sum, file) => sum + file.size, 0)),
  ].join(" · ");
}

export function listing(shelf: Shelf, path: string, layout: Layout, admin: boolean): string {
  const base = admin ? ADMIN : "/";
  const list = rows(shelf, path, admin);
  const up = path === TOP ? null : base + href(parentOf(path));
  const body =
    layout === "table" ? table(list, up, admin) : lines(list, up, shown(parentOf(path)), admin);
  const where = escape(shown(path));
  const parts = admin
    ? [
        `<p>editing · <a href="/${href(path)}">see it as everyone does</a> · <a href="${PUT_UP}">put something up</a></p>`,
        `<h1>Index of ${where}</h1>`,
        `<form method="post" action="${ADMIN}${href(path)}?make">new folder in ${where} <input name="name" type="text" size="14" required> <button>make</button></form>`,
        body,
        adminFoot(shelf),
      ]
    : [
        `<h1>Index of ${where}</h1>`,
        body,
        `<address>${HOST} · ${escape(summary(shelf, path))}</address>`,
      ];
  return page(`Index of ${shown(path)}`, parts.join("\n"));
}

function adminFoot(shelf: Shelf): string {
  const keptFiles = shelf.files.filter((file) => file.kept).length;
  const keptFolders = shelf.folders.filter((folder) => folder.kept).length;
  return [
    `<p>used ${bytes(shelf.used())} of ${roundBytes(STORE_BYTES)} · ${counted(keptFiles, "file")} and ${counted(keptFolders, "folder")} kept</p>`,
    `<form method="get" action="${ADMIN}">delete files older than <input name="older" type="number" min="1" size="3" value="${DEFAULT_OLDER_DAYS}"> days, kept ones stay <button>show them first</button></form>`,
  ].join("\n");
}

function folderChoice(shelf: Shelf, picked: string, leaveOut: string | null): string {
  const options = [TOP, ...shelf.folders.map((folder) => folder.path)]
    .filter((path) => leaveOut === null || !path.startsWith(leaveOut))
    .map(
      (path) =>
        `<option value="${escape(path)}"${path === picked ? " selected" : ""}>${escape(shown(path))}</option>`,
    );
  return `<select name="folder">${options.join("")}</select>`;
}

const back = (path: string) =>
  `<p><a href="${ADMIN}${href(path)}">← ${escape(shown(path))}</a></p>`;
const where = (file: FileRow) => `${HOST}${linkOf(file)}`;

export function editFile(shelf: Shelf, file: FileRow, problem = ""): string {
  const fromFolder = shelf.folderKept(file.folder);
  const preview = picture(file, PREVIEW_HEIGHT, false);
  return page(
    file.name,
    [
      back(file.folder),
      `<h1>${escape(file.name)}</h1>`,
      ...(preview ? [`<p>${preview}</p>`] : []),
      `<p><a href="${escape(linkOf(file))}">${escape(where(file))}</a><br>${bytes(file.size)} · ${escape(file.type)} · up since ${day(file.created)}</p>`,
      ...(problem ? [`<p><b>${escape(problem)}</b></p>`] : []),
      `<form method="post" action="${ADMIN}${file.id}">`,
      `<p><label>name <input name="name" type="text" size="24" value="${escape(file.name)}" required></label></p>`,
      `<p><label>folder ${folderChoice(shelf, file.folder, null)}</label></p>`,
      `<p><label><input name="kept" type="checkbox"${file.kept ? " checked" : ""}> keep it for good (no [X] while kept)</label>${fromFolder ? `<br><small>its folder is kept, so it stays either way</small>` : ""}</p>`,
      "<p><button>Save</button></p>",
      "</form>",
      "<p><small>the five letters never change, so moving and renaming keep every link alive</small></p>",
    ].join("\n"),
  );
}

export function editFolder(shelf: Shelf, path: string, problem = ""): string {
  const folder = shelf.folder(path)!;
  const above = parentOf(path);
  return page(
    shown(path),
    [
      back(above),
      `<h1>${escape(shown(path))}</h1>`,
      `<p>${escape(summary(shelf, path))} · since ${day(folder.created)}</p>`,
      ...(problem ? [`<p><b>${escape(problem)}</b></p>`] : []),
      `<form method="post" action="${ADMIN}${href(path)}?edit">`,
      `<p><label>name <input name="name" type="text" size="24" value="${escape(lastPart(path).slice(0, -1))}" required></label></p>`,
      `<p><label>in ${folderChoice(shelf, above, path)}</label></p>`,
      `<p><label><input name="kept" type="checkbox"${folder.kept ? " checked" : ""}> keep it and all inside for good (no [X] while kept)</label></p>`,
      "<p><button>Save</button></p>",
      "</form>",
      "<p><small>files keep their five letters, so moving and renaming a folder keeps every link alive</small></p>",
    ].join("\n"),
  );
}

const WARNING =
  "<p>The link stops working at once. Chats that already unfolded it may keep their own copy.</p>";

export function deleteFile(shelf: Shelf, file: FileRow): string {
  const preview = picture(file, PREVIEW_HEIGHT, true);
  const head = [
    `<h1>Delete ${escape(file.name)}?</h1>`,
    ...(preview ? [`<p>${preview}</p>`] : []),
    `<p>${escape(where(file))}<br>${bytes(file.size)} · in ${escape(shown(file.folder))} · up since ${day(file.created)}</p>`,
  ];
  const backTo = `<a href="${ADMIN}${href(file.folder)}">keep it, back to ${escape(shown(file.folder))}</a>`;
  const ask = shelf.fileKept(file)
    ? [
        `<p>It is kept, so it stays. <a href="${ADMIN}${file.id}">Unpin it first</a>, here or on its folder.</p>`,
        `<p>${backTo}</p>`,
      ]
    : [
        WARNING,
        `<form method="post" action="${ADMIN}${file.id}?delete"><button>Delete it</button> or ${backTo}</form>`,
      ];
  return page(`Delete ${file.name}?`, [...head, ...ask].join("\n"));
}

export function deleteFolder(shelf: Shelf, path: string): string {
  const { folders, files } = shelf.under(path);
  const size = files.reduce((sum, file) => sum + file.size, 0);
  const above = parentOf(path);
  const backTo = `<a href="${ADMIN}${href(above)}">keep it, back to ${escape(shown(above))}</a>`;
  const inside =
    files.length + folders.length === 0
      ? "<p>It is empty.</p>"
      : `<p>${counted(files.length, "file")} and ${counted(folders.length, "folder")} inside go with it, ${bytes(size)}.</p>`;
  const ask = shelf.holdsKept(path)
    ? [`<p>Something in there is kept, so it all stays. Unpin it first.</p>`, `<p>${backTo}</p>`]
    : [
        WARNING.replace("The link stops", "Every link inside stops"),
        `<form method="post" action="${ADMIN}${href(path)}?delete"><button>Delete it all</button> or ${backTo}</form>`,
      ];
  return page(
    `Delete ${shown(path)}?`,
    [`<h1>Delete ${escape(shown(path))}?</h1>`, inside, ...ask].join("\n"),
  );
}

export function older(old: FileRow[], days: number): string {
  const total = old.reduce((sum, file) => sum + file.size, 0);
  const items = old.map(
    (file) =>
      `<li><a href="${escape(linkOf(file))}">${escape(file.name)}</a> <small>${escape(shown(file.folder))} · ${bytes(file.size)} · ${day(file.created)}</small></li>`,
  );
  const ask =
    old.length === 0
      ? [
          `<p>Nothing that old, or all of it is kept.</p>`,
          `<p><a href="${ADMIN}">back to the index</a></p>`,
        ]
      : [
          `<p>${counted(old.length, "file")}, ${bytes(total)}, up before ${day(Date.now() - days * MS_PER_DAY)}. Kept ones are not on the list.</p>`,
          `<ul>\n${items.join("\n")}\n</ul>`,
          WARNING.replace("The link stops", "Their links stop"),
          `<form method="post" action="${ADMIN}?older=${days}"><button>${old.length === 1 ? "Delete it" : `Delete these ${old.length}`}</button> or <a href="${ADMIN}">keep them</a></form>`,
        ];
  return page(
    `Older than ${counted(days, "day")}`,
    [`<h1>Older than ${counted(days, "day")}</h1>`, ...ask].join("\n"),
  );
}

export function gone(path: string): string {
  const looksLikeId = ID_PATTERN.test(path.slice(1).split(".")[0]);
  return page(
    "Not here",
    [
      "<h1>Not here</h1>",
      `<p>Nothing lives at ${escape(path)}. ${looksLikeId ? "It may have been deleted, or the letters are off by one." : "It may have been deleted or moved."}</p>`,
      "<hr>",
      `<address><a href="/">Index of /</a> · ${HOST}</address>`,
    ].join("\n"),
  );
}
