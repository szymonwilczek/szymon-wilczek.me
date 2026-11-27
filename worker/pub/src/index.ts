// Files that stay up, open to anyone
//   GET    /                         Index of /, raw HTML; /photos/2026/ for a folder
//   GET    /:id[.ext]                the file itself, ranges for video; the extension is only for show
//   GET    /~count                   how much is up, for the locked page on /pub/
//   GET    /~shelf                   the folders, for /pub/, with my word
//   POST   /~folder                  {path}: a new folder (and any missing above it), with my word
//   PUT    /~file?folder&name&kept   one file's bytes, with my word; answers its link
//   *      /~/...                    editing, behind a Basic prompt with the same word:
//                                    /~/<folder>/  listing   ?make ?edit ?delete
//                                    /~/<id>       edit      ?delete
//                                    /~/?older=N   files older than N days, then delete them
//
// Secret: PUB_WORD (the password, for /pub/ and the /~/ prompt alike)

import {
  MAX_FILE_BYTES,
  MAX_NAME_LENGTH,
  STORE_BYTES,
  WORD_HEADER,
  bytes,
  extensionOf,
  folderPath,
  ID_PATTERN,
  type Count,
  type Put,
  type Shelf as ShelfAnswer,
} from "../../../src/utils/pub";
import { randomId, same } from "../../send/src/secret";
import * as html from "./html";
import {
  dropFiles,
  dropFolder,
  makeFolder,
  moveFolder,
  parentOf,
  Shelf,
  TOP,
  type FileRow,
} from "./store";

interface Env {
  BYTES: KVNamespace;
  DB: D1Database;
  WRITES: RateLimit;
  GUESSES: RateLimit;
  PUB_WORD: string;
  ORIGINS: string; // comma-separated
}

const ADMIN = "/~/";
const API = "/~";
const FOLDER_BODY_LIMIT = 4096;
const ID_ATTEMPTS = 8;
const TYPE_PATTERN = /^[\w.+-]+\/[\w.+-]+$/;
const OPAQUE_TYPE = "application/octet-stream";
const SHOWN = /^((image|video|audio|text)\/|application\/(pdf|json)$)/;
const SANDBOX =
  "sandbox; default-src 'none'; img-src 'self'; media-src 'self'; style-src 'unsafe-inline'";
const PAGE_POLICY =
  "default-src 'none'; img-src 'self'; media-src 'self'; form-action 'self'; frame-ancestors 'none'; base-uri 'none'";
const RANGE = /^bytes=(\d*)-(\d*)$/;
const MOBILE_AGENT = /Mobi|Android|iPhone|iPad|iPod/i;

export default {
  async fetch(request: Request, env: Env): Promise<Response> {
    const url = new URL(request.url);
    let path: string;
    try {
      path = decodeURIComponent(url.pathname);
    } catch {
      return gone(url.pathname);
    }
    try {
      if (path === API || path.startsWith(ADMIN)) return await admin(path, url, request, env);
      if (path === `${API}count`)
        return await guarded(request, env, "GET", (cors) => count(env, cors));
      if (path === `${API}shelf`)
        return await guarded(request, env, "GET", (cors) => shelf(request, env, cors));
      if (path === `${API}folder`)
        return await guarded(request, env, "POST", (cors) => folder(request, env, cors));
      if (path === `${API}file`)
        return await guarded(request, env, "PUT", (cors) => put(url, request, env, cors));
      if (request.method !== "GET" && request.method !== "HEAD") return text("GET only", 405);
      return await look(path, request, env);
    } catch (error) {
      console.error(error);
      return text("something broke", 500);
    }
  },
};

// the API answers the garden only
async function guarded(
  request: Request,
  env: Env,
  method: string,
  handle: (cors: Record<string, string>) => Promise<Response>,
): Promise<Response> {
  const origin = request.headers.get("origin") || "";
  const allowed = env.ORIGINS.split(",").map((entry) => entry.trim());
  if (!allowed.includes(origin)) return text("not from the garden", 403);
  const cors = {
    "access-control-allow-origin": origin,
    "access-control-allow-methods": "GET, POST, PUT",
    "access-control-allow-headers": `content-type, ${WORD_HEADER}`,
    "access-control-max-age": "86400",
    vary: "origin",
  };
  if (request.method === "OPTIONS") return new Response(null, { status: 204, headers: cors });
  if (request.method !== method) return text(`${method} only`, 405, cors);
  return handle(cors);
}

const ip = (request: Request) => request.headers.get("cf-connecting-ip") || "";

// null when the word fits, or the answer to give instead
async function refused(
  given: string | null,
  request: Request,
  env: Env,
  cors: Record<string, string>,
): Promise<Response | null> {
  if (!env.PUB_WORD) return text("the password is not set", 503, cors);
  if (given !== null && (await same(given, env.PUB_WORD))) return null;
  if (!(await env.GUESSES.limit({ key: ip(request) })).success) return text("slow down", 429, cors);
  return text("the password does not fit", 403, cors);
}

async function count(env: Env, cors: Record<string, string>): Promise<Response> {
  const shelf = await Shelf.read(env.DB);
  const answer: Count = {
    folders: shelf.folders.length,
    files: shelf.files.length,
    used: shelf.used(),
    store: STORE_BYTES,
  };
  return json(answer, cors);
}

const shelfAnswer = (shelf: Shelf): ShelfAnswer => ({
  folders: shelf.forPage(),
  files: shelf.files.length,
  used: shelf.used(),
  store: STORE_BYTES,
});

async function shelf(request: Request, env: Env, cors: Record<string, string>) {
  const no = await refused(request.headers.get(WORD_HEADER), request, env, cors);
  if (no) return no;
  return json(shelfAnswer(await Shelf.read(env.DB)), cors);
}

async function folder(request: Request, env: Env, cors: Record<string, string>) {
  const no = await refused(request.headers.get(WORD_HEADER), request, env, cors);
  if (no) return no;
  if (!(await env.WRITES.limit({ key: ip(request) })).success) return text("slow down", 429, cors);
  const body = await request.text();
  if (body.length > FOLDER_BODY_LIMIT) return text("too big", 413, cors);
  let asked: { path?: unknown };
  try {
    asked = JSON.parse(body);
  } catch {
    return text("not JSON", 400, cors);
  }
  const path = folderPath(String(asked.path ?? ""));
  if (!path) return text("not a folder name: no ~ ? # % \\ and no empty parts", 400, cors);
  await makeFolder(env.DB, path, Date.now());
  return json({ path, ...shelfAnswer(await Shelf.read(env.DB)) }, cors);
}

const cleanName = (raw: string) =>
  raw
    .replace(/[\u0000-\u001f\u007f/\\]/g, "_")
    .trim()
    .slice(0, MAX_NAME_LENGTH);

async function put(url: URL, request: Request, env: Env, cors: Record<string, string>) {
  const no = await refused(request.headers.get(WORD_HEADER), request, env, cors);
  if (no) return no;
  if (!(await env.WRITES.limit({ key: ip(request) })).success) return text("slow down", 429, cors);

  const length = request.headers.get("content-length");
  const size = Number(length);
  if (length === null || !Number.isSafeInteger(size) || size < 0)
    return text("the size is missing", 411, cors);
  if (size > MAX_FILE_BYTES) return text(`bigger than ${bytes(MAX_FILE_BYTES)}`, 413, cors);
  const name = cleanName(url.searchParams.get("name") ?? "");
  if (!name) return text("a file needs a name", 400, cors);
  const folder = folderPath(url.searchParams.get("folder") ?? "");
  const shelf = await Shelf.read(env.DB);
  if (folder === null || !shelf.has(folder)) return text("no such folder", 404, cors);
  const used = shelf.used();
  if (used + size > STORE_BYTES)
    return text(`no room: ${bytes(size)} asked, ${bytes(STORE_BYTES - used)} free`, 507, cors);

  const sent = (request.headers.get("content-type") || "").split(";")[0].trim().toLowerCase();
  const type = TYPE_PATTERN.test(sent) ? sent : OPAQUE_TYPE;
  const id = await freshId(env.DB);
  if (!id) return text("no free name, try again", 503, cors);
  const body = await request.arrayBuffer();
  if (body.byteLength !== size) return text("the file came in cut short", 400, cors);

  const created = Date.now();
  const kept = url.searchParams.get("kept") === "1" ? 1 : 0;
  await env.BYTES.put(id, body);
  try {
    await env.DB.prepare(
      "INSERT INTO files (id, name, folder, size, type, created, kept) VALUES (?, ?, ?, ?, ?, ?, ?)",
    )
      .bind(id, name, folder, size, type, created, kept)
      .run();
  } catch (error) {
    await env.BYTES.delete(id);
    throw error;
  }
  const answer: Put = {
    id,
    link: `${url.origin}/${id}${extensionOf(name)}`,
    name,
    size,
    folder,
    type,
  };
  return json(answer, cors);
}

async function freshId(db: D1Database): Promise<string | null> {
  for (let attempt = 0; attempt < ID_ATTEMPTS; attempt++) {
    const id = randomId();
    if (!(await db.prepare("SELECT 1 FROM files WHERE id = ?").bind(id).first())) return id;
  }
  return null;
}

// what anyone sees: a folder's index, a file, or Not here
async function look(path: string, request: Request, env: Env): Promise<Response> {
  const rest = path.slice(1);
  if (rest !== "" && !rest.endsWith("/")) {
    const [id, ...extension] = rest.split(".");
    if (!rest.includes("/") && extension.length <= 1 && ID_PATTERN.test(id))
      return serve(id, path, request, env);
    const shelf = await Shelf.read(env.DB);
    if (shelf.has(`${rest}/`)) return redirect(`/${encodedPath(rest)}/`, 301);
    return gone(path);
  }
  const shelf = await Shelf.read(env.DB);
  if (!shelf.has(rest)) return gone(path);
  return page(html.listing(shelf, rest, layoutFor(request), false), {
    "cache-control": "no-cache",
    vary: "sec-ch-ua-mobile, user-agent",
  });
}

// no CSS to switch by width, so the browser says whether it is a phone
function layoutFor(request: Request): html.Layout {
  const mobile = request.headers.get("sec-ch-ua-mobile");
  if (mobile === "?1") return "lines";
  if (mobile === "?0") return "table";
  return MOBILE_AGENT.test(request.headers.get("user-agent") || "") ? "lines" : "table";
}

async function serve(id: string, path: string, request: Request, env: Env): Promise<Response> {
  const file = await env.DB.prepare(
    "SELECT id, name, folder, size, type, created, kept FROM files WHERE id = ?",
  )
    .bind(id)
    .first<FileRow>();
  if (!file) return gone(path);

  // the bytes never change under one id, so a browser may keep them and only ask if they're still up
  const tag = `"${file.id}-${file.created}"`;
  const shown = SHOWN.test(file.type);
  const type =
    file.type.startsWith("text/") && !file.type.includes("charset")
      ? `${file.type}; charset=utf-8`
      : file.type;
  const headers: Record<string, string> = {
    "content-type": type,
    "content-disposition": `${shown ? "inline" : "attachment"}; ${filename(file.name)}`,
    "accept-ranges": "bytes",
    "cache-control": "public, no-cache",
    etag: tag,
    "x-content-type-options": "nosniff",
    "x-robots-tag": "noindex",
  };
  if (file.type !== "application/pdf") headers["content-security-policy"] = SANDBOX;
  if (request.headers.get("if-none-match") === tag)
    return new Response(null, { status: 304, headers });

  const range = wanted(request.headers.get("range"), file.size);
  if (range === "unsatisfiable")
    return text("out of range", 416, { "content-range": `bytes */${file.size}` });
  const [first, end] = range ?? [0, file.size];
  headers["content-length"] = String(end - first);
  if (range) headers["content-range"] = `bytes ${first}-${end - 1}/${file.size}`;
  const status = range ? 206 : 200;
  if (request.method === "HEAD") return new Response(null, { status, headers });

  const body = range
    ? (await env.BYTES.get(id, "arrayBuffer"))?.slice(first, end)
    : await env.BYTES.get(id, "stream");
  if (!body) return gone(path);
  return new Response(body, { status, headers });
}

function filename(name: string): string {
  const plain = name.replace(/[^\x20-\x7e]|["\\]/g, "_");
  return `filename="${plain}"; filename*=UTF-8''${encodeURIComponent(name)}`;
}

// one range, as a video player asks for it: [first, end), or null for all of it
function wanted(header: string | null, size: number): [number, number] | null | "unsatisfiable" {
  const match = header ? RANGE.exec(header.trim()) : null;
  if (!match || (match[1] === "" && match[2] === "")) return null;
  if (match[1] === "") {
    const tail = Math.min(Number(match[2]), size);
    return tail === 0 ? "unsatisfiable" : [size - tail, size];
  }
  const first = Number(match[1]);
  if (first >= size) return "unsatisfiable";
  const last = match[2] === "" ? size - 1 : Math.min(Number(match[2]), size - 1);
  return last < first ? "unsatisfiable" : [first, last + 1];
}

// the password from a Basic prompt; the name typed beside it doesn't matter
function password(authorization: string | null): string | null {
  const [scheme, encoded] = (authorization || "").split(" ");
  if (scheme?.toLowerCase() !== "basic" || !encoded) return null;
  try {
    const decoded = new TextDecoder().decode(
      Uint8Array.from(atob(encoded), (c) => c.charCodeAt(0)),
    );
    const colon = decoded.indexOf(":");
    return colon < 0 ? null : decoded.slice(colon + 1);
  } catch {
    return null;
  }
}

// editing: every page under /~/ asks for the word first
async function admin(path: string, url: URL, request: Request, env: Env): Promise<Response> {
  if (!env.PUB_WORD) return text("the password is not set", 503);
  const given = password(request.headers.get("authorization"));
  if (given === null || !(await same(given, env.PUB_WORD))) {
    if (given !== null && !(await env.GUESSES.limit({ key: ip(request) })).success)
      return text("slow down", 429);
    return text("locked", 401, { "www-authenticate": `Basic realm="pub", charset="UTF-8"` });
  }
  if (!path.startsWith(ADMIN)) return redirect(ADMIN);
  const posted = request.method === "POST";
  if (!posted && request.method !== "GET") return text("GET or POST only", 405);
  // the browser sends the word by itself, so a form from anywhere else must not count
  if (posted && request.headers.get("origin") !== url.origin) return text("not from here", 403);

  const rest = path.slice(ADMIN.length);
  const shelf = await Shelf.read(env.DB);
  const asks = (word: string) => url.searchParams.has(word);
  // a button with no fields may come with no type at all
  const form = posted && request.headers.has("content-type") ? await request.formData() : null;
  const field = (name: string) => String(form?.get(name) ?? "");

  if (rest === "" || rest.endsWith("/")) {
    if (!shelf.has(rest)) return gone(path);
    if (rest === TOP && asks("older")) return older(shelf, url, posted, env);
    if (asks("make")) {
      if (!posted) return redirect(ADMIN + encodedPath(rest));
      const made = folderPath(rest + field("name"));
      if (!made || parentOf(made) !== rest) return text("not a folder name: no / ~ ? # % \\", 400);
      await makeFolder(env.DB, made, Date.now());
      return redirect(ADMIN + encodedPath(made));
    }
    if (rest !== TOP && asks("edit")) {
      if (!posted) return page(html.editFolder(shelf, rest));
      return saveFolder(shelf, rest, field("name"), field("folder"), field("kept") !== "", env);
    }
    if (rest !== TOP && asks("delete")) {
      if (!posted) return page(html.deleteFolder(shelf, rest));
      if (shelf.holdsKept(rest)) return page(html.deleteFolder(shelf, rest), {}, 409);
      await dropFolder(env.DB, env.BYTES, shelf, rest);
      return redirect(ADMIN + encodedPath(parentOf(rest)));
    }
    return page(html.listing(shelf, rest, layoutFor(request), true), {
      vary: "sec-ch-ua-mobile, user-agent",
    });
  }

  const file = shelf.file(rest);
  if (!file) return gone(path);
  if (asks("delete")) {
    if (!posted) return page(html.deleteFile(shelf, file));
    if (shelf.fileKept(file)) return page(html.deleteFile(shelf, file), {}, 409);
    await dropFiles(env.DB, env.BYTES, [file.id]);
    return redirect(ADMIN + encodedPath(file.folder));
  }
  if (!posted) return page(html.editFile(shelf, file));
  const name = cleanName(field("name"));
  const into = field("folder");
  if (!name) return page(html.editFile(shelf, file, "A file needs a name."), {}, 400);
  if (!shelf.has(into)) return page(html.editFile(shelf, file, "That folder is gone."), {}, 400);
  await env.DB.prepare("UPDATE files SET name = ?, folder = ?, kept = ? WHERE id = ?")
    .bind(name, into, field("kept") !== "" ? 1 : 0, file.id)
    .run();
  return redirect(ADMIN + encodedPath(into));
}

async function saveFolder(
  shelf: Shelf,
  from: string,
  name: string,
  into: string,
  kept: boolean,
  env: Env,
): Promise<Response> {
  const again = (problem: string) => page(html.editFolder(shelf, from, problem), {}, 400);
  if (name.includes("/")) return again("A name has no / in it; pick the folder it goes in below.");
  if (!shelf.has(into) || into.startsWith(from)) return again("It can't go there.");
  const to = folderPath(into + name);
  if (!to || parentOf(to) !== into) return again("Not a folder name: no ~ ? # % \\ and not empty.");
  if (to !== from && shelf.has(to)) return again(`There is a ${to} already.`);
  await moveFolder(env.DB, from, to, kept);
  return redirect(ADMIN + encodedPath(into));
}

// the bulk clean: first the list, then, posted, they go
async function older(shelf: Shelf, url: URL, posted: boolean, env: Env): Promise<Response> {
  const days = Number(url.searchParams.get("older"));
  if (!Number.isSafeInteger(days) || days < 1) return redirect(ADMIN);
  const before = Date.now() - days * html.MS_PER_DAY;
  const old = shelf.files.filter((file) => file.created < before && !shelf.fileKept(file));
  if (!posted) return page(html.older(old, days));
  await dropFiles(
    env.DB,
    env.BYTES,
    old.map((file) => file.id),
  );
  return redirect(ADMIN);
}

const encodedPath = (path: string) => path.split("/").map(encodeURIComponent).join("/");

const PAGE_HEADERS = {
  "content-type": "text/html; charset=utf-8",
  "content-security-policy": PAGE_POLICY,
  "cache-control": "no-store",
  "x-content-type-options": "nosniff",
  "x-robots-tag": "noindex",
  "referrer-policy": "same-origin",
};

const page = (body: string, headers: Record<string, string> = {}, status = 200) =>
  new Response(body, { status, headers: { ...PAGE_HEADERS, ...headers } });

const gone = (path: string) => page(html.gone(path), {}, 404);

const redirect = (location: string, status = 303) =>
  new Response(null, { status, headers: { location } });

const RAW_HEADERS = {
  "content-type": "text/plain; charset=utf-8",
  "cache-control": "no-store",
  "x-robots-tag": "noindex",
  "x-content-type-options": "nosniff",
};

const text = (body: string, status = 200, headers: Record<string, string> = {}) =>
  new Response(body, { status, headers: { ...RAW_HEADERS, ...headers } });
const json = (value: unknown, headers: Record<string, string> = {}) =>
  new Response(JSON.stringify(value), {
    headers: {
      "content-type": "application/json; charset=utf-8",
      "cache-control": "no-store",
      ...headers,
    },
  });
