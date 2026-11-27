// What pub holds: folders and files in D1, the bytes of each file in KV under its id.
// Everything is read in one go; a personal shelf stays small enough for that.

import type { ShelfFolder } from "../../../src/utils/pub";

export interface FileRow {
  id: string;
  name: string;
  folder: string;
  size: number;
  type: string;
  created: number;
  kept: number;
}

export interface FolderRow {
  path: string;
  kept: number;
  created: number;
}

export const TOP = "";

// the folder above: "photos/" for "photos/2026/", the top for "photos/"
export function parentOf(path: string): string {
  const cut = path.slice(0, -1).lastIndexOf("/");
  return cut < 0 ? TOP : path.slice(0, cut + 1);
}

// "2026/" out of "photos/2026/"
export const lastPart = (path: string) => path.slice(parentOf(path).length);

export class Shelf {
  readonly folders: FolderRow[];
  readonly files: FileRow[];
  private readonly keptPaths: string[];

  constructor(folders: FolderRow[], files: FileRow[]) {
    this.folders = folders;
    this.files = files;
    this.keptPaths = folders.filter((folder) => folder.kept).map((folder) => folder.path);
  }

  static async read(db: D1Database): Promise<Shelf> {
    const [folders, files] = await Promise.all([
      db.prepare("SELECT path, kept, created FROM folders ORDER BY path").all<FolderRow>(),
      db
        .prepare(
          "SELECT id, name, folder, size, type, created, kept FROM files ORDER BY name COLLATE NOCASE",
        )
        .all<FileRow>(),
    ]);
    return new Shelf(folders.results, files.results);
  }

  has = (path: string) => path === TOP || this.folders.some((folder) => folder.path === path);
  folder = (path: string) => this.folders.find((folder) => folder.path === path);
  file = (id: string) => this.files.find((file) => file.id === id);

  // a pin on a folder keeps all that is inside it
  folderKept = (path: string) => this.keptPaths.some((kept) => path.startsWith(kept));
  fileKept = (file: FileRow) => file.kept === 1 || this.folderKept(file.folder);

  childFolders = (path: string) => this.folders.filter((folder) => parentOf(folder.path) === path);
  filesIn = (path: string) => this.files.filter((file) => file.folder === path);

  // the folder and all below it
  under = (path: string) => ({
    folders: this.folders.filter((folder) => folder.path.startsWith(path) && folder.path !== path),
    files: this.files.filter((file) => file.folder.startsWith(path)),
  });

  // anything in there that a pin keeps, the folder's own pin included
  holdsKept(path: string): boolean {
    if (this.folderKept(path)) return true;
    const { folders, files } = this.under(path);
    return folders.some((folder) => folder.kept) || files.some((file) => file.kept);
  }

  // the newest file below, or the folder's own birth when it is empty
  lastChange(path: string): number {
    const { files } = this.under(path);
    const own = this.folder(path)?.created ?? 0;
    return files.reduce((latest, file) => Math.max(latest, file.created), own);
  }

  used = () => this.files.reduce((sum, file) => sum + file.size, 0);

  forPage(): ShelfFolder[] {
    return [TOP, ...this.folders.map((folder) => folder.path)].map((path) => ({
      path,
      files: this.filesIn(path).length,
      folders: this.childFolders(path).length,
      kept: path !== TOP && this.folderKept(path),
    }));
  }
}

// the folder and every one above it that is missing
export async function makeFolder(db: D1Database, path: string, now: number) {
  const chain: string[] = [];
  for (let at = path; at !== TOP; at = parentOf(at)) chain.unshift(at);
  if (chain.length === 0) return;
  await db.batch(
    chain.map((at) =>
      db
        .prepare("INSERT OR IGNORE INTO folders (path, kept, created) VALUES (?, 0, ?)")
        .bind(at, now),
    ),
  );
}

// a folder takes a new place under a folder that is there already;
// all below it moves along, and no link changes
export async function moveFolder(db: D1Database, from: string, to: string, kept: boolean) {
  const rest = from.length + 1;
  const moves =
    from === to
      ? []
      : [
          db
            .prepare("UPDATE folders SET path = ? || substr(path, ?) WHERE substr(path, 1, ?) = ?")
            .bind(to, rest, from.length, from),
          db
            .prepare(
              "UPDATE files SET folder = ? || substr(folder, ?) WHERE substr(folder, 1, ?) = ?",
            )
            .bind(to, rest, from.length, from),
        ];
  await db.batch([
    ...moves,
    db.prepare("UPDATE folders SET kept = ? WHERE path = ?").bind(kept ? 1 : 0, to),
  ]);
}

export async function dropFiles(db: D1Database, bytes: KVNamespace, ids: string[]) {
  if (ids.length === 0) return;
  await db.batch(ids.map((id) => db.prepare("DELETE FROM files WHERE id = ?").bind(id)));
  await Promise.all(ids.map((id) => bytes.delete(id)));
}

export async function dropFolder(db: D1Database, bytes: KVNamespace, shelf: Shelf, path: string) {
  const { files } = shelf.under(path);
  await dropFiles(
    db,
    bytes,
    files.map((file) => file.id),
  );
  await db
    .prepare("DELETE FROM folders WHERE substr(path, 1, ?) = ?")
    .bind(path.length, path)
    .run();
}
