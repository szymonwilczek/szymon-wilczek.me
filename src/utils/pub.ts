// Shared by /pub/ and its Worker (worker/pub), so both sides agree on the rules

export { EXTENSION_PATTERN, ID_ALPHABET, ID_LENGTH, ID_PATTERN, bytes } from "./send";
import { EXTENSION_PATTERN, bytes } from "./send";

export const PUB_URL = "https://pub.szymon-wilczek.me";

const MB = 1_000_000;
const GB = 1_000_000_000;

// one KV value holds at most 25 MiB, a little more than this
export const MAX_FILE_BYTES = 25 * MB;
export const STORE_BYTES = 1 * GB;

export const MAX_NAME_LENGTH = 255;
export const MAX_FOLDER_NAME_LENGTH = 64;
export const MAX_FOLDER_DEPTH = 8;

// the page sends my word with every call in this header
export const WORD_HEADER = "x-pub-word";

// "photos/2026/" for photos/2026, "" for the top;
// null when a part is empty, a dot, or holds what a path can't
// (a "~" would meet the Worker's own pages, so it is out too)
export function folderPath(raw: string): string | null {
  const parts = raw.split("/").filter((part) => part !== "");
  if (parts.length > MAX_FOLDER_DEPTH) return null;
  for (const part of parts) {
    if (part.length > MAX_FOLDER_NAME_LENGTH || part.trim() !== part) return null;
    if (part === "." || part === ".." || /[\u0000-\u001f\u007f\\~?#%]/.test(part)) return null;
  }
  return parts.map((part) => `${part}/`).join("");
}

// the extension a link carries, from the file's name: ".jpg",
// or "" when it has none
export function extensionOf(name: string): string {
  const dot = name.lastIndexOf(".");
  if (dot <= 0) return "";
  const extension = name.slice(dot + 1).toLowerCase();
  return EXTENSION_PATTERN.test(extension) ? `.${extension}` : "";
}

// "1 GB", not "1.0 GB", for the round size of the whole store
export const roundBytes = (size: number) => bytes(size).replace(/\.0 /, " ");

// one folder as the shelf on /pub/ shows it; "" is the top
export interface ShelfFolder {
  path: string;
  files: number;
  folders: number;
  kept: boolean;
}

export interface Shelf {
  folders: ShelfFolder[];
  files: number;
  used: number;
  store: number;
}

// how much is up, for the locked page
export interface Count {
  folders: number;
  files: number;
  used: number;
  store: number;
}

export interface Put {
  id: string;
  link: string;
  name: string;
  size: number;
  folder: string;
  type: string;
}
