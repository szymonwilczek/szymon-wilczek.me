-- What pub knows about its files; the bytes live in KV under each id.
-- A path is "photos/2026/"; the top is "" and has no row of its own.
CREATE TABLE IF NOT EXISTS folders (
  path TEXT PRIMARY KEY,
  kept INTEGER NOT NULL DEFAULT 0,
  created INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS files (
  id TEXT PRIMARY KEY,
  name TEXT NOT NULL,
  folder TEXT NOT NULL DEFAULT '',
  size INTEGER NOT NULL,
  type TEXT NOT NULL,
  created INTEGER NOT NULL,
  kept INTEGER NOT NULL DEFAULT 0
);
CREATE INDEX IF NOT EXISTS files_folder ON files (folder);
