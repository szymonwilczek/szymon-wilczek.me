# 公 pub

Files that stay up, open to anyone: a Cloudflare Worker with the bytes in
KV and everything about them in D1.

`/pub/` on the site takes my password, shows the folders, and puts files up
one by one into the folder I pick; each gets five letters and answers with
its link, `pub.szymon-wilczek.me/q4n8t.jpg`.

What the link gives back:

- the file itself, with the type it came with, so chats unfold images and
  video; images, video, audio, text, JSON and PDFs open in the browser,
  everything else downloads under its own name;
- anything but a PDF carries a CSP sandbox, so an HTML or SVG file is shown
  but can't run a script;
- the extension is only for show: `/q4n8t`, `/q4n8t.jpg` and an old
  extension from before a rename all reach the same file.

The top, `pub.szymon-wilczek.me/`, is an FTP-style index of every folder,
raw HTML without a line of CSS. A browser that says it is a phone gets
lines with small pictures, everything else gets a table.

Files stay until I delete them. Ticking "keep them for good" on `/pub/`,
or "keep" on a file or a folder under `/~/`, takes its `[X]` away; a kept
folder keeps all that is inside it.

## How it is kept

- KV `BYTES`: one value a file, under its five letters (at most 25 MB a
  file, one value holds 25 MiB).
- D1 `DB`: the `folders` and `files` tables from `schema.sql`. A file
  belongs to a folder by path, so moving or renaming either changes rows,
  never a link. Listing KV is capped at 1000 a day on the free plan, so
  nothing is ever listed from it.

`/~/` is the editing side, behind the browser's Basic Auth prompt (any
name, the same password): the index again with `[edit]` and `[X]`, new
folders, renaming and moving, keeping, and a sweep of files older than so
many days that shows what it would delete first. Its forms only count when
they come from `pub.*` itself.

The numbers live in `src/utils/pub.ts`, shared with the site.

## Setting it up

Once, from this directory, with a Cloudflare account (the free plan is
enough, no card):

```sh
npx wrangler login
npx wrangler kv namespace create BYTES   # put the id it prints under [[kv_namespaces]] as id
npx wrangler d1 create pub               # put the id it prints under [[d1_databases]] as database_id
npx wrangler d1 execute pub --remote --file schema.sql
npx wrangler secret put PUB_WORD         # the password for /pub/ and /~/
npx wrangler deploy
```

`deploy` makes `pub.website.com` the Worker's custom domain (the zone has
to be on the same Cloudflare account).

The password is only ever a Worker secret: it is never in the repository
and never in the site's build. `/pub/` asks for it and keeps it until that
tab closes.

To try it locally, without an account:

```sh
npx wrangler d1 execute pub --local --file schema.sql
npx wrangler dev --local --var PUB_WORD:test
```

## Limits

- 1 GB across all files (the free plan holds 1 GB of KV), 25 MB a file
- free KV allows 1000 writes a day: uploads and deletes count, one each
- 60 uploads or new folders a minute per address, and 10 wrong passwords
  a minute (`[[ratelimits]]`)
