# ngit

ngit is a work-alike git version written in Python by AI and a lot of
prompting. It is for local repos only and isn't usable against real Git
repos. It was more of an early AI-Vibe experiment that got out of hand ;)

The whole tool is one standard-library Python script, `notgit.py`
(installed as `ngit`). It keeps history in a `.notgit/` directory next to
your files and copies Git's command line closely enough that everyday local
work feels the same: `add`, `commit`, `status`, `diff`, `log`, `branch`,
`checkout`, `merge`, `stash` and friends.

The commit history shows how it was made: features and fixes came from
prompting several assistants (Claude, Codex, GPT), followed by rounds of
functional review, each pinned by a regression test.

---

## Contents

- [Install](#install)
- [Quick start](#quick-start)
- [Usage](#usage)
- [Design](#design)
- [Decisions and trade-offs](#decisions-and-trade-offs)
- [Differences from Git](#differences-from-git)
- [Development](#development)

---

## Install

You need Python 3.10 or newer (the code uses `X | None` annotations). There
are no third-party dependencies.

```sh
cp notgit.py ~/bin/ngit
chmod +x ~/bin/ngit
ngit --help
```

You can also run it in place with `python3 notgit.py <command>`. Every
example below works with either name.

---

## Quick start

```console
$ ngit init
Initialized empty notgit repository in /home/me/demo/.notgit/
$ ngit config user.name "Ada"
$ ngit config user.email ada@example.com

$ echo hello > hello.txt
$ ngit add .
$ ngit commit -m "First commit"
[main 6c75fcf] First commit
 2 files changed, 5 insertions(+)
 create mode 100644 .notgitignore
 create mode 100644 hello.txt

$ echo world >> hello.txt
$ ngit status --short
 M hello.txt
$ ngit commit -qam "Add world"
$ ngit log --oneline
e2b9d99 (HEAD -> main) Add world
6c75fcf First commit
```

`init` also writes a starter `.notgitignore` (`__pycache__/`, `*.pyc`,
`.DS_Store`). The default branch is `main`; use `init -b <name>` to pick
another.

---

## Usage

Run `ngit --help` for the grouped synopsis, or `ngit <command> -h` for every
option of one command. Options follow Git's spelling wherever a feature
exists in both.

### Commands

| Area | Commands |
| --- | --- |
| Start a working area | `init`, `clone`, `import-git` |
| Work on the current change | `add`, `rm`, `mv`, `restore`, `reset` |
| Examine history and state | `status`, `log`, `show`, `diff`, `grep`, `ls`, `versions`, `rev-parse` |
| Grow, mark and tweak history | `commit`, `branch`, `checkout`, `merge`, `revert`, `tag`, `stash` |
| Settings | `config` |

### Everyday examples

```sh
ngit add -A                      # stage everything, including deletions
ngit add -p                      # choose files to stage interactively
ngit diff --staged --stat        # what will be committed
ngit commit --amend --no-edit    # fold staged changes into HEAD

ngit checkout -b topic           # new branch from HEAD
ngit checkout main               # switch; unrelated local edits come along
ngit checkout HEAD~2 -- app.py   # take one file from an older commit
ngit merge topic                 # fast-forward or three-way merge
ngit merge --squash topic        # bring the changes in without a merge commit

ngit stash push -u -m "wip"      # include untracked files
ngit stash pop --index           # restore the staged state too

ngit log --oneline --all -- src/ # history of a directory
ngit show HEAD:src/app.py        # a file as it was in a commit
ngit grep -n -e TODO -- src      # search tracked files
ngit reset --keep HEAD~1         # move back, refusing to lose local edits
ngit revert -m 1 <merge>         # undo a merge commit
```

### Revisions and paths

- A `<rev>` is `HEAD`, a branch, a tag, or a full or abbreviated object ID
  (at least four hex digits), optionally followed by `~<n>` and `^<n>`, as
  in `HEAD~2`, `main^`, `HEAD^2~1`. `rev^{commit}` is accepted by `rev-parse`.
- `<rev>:<path>` names a file or directory in that commit; `:<path>` is the
  staged copy. The path is relative to the repository root unless it
  starts with `./` or `../`.
- Paths are relative to the directory you run `ngit` from, as in Git, and a
  path that leaves the repository is rejected.
- `--` ends the revision list for `diff`, `checkout`, `reset` and `grep`.
  A name that is both an abbreviated object ID and a file (`cafe`,
  `beef`, ...) is refused as ambiguous until you add `--`.

### Commands Git doesn't have

```console
$ ngit ls
FILE           LAST ADD          LAST COMMIT
--------------------------------------------
.notgitignore  2026-10-15 19:29  2026-10-15 19:29 (6c75fcf)
hello.txt      2026-10-15 19:29  2026-10-15 19:29 (e2b9d99)

$ ngit versions hello.txt
hello_6c75fcf_20261015_1929_1.txt
hello_e2b9d99_20261015_1929_2.txt
```

- `ls` lists tracked files with the time each was last staged and the last
  commit that changed it.
- `versions <file>` writes every distinct committed version of a file next
  to it, named `<stem>_<commit>_<date>_<n><ext>`, oldest first. It refuses
  to overwrite existing files.

### Moving history between places

- `ngit clone <src> [<dest>]` copies another `.notgit` repository on the
  same machine (`--branch`, `--single-branch`, `--no-tags`, `--no-checkout`).
  The source is recorded as `remote.origin`, but there is no fetch, pull or
  push.
- `ngit import-git <git-repo> [<dest>]` converts a real Git repository into
  a **new** `.notgit` repository. It reads loose objects and pack files
  (`.idx` version 2), keeps branches, lightweight and annotated tags, and
  the checked-out branch. This is one-way: ngit never writes to a `.git`
  directory. Submodules are skipped with a warning. Symbolic links and
  executable bits do not survive, because ngit trees have no file modes.

### Configuration and environment

`ngit config <section.key> [value]` reads or writes `.notgit/config`. It also
supports `--list`, `--get`, `--unset` and `--default`.

| Setting | Used for |
| --- | --- |
| `user.name`, `user.email` | commit author and tagger |
| `NOTGIT_AUTHOR_NAME`, `NOTGIT_AUTHOR_EMAIL` | author when the config keys are unset |
| login name and `<user>@<hostname>` | last-resort author |
| `GIT_PAGER`, `PAGER` | pager for `diff` on a terminal (default `less`, with `LESS=FRX` unless you set it) |

---

## Design

### One script, standard library only

Everything lives in `notgit.py`: argument parsing, the object store, refs,
the index, diffing, merging and the Git importer. There is no build step,
no package and no dependency to install. `main()` builds an `argparse`
parser and dispatches each subcommand to a `cmd_<name>(args)` function.
`_normalize_argv()` rewrites the handful of Git spellings argparse can't
express directly (`-5` for `-n 5`, `--short=12`, flags after paths in
`diff`, paths after `--`, `-e -pattern`).

### Repository layout

```
.notgit/
  HEAD              "ref: refs/heads/main" or a detached commit id
  refs/heads/<name> one object id per branch (names may contain "/")
  refs/tags/<name>  a commit id, or the id of an annotated tag object
  objects/xx/yyyy…  content-addressed objects
  index             JSON {path: blob id}, the staging area
  index_times       JSON {path: time last staged}, used by `ls`
  config            JSON {section: {key: value}}
  stash             JSON list of stash entries, newest first
  MERGE_HEAD, MERGE_MSG, MERGE_CONFLICTS       in-progress merge
  REVERT_HEAD, REVERT_MSG, REVERT_CONFLICTS    in-progress revert
  LOCK, TRANSACTION, .transaction-*            concurrency and crash safety
```

### Objects

Each object is stored as `<type> <size>\0<content>` under the SHA-1 of
those exact bytes, split into a two-character directory as in Git.

- **Blobs** are raw file bytes with Git's header, so a blob's ID is the same
  one Git would compute for that file.
- **Trees, commits and annotated tags** are JSON documents, so their IDs are
  ngit's own. A tree lists `{name, type, oid}` entries; a commit records
  `tree`, `parents`, `author`, `message` and a Unix `timestamp`.
- Objects are not compressed and are never packed or garbage-collected.
- Every read checks the hash, the header and the declared size, and
  refuses objects that don't match. Tree entry names are checked so a
  crafted tree can't write outside the work tree.
- Readers still accept the original flat `objects/<id>` layout from early
  versions.

### Index and working tree

The index is a flat map from repository-relative path to blob ID, and the
next commit's tree is built from it alone. A working-tree scan walks the
tree, skips `.notgit/` and ignored paths, and hashes files in 1 MiB chunks.
Files are opened without following links or blocking on FIFOs and devices,
and a file that changes while it is being read is reported instead of being
hashed half-written.

### Writes, locking and recovery

- **Atomic files.** Refs, the index, config and state files are written to a
  temporary file, fsynced, renamed into place, and the directory is
  fsynced.
- **One writer at a time.** Commands that modify the repository hold an
  advisory lock on `.notgit/LOCK` (`flock`, or `msvcrt` on Windows). A
  second writer fails at once instead of waiting. Read-only commands don't
  take the lock.
- **Transactions.** Operations that touch several files at once (checkout,
  reset, merge, stash, restore) go through a small journal:
  1. Back up every file that will change, and stage the new contents.
  2. Write `.notgit/TRANSACTION`.
  3. Apply the changes and update the index and refs.
  4. Delete the journal.

  If anything fails, or the process dies part-way, the next modifying
  command rolls back from the backups and prints
  `warning: recovered an interrupted repository transaction`.

### Merging

`merge` finds the best common ancestor, the merge base. It fast-forwards
when it can, and otherwise does a three-way merge file by file:

- If only one side changed a file, that side wins.
- If both changed it, line edits are computed against the base with
  `difflib`. Edits that don't overlap are combined, and identical edits are
  applied once.
- Overlapping edits produce one conflict block for the whole file, in diff3
  style:

  ```
  <<<<<<< HEAD (main)
  …ours…
  ||||||| merged common ancestors
  …base…
  =======
  …theirs…
  >>>>>>> topic
  ```

- Binary files and files that aren't UTF-8 are never merged; they are
  marked as conflicts and keep our version.

Conflicted paths are recorded in `MERGE_CONFLICTS`. `commit` refuses to run
until each one has been re-added. `revert` is the same three-way merge with
the reverted commit as the base. `stash pop`/`apply` use it to replay a
stash onto a branch that has moved.

### Ignore rules

`.notgitignore` in the work-tree root uses gitignore syntax: `*`, `?`,
`**`, character classes including `[!…]`, leading `/` for anchoring, a
trailing `/` for directories only, `!` to negate, and `\#` and `\!` as
escapes. Rules are applied in order and the last match wins.

---

## Decisions and trade-offs

- **Local only.** ngit has no network code, remotes protocol or credentials.
  `clone` is a file copy and `import-git` is a one-way conversion. This kept
  the tool small and meant the store could be designed freely.
- **JSON instead of Git's binary formats.** Trees, commits, the index and
  stashes are human-readable and easy to debug with `cat`. The cost is that
  only blob IDs match Git's, so ngit can't read or write a `.git` directory
  in place. That is why "isn't usable against real Git repos" is a hard
  limit and not a missing feature.
- **No compression, no packs.** Objects are readable as they sit on disk.
  Repositories grow linearly with history, which is fine at the size of
  projects this was built for.
- **No file modes or symbolic links.** Every file is a plain `100644` file.
  An untracked symlink is skipped with a warning rather than followed or
  failing the scan. A tracked file that has been replaced by a symlink is
  an error, so it is never silently dropped from the index.
- **Safety over speed when files are written.** Every write is fsynced and
  multi-file updates are journaled. Work that would be wasted is skipped:
  content that is already stored isn't copied or fsynced again, and
  `checkout <path>` doesn't rewrite files that already match.
- **Git's behavior where it protects your work.** A branch switch carries
  unrelated local edits and staged files over and refuses only when a
  change would be overwritten. `--force` is the only way to discard.
  `branch -f`/`-M` won't move the checked-out branch. `stash --staged`
  refuses when it couldn't save everything.
- **Stricter than Git in a few places.** `merge`, `revert` and `stash pop`
  need a clean working tree, which avoids partial-overlap cases.
  `--no-index` diffs compare regular files only.
- **One file, many authors.** Keeping everything in one script made it easy
  to hand the whole program to an assistant in one go. The thick regression
  suite is what keeps those hand-offs honest.

---

## Differences from Git

Not implemented: remotes (`fetch`, `pull`, `push`), `rebase`,
`cherry-pick`, `switch`, `bisect`, `blame`, `worktree`, `submodule`,
hooks, the reflog, `gc`, signing, and `.gitattributes`.

Behaves differently:

- `commit` never opens an editor; give the message with `-m` or `-F`.
- Only the author and an author timestamp are recorded (no separate
  committer), and `--date` takes `YYYY-MM-DD[ HH:MM[:SS]]`, a year, or
  epoch seconds.
- Conflicts are whole-file. There are no hunk-level conflict regions, no
  rename detection, and no recursive or octopus strategies.
- Interactive modes (`add -p`, `reset -p`, `restore -p`, `stash -p`)
  choose whole files, not hunks.
- `log --graph` only prefixes each entry with `* `; it draws no lines.
- Ignore rules come from the root `.notgitignore` only; nested ignore
  files are not read. A negated rule can re-include a file even inside an
  ignored directory, which Git doesn't allow.
- Binary files are diffed as text with undecodable bytes replaced.
- Output follows Git's wording but says `diff --notgit` and `notgit` in
  hints.

---

## Development

```sh
python3 test_notgit.py            # full suite (unittest), several minutes
python3 test_notgit.py -v         # with test names
python3 -m pytest test_notgit.py  # same tests under pytest
python3 -m unittest test_notgit.TestStash.test_pop_restores_changes
```

Each test runs `notgit.py` as a subprocess inside its own temporary
directory, using the helpers on the `NG` base class (`init`, `write`,
`commit`, `ok`, `fail_ng`, …), so the suite never touches your repository.
New behavior comes with a regression test next to the related command
group.

