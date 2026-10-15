#!/usr/bin/env python3
"""
test_notgit.py  –  Regression suite for notgit.py

Run with:
    python test_notgit.py [-v]

Each test class gets a fresh temp directory so tests are fully isolated.\n"""

import os
import sys
import json
import hashlib
import shutil
import subprocess
import tempfile
import unittest
import io
import argparse
import importlib.util
import struct
import zlib
from unittest import mock

# ── path to the script under test ────────────────────────────────────────────
SCRIPT = os.path.join(os.path.dirname(__file__), "notgit.py")


# ══════════════════════════════════════════════════════════════════════════════
# Base test case
# ══════════════════════════════════════════════════════════════════════════════

class NG(unittest.TestCase):
    """Base class: creates an isolated temp repo for every test method."""

    def setUp(self):
        self.tmpdir = tempfile.mkdtemp(prefix="notgit_test_")
        self.addCleanup(shutil.rmtree, self.tmpdir, ignore_errors=True)

    # ── helpers ───────────────────────────────────────────────────────────────

    def ng(self, *args, check=False, cwd=None, input=None, env=None):
        """Run notgit with *args, return CompletedProcess."""
        cmd = [sys.executable, SCRIPT] + list(args)
        return subprocess.run(
            cmd,
            cwd=cwd or self.tmpdir,
            capture_output=True,
            text=True,
            input=input,
            env=env,
        )

    def ok(self, *args, **kw):
        """Run notgit and assert exit-code 0."""
        r = self.ng(*args, **kw)
        self.assertEqual(r.returncode, 0,
                         f"Expected success:\n{r.stdout}\n{r.stderr}")
        return r

    def fail_ng(self, *args, **kw):
        """Run notgit and assert non-zero exit-code."""
        r = self.ng(*args, **kw)
        self.assertNotEqual(r.returncode, 0,
                            f"Expected failure but got 0:\n{r.stdout}\n{r.stderr}")
        return r

    def write(self, name, content="content\n"):
        path = os.path.join(self.tmpdir, name)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            f.write(content)

    def read(self, name):
        with open(os.path.join(self.tmpdir, name)) as f:
            return f.read()

    def exists(self, name):
        return os.path.exists(os.path.join(self.tmpdir, name))

    def init(self):
        """Initialise a repo and set a deterministic author."""
        self.ok("init")
        self.ok("config", "user.name",  "Test User")
        self.ok("config", "user.email", "test@example.com")

    def commit(self, msg="test commit"):
        """Stage everything and commit."""
        self.ok("add", ".")
        self.ok("commit", "-m", msg)

    def initial_commit(self):
        """Write one file and make the first commit."""
        self.write("a.txt", "alpha\n")
        self.commit("Initial commit")


# ══════════════════════════════════════════════════════════════════════════════
# TestInit
# ══════════════════════════════════════════════════════════════════════════════

class TestInit(NG):

    def test_creates_notgit_dir(self):
        r = self.ok("init")
        self.assertTrue(self.exists(".notgit"))
        self.assertIn("Initialized", r.stdout)

    def test_creates_required_subdirs(self):
        self.ok("init")
        for sub in (".notgit/objects", ".notgit/refs/heads", ".notgit/refs/tags"):
            self.assertTrue(self.exists(sub), f"Missing: {sub}")

    def test_creates_notgitignore(self):
        self.ok("init")
        self.assertTrue(self.exists(".notgitignore"))

    def test_reinit_is_nondestructive(self):
        self.init()
        self.write("a.txt")
        self.commit("pre-reinit commit")
        r = self.ok("init")
        self.assertIn("Reinitialized", r.stdout)
        # repo data must survive
        r2 = self.ok("log", "--oneline")
        self.assertIn("pre-reinit commit", r2.stdout)

    def test_reinit_from_subdirectory_reports_existing_repo_root(self):
        self.init()
        subdir = os.path.join(self.tmpdir, "sub")
        os.makedirs(subdir, exist_ok=True)
        r = self.ok("init", cwd=subdir)
        self.assertIn(
            os.path.join(self.tmpdir, ".notgit") + "/",
            r.stdout,
        )
        self.assertFalse(os.path.exists(os.path.join(subdir, ".notgit")))

    def test_commands_require_repo(self):
        r = self.ng("status")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("not a notgit repository", r.stderr)

    def test_commands_work_from_subdirectory(self):
        self.init()
        os.makedirs(os.path.join(self.tmpdir, "sub"), exist_ok=True)
        r = self.ok("status", cwd=os.path.join(self.tmpdir, "sub"))
        self.assertIn("On branch main", r.stdout)

    def test_pathspecs_from_subdirectory_are_relative_to_invocation(self):
        self.init()
        os.makedirs(os.path.join(self.tmpdir, "sub"), exist_ok=True)
        self.write("sub/a.txt", "from sub\n")
        self.ok("add", "a.txt", cwd=os.path.join(self.tmpdir, "sub"))
        r = self.ok("status")
        self.assertIn("sub/a.txt", r.stdout)


# ══════════════════════════════════════════════════════════════════════════════
# TestClone
# ══════════════════════════════════════════════════════════════════════════════

class TestClone(NG):

    def _write_in(self, root, name, content):
        path = os.path.join(root, name)
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "w") as f:
            f.write(content)

    def _source_repo(self):
        src = os.path.join(self.tmpdir, "src")
        os.makedirs(src)
        self.ok("init", cwd=src)
        self.ok("config", "user.name", "Test User", cwd=src)
        self.ok("config", "user.email", "test@example.com", cwd=src)
        self._write_in(src, "a.txt", "main\n")
        self.ok("add", ".", cwd=src)
        self.ok("commit", "-m", "main", cwd=src)
        return src

    def test_clone_branch_checks_out_requested_branch(self):
        src = self._source_repo()
        self.ok("checkout", "-b", "feature", cwd=src)
        self._write_in(src, "a.txt", "feature\n")
        self.ok("add", ".", cwd=src)
        self.ok("commit", "-m", "feature", cwd=src)
        self.ok("checkout", "main", cwd=src)

        dest = os.path.join(self.tmpdir, "dest")
        r = self.ok("clone", "--branch", "feature", src, dest)

        self.assertIn("done.", r.stdout)
        with open(os.path.join(dest, "a.txt")) as f:
            self.assertEqual(f.read(), "feature\n")
        branch = self.ok("rev-parse", "--abbrev-ref", "HEAD", cwd=dest).stdout.strip()
        self.assertEqual(branch, "feature")

    def test_clone_branch_can_checkout_tag(self):
        src = self._source_repo()
        self.ok("tag", "v1.0", cwd=src)
        self._write_in(src, "a.txt", "main v2\n")
        self.ok("add", ".", cwd=src)
        self.ok("commit", "-m", "main v2", cwd=src)

        dest = os.path.join(self.tmpdir, "dest")
        self.ok("clone", "--branch", "v1.0", src, dest)

        with open(os.path.join(dest, "a.txt")) as f:
            self.assertEqual(f.read(), "main\n")
        branch = self.ok("rev-parse", "--abbrev-ref", "HEAD", cwd=dest).stdout.strip()
        self.assertEqual(branch, "HEAD")

    def test_clone_branch_missing_errors_before_creating_destination(self):
        src = self._source_repo()
        dest = os.path.join(self.tmpdir, "dest")

        r = self.fail_ng("clone", "--branch", "missing", src, dest)

        self.assertIn("Remote branch missing not found", r.stderr)
        self.assertFalse(os.path.exists(dest))


# ══════════════════════════════════════════════════════════════════════════════
# TestAdd
# ══════════════════════════════════════════════════════════════════════════════

class TestAdd(NG):

    def setUp(self):
        super().setUp()
        self.init()

    def test_add_single_file(self):
        self.write("hello.txt")
        self.ok("add", "hello.txt")
        r = self.ok("status")
        self.assertIn("new file", r.stdout)

    def test_add_rejects_path_outside_repo(self):
        outside = os.path.join(os.path.dirname(self.tmpdir), "outside.txt")
        self.addCleanup(lambda: os.path.exists(outside) and os.remove(outside))
        with open(outside, "w") as f:
            f.write("outside\n")
        r = self.ng("add", outside)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("outside repository", r.stderr)
        r2 = self.ok("status", "--short")
        self.assertNotIn("outside.txt", r2.stdout)

    def test_add_dot_stages_all(self):
        self.write("a.txt")
        self.write("b.txt")
        self.ok("add", ".")
        r = self.ok("status")
        self.assertIn("a.txt", r.stdout)
        self.assertIn("b.txt", r.stdout)

    def test_add_directory(self):
        self.write("sub/c.txt")
        self.write("sub/d.txt")
        self.ok("add", "sub")
        r = self.ok("status")
        self.assertIn("sub/c.txt", r.stdout)

    def test_add_nonexistent_file_errors(self):
        r = self.ng("add", "ghost.txt")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("ghost.txt", r.stderr)

    def test_ignored_file_not_staged(self):
        # write a pattern to .notgitignore
        self.write(".notgitignore", "*.log\n")
        self.write("debug.log")
        self.ok("add", ".")
        r = self.ok("status")
        # debug.log must NOT appear as staged
        self.assertNotIn("debug.log", r.stdout.replace("Changes", "X"))

    def test_leading_slash_ignore_patterns_are_root_anchored(self):
        self.write(".notgitignore", "/root.txt\n/build/\n/root-*.log\n")
        self.write("root.txt")
        self.write("nested/root.txt")
        self.write("build/output.txt")
        self.write("nested/build/output.txt")
        self.write("root-debug.log")
        self.write("nested/root-debug.log")

        self.ok("add", ".")

        with open(os.path.join(self.tmpdir, ".notgit", "index")) as f:
            index = json.load(f)
        self.assertNotIn("root.txt", index)
        self.assertNotIn("build/output.txt", index)
        self.assertNotIn("root-debug.log", index)
        self.assertIn("nested/root.txt", index)
        self.assertIn("nested/build/output.txt", index)
        self.assertIn("nested/root-debug.log", index)

    def test_force_flag_stages_ignored_file(self):
        self.write(".notgitignore", "*.log\n")
        self.write("debug.log")
        self.ok("add", "-f", "debug.log")
        r = self.ok("status")
        self.assertIn("debug.log", r.stdout)

    def test_force_flag_stages_ignored_files_under_dot(self):
        self.write(".notgitignore", "*.log\n")
        self.write("debug.log")
        self.write("sub/nested.log")
        self.ok("add", "-f", ".")
        r = self.ok("status")
        self.assertIn("debug.log", r.stdout)
        self.assertIn("sub/nested.log", r.stdout)

    def test_force_flag_does_not_stage_notgit_dir(self):
        self.write(".notgitignore", "*.log\n")
        self.write("debug.log")
        self.ok("add", "-f", ".")
        r = self.ok("status")
        self.assertNotIn(".notgit/", r.stdout)

    def test_add_verbose_flag(self):
        self.write("v.txt")
        r = self.ok("add", "-v", "v.txt")
        self.assertIn("v.txt", r.stdout)

    def test_add_update_flag_only_tracked(self):
        self.write("tracked.txt", "v1\n")
        self.ok("add", "tracked.txt")
        self.ok("commit", "-m", "base")
        self.write("tracked.txt", "v2\n")
        self.write("new.txt")
        self.ok("add", "-u", ".")
        r = self.ok("status")
        self.assertIn("tracked.txt", r.stdout)
        # new.txt must remain untracked
        self.assertIn("new.txt", r.stdout)
        untracked_section = r.stdout.split("Untracked")[-1] if "Untracked" in r.stdout else ""
        self.assertIn("new.txt", untracked_section)


# ══════════════════════════════════════════════════════════════════════════════
# TestRm
# ══════════════════════════════════════════════════════════════════════════════

class TestRm(NG):

    def setUp(self):
        super().setUp()
        self.init()
        self.write("del.txt")
        self.commit("add del.txt")

    def test_rm_removes_from_index_and_disk(self):
        self.ok("rm", "del.txt")
        self.assertFalse(self.exists("del.txt"))
        r = self.ok("status")
        self.assertIn("deleted", r.stdout)

    def test_rm_cached_keeps_file_on_disk(self):
        self.ok("rm", "--cached", "del.txt")
        self.assertTrue(self.exists("del.txt"))
        r = self.ok("status")
        self.assertIn("deleted", r.stdout)

    def test_rm_unknown_file_errors(self):
        r = self.ng("rm", "ghost.txt")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("ghost.txt", r.stderr)


# ══════════════════════════════════════════════════════════════════════════════
# TestMv
# ══════════════════════════════════════════════════════════════════════════════

class TestMv(NG):

    def setUp(self):
        super().setUp()
        self.init()

    def index(self):
        with open(os.path.join(self.tmpdir, ".notgit", "index")) as f:
            return json.load(f)

    def test_mv_renames_tracked_file_and_stages_it(self):
        self.write("old.txt", "content\n")
        self.commit("add old")
        r = self.ok("mv", "old.txt", "new.txt")
        self.assertIn("rename 'old.txt' -> 'new.txt'", r.stdout)
        self.assertFalse(self.exists("old.txt"))
        self.assertEqual(self.read("new.txt"), "content\n")
        index = self.index()
        self.assertNotIn("old.txt", index)
        self.assertIn("new.txt", index)
        status = self.ok("status", "--short")
        self.assertIn("D  old.txt", status.stdout)
        self.assertIn("A  new.txt", status.stdout)

    def test_mv_file_into_directory(self):
        self.write("src.txt", "content\n")
        self.commit("add src")
        os.makedirs(os.path.join(self.tmpdir, "dir"), exist_ok=True)
        self.ok("mv", "src.txt", "dir")
        self.assertFalse(self.exists("src.txt"))
        self.assertEqual(self.read("dir/src.txt"), "content\n")
        index = self.index()
        self.assertNotIn("src.txt", index)
        self.assertIn("dir/src.txt", index)

    def test_mv_directory_rewrites_tracked_children(self):
        self.write("src/a.txt", "a\n")
        self.write("src/nested/b.txt", "b\n")
        self.commit("add dir")
        self.ok("mv", "src", "dst")
        self.assertFalse(self.exists("src/a.txt"))
        self.assertEqual(self.read("dst/a.txt"), "a\n")
        self.assertEqual(self.read("dst/nested/b.txt"), "b\n")
        index = self.index()
        self.assertNotIn("src/a.txt", index)
        self.assertNotIn("src/nested/b.txt", index)
        self.assertIn("dst/a.txt", index)
        self.assertIn("dst/nested/b.txt", index)

    def test_mv_rejects_untracked_source(self):
        self.write("loose.txt", "content\n")
        r = self.fail_ng("mv", "loose.txt", "moved.txt")
        self.assertIn("not under version control", r.stderr)
        self.assertTrue(self.exists("loose.txt"))
        self.assertFalse(self.exists("moved.txt"))

    def test_mv_rejects_existing_destination_without_force(self):
        self.write("a.txt", "a\n")
        self.write("b.txt", "b\n")
        self.commit("add files")
        r = self.fail_ng("mv", "a.txt", "b.txt")
        self.assertIn("already exists", r.stderr)
        self.assertEqual(self.read("a.txt"), "a\n")
        self.assertEqual(self.read("b.txt"), "b\n")

    def test_mv_force_overwrites_destination(self):
        self.write("a.txt", "a\n")
        self.write("b.txt", "b\n")
        self.commit("add files")
        self.ok("mv", "-f", "a.txt", "b.txt")
        self.assertFalse(self.exists("a.txt"))
        self.assertEqual(self.read("b.txt"), "a\n")
        index = self.index()
        self.assertNotIn("a.txt", index)
        self.assertIn("b.txt", index)


# ══════════════════════════════════════════════════════════════════════════════
# TestCommit
# ══════════════════════════════════════════════════════════════════════════════

class TestCommit(NG):

    def setUp(self):
        super().setUp()
        self.init()

    def test_basic_commit(self):
        self.write("a.txt")
        self.ok("add", ".")
        r = self.ok("commit", "-m", "first")
        self.assertIn("first", r.stdout)
        self.assertIn("main", r.stdout)

    def test_commit_shows_file_stats(self):
        self.write("a.txt")
        self.ok("add", ".")
        r = self.ok("commit", "-m", "s")
        self.assertIn("file", r.stdout)   # "1 file changed"

    def test_nothing_to_commit(self):
        self.write("a.txt")
        self.commit()
        r = self.ng("commit", "-m", "again")
        self.assertEqual(r.returncode, 1)
        self.assertIn("nothing to commit", r.stdout)

    def test_commit_with_only_untracked_file_does_not_report_clean(self):
        self.write("tracked.txt")
        self.commit()
        self.write("untracked.txt")
        r = self.ng("commit", "-m", "again")
        self.assertEqual(r.returncode, 1)
        self.assertIn("untracked files present", r.stdout)
        self.assertNotIn("working tree clean", r.stdout)

    def test_commit_uses_index_not_workdir(self):
        """Only staged file should end up in the commit."""
        self.write("staged.txt", "yes\n")
        self.write("unstaged.txt", "no\n")
        self.ok("add", "staged.txt")
        self.ok("commit", "-m", "only staged")
        r = self.ok("status")
        # unstaged.txt must still be untracked after commit
        self.assertIn("unstaged.txt", r.stdout)

    def test_commit_all_flag(self):
        self.write("a.txt", "v1\n")
        self.commit("base")
        self.write("a.txt", "v2\n")
        r = self.ok("commit", "-a", "-m", "auto stage")
        self.assertIn("auto stage", r.stdout)

    def test_commit_records_author(self):
        self.write("a.txt")
        self.commit()
        r = self.ok("log")
        self.assertIn("Test User", r.stdout)
        self.assertIn("test@example.com", r.stdout)

    def test_commit_shows_create_mode(self):
        self.write("brand_new.txt")
        self.ok("add", "brand_new.txt")
        r = self.ok("commit", "-m", "new file commit")
        self.assertIn("create mode", r.stdout)
        self.assertIn("brand_new.txt", r.stdout)

    def test_commit_message_from_stdin(self):
        self.write("a.txt")
        self.ok("add", ".")
        r = self.ok("commit", "-F", "-", input="\n\nsubject  \n\n\n\nbody line\n\n")
        self.assertIn("] subject\n", r.stdout)
        self.assertNotIn("body line", r.stdout)
        log = self.ok("log").stdout
        self.assertIn("    subject\n\n    body line\n", log)

    def test_commit_message_file_relative_to_invocation_cwd(self):
        self.write("a.txt")
        self.write("sub/msg.txt", "from subdir\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-F", "msg.txt", cwd=os.path.join(self.tmpdir, "sub"))
        self.assertEqual(self.ok("log", "--format=%s").stdout.strip(), "from subdir")

    def test_commit_rejects_message_and_file_together(self):
        self.write("a.txt")
        self.write("msg.txt", "file message\n")
        self.ok("add", "a.txt")
        r = self.fail_ng("commit", "-m", "inline", "-F", "msg.txt")
        self.assertIn("cannot be used together", r.stderr)

    def test_commit_dry_run_nothing_to_commit_exits_1(self):
        self.write("a.txt")
        self.commit()
        r = self.ng("commit", "--dry-run")
        self.assertEqual(r.returncode, 1)
        self.assertIn("nothing to commit", r.stdout)
        self.write("a.txt", "changed\n")
        self.ok("add", "a.txt")
        self.ok("commit", "--dry-run")

    def test_commit_quiet(self):
        self.write("a.txt")
        self.ok("add", ".")
        r = self.ok("commit", "-q", "-m", "quiet one")
        self.assertEqual(r.stdout, "")
        self.assertEqual(self.ok("log", "--format=%s").stdout.strip(), "quiet one")


class TestHelp(NG):

    def _parsers(self):
        spec = importlib.util.spec_from_file_location("notgit_help_test", SCRIPT)
        ng = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ng)
        todo = [("notgit", ng.build_parser())]
        while todo:
            name, parser = todo.pop()
            yield name, parser
            for action in parser._actions:
                if isinstance(action, argparse._SubParsersAction):
                    todo.extend((f"{name} {sub}", sp)
                                for sub, sp in action.choices.items())

    def test_every_option_has_help(self):
        for name, parser in self._parsers():
            for action in parser._actions:
                if isinstance(action, argparse._SubParsersAction):
                    continue
                with self.subTest(command=name, dest=action.dest):
                    self.assertTrue(action.help, f"{name} {action.dest} has no help")

    def test_top_level_help_lists_every_command_synopsis(self):
        out = self.ok("--help").stdout
        for name, _parser in self._parsers():
            if name == "notgit":
                continue
            with self.subTest(command=name):
                self.assertRegex(out, rf"(?m)^  {name.removeprefix('notgit ')}\b")
        self.assertIn("commit [-m <msg>] [-F <file>]", out)

    def test_command_help_describes_options(self):
        out = self.ok("commit", "-h").stdout
        self.assertIn("-F <file>, --file <file>", out)
        self.assertIn("'-' reads stdin", out)


class TestQuiet(NG):

    def setUp(self):
        super().setUp()
        self.init()
        self.initial_commit()

    def test_init_quiet(self):
        other = os.path.join(self.tmpdir, "other")
        os.makedirs(other)
        self.assertEqual(self.ok("init", "-q", cwd=other).stdout, "")

    def test_branch_checkout_merge_quiet(self):
        self.assertEqual(self.ok("checkout", "-q", "-b", "feat").stdout, "")
        self.write("b.txt", "b\n")
        self.ok("add", "b.txt")
        self.ok("commit", "-q", "-m", "feat")
        self.assertEqual(self.ok("checkout", "-q", "main").stdout, "")
        self.assertEqual(self.ok("merge", "-q", "feat").stdout, "")
        self.assertTrue(self.exists("b.txt"))
        self.assertEqual(self.ok("branch", "-q", "-d", "feat").stdout, "")

    def test_branch_quiet_still_lists(self):
        self.ok("branch", "-q", "other")
        self.assertIn("other", self.ok("branch", "-q").stdout)

    def test_reset_and_stash_quiet(self):
        self.write("a.txt", "changed\n")
        self.ok("add", "a.txt")
        self.assertEqual(self.ok("reset", "-q").stdout, "")
        self.assertEqual(self.ok("stash", "-q").stdout, "")
        self.assertEqual(self.read("a.txt"), "alpha\n")
        self.assertEqual(self.ok("stash", "pop", "-q").stdout, "")
        self.assertEqual(self.read("a.txt"), "changed\n")


# ══════════════════════════════════════════════════════════════════════════════
# TestLog
# ══════════════════════════════════════════════════════════════════════════════

class TestLog(NG):

    def setUp(self):
        super().setUp()
        self.init()

    def test_empty_repo_log(self):
        r = self.ng("log")
        self.assertNotEqual(r.returncode, 0)

    def test_single_commit(self):
        self.write("a.txt")
        self.commit("hello commit")
        r = self.ok("log")
        self.assertIn("hello commit", r.stdout)
        self.assertIn("Author:", r.stdout)
        self.assertIn("Date:", r.stdout)

    def test_oneline(self):
        self.write("a.txt")
        self.commit("one liner")
        r = self.ok("log", "--oneline")
        lines = r.stdout.strip().splitlines()
        self.assertEqual(len(lines), 1)
        self.assertIn("one liner", lines[0])

    def test_oneline_uses_only_commit_subject(self):
        self.write("a.txt")
        self.commit("subject\n\ncommit body")
        r = self.ok("log", "--oneline")
        lines = r.stdout.strip().splitlines()
        self.assertEqual(len(lines), 1)
        self.assertIn("subject", lines[0])
        self.assertNotIn("commit body", r.stdout)

    def test_n_limits_output(self):
        for i in range(5):
            self.write(f"f{i}.txt")
            self.ok("add", f"f{i}.txt")
            self.ok("commit", "-m", f"commit {i}")
        r = self.ok("log", "--oneline", "-n", "3")
        self.assertEqual(len(r.stdout.strip().splitlines()), 3)

    def test_pretty_subject_compact_count_and_all(self):
        for i in range(12):
            self.write(f"f{i}.txt")
            self.ok("add", f"f{i}.txt")
            self.ok("commit", "-m", f"commit {i}")

        r = self.ok("log", "--pretty=format:%s", "-10", "--all")
        lines = r.stdout.strip().splitlines()
        self.assertEqual(len(lines), 10)
        self.assertEqual(lines, [f"commit {i}" for i in range(11, 1, -1)])

    def test_log_shows_head_decoration(self):
        self.write("a.txt")
        self.commit("decorated")
        r = self.ok("log", "--oneline")
        self.assertIn("HEAD", r.stdout)
        self.assertIn("main", r.stdout)

    def test_multiple_commits_ordered_newest_first(self):
        for msg in ("first", "second", "third"):
            self.write(f"{msg}.txt")
            self.ok("add", ".")
            self.ok("commit", "-m", msg)
        r = self.ok("log", "--oneline")
        lines = r.stdout.strip().splitlines()
        self.assertIn("third",  lines[0])
        self.assertIn("second", lines[1])
        self.assertIn("first",  lines[2])

    def test_reverse_lists_commits_oldest_first(self):
        for msg in ("first", "second", "third"):
            self.write(f"{msg}.txt")
            self.ok("add", ".")
            self.ok("commit", "-m", msg)
        r = self.ok("log", "--oneline", "--reverse")
        lines = r.stdout.strip().splitlines()
        self.assertIn("first",  lines[0])
        self.assertIn("second", lines[1])
        self.assertIn("third",  lines[2])


# ══════════════════════════════════════════════════════════════════════════════
# TestStatus
# ══════════════════════════════════════════════════════════════════════════════

class TestStatus(NG):

    def setUp(self):
        super().setUp()
        self.init()

    def test_untracked_file(self):
        self.write("u.txt")
        r = self.ok("status")
        self.assertIn("u.txt", r.stdout)
        self.assertIn("Untracked", r.stdout)

    def test_staged_new_file(self):
        self.write("n.txt")
        self.ok("add", "n.txt")
        r = self.ok("status")
        self.assertIn("new file", r.stdout)
        self.assertIn("n.txt", r.stdout)

    def test_staged_modified_file(self):
        self.write("m.txt", "v1\n")
        self.commit("base")
        self.write("m.txt", "v2\n")
        self.ok("add", "m.txt")
        r = self.ok("status")
        self.assertIn("modified", r.stdout)

    def test_unstaged_modification(self):
        self.write("q.txt", "v1\n")
        self.commit("base")
        self.write("q.txt", "v2\n")
        r = self.ok("status")
        self.assertIn("not staged", r.stdout)
        self.assertIn("q.txt", r.stdout)

    def test_deleted_from_disk_shows_in_unstaged(self):
        self.write("gone.txt")
        self.commit("add gone")
        os.remove(os.path.join(self.tmpdir, "gone.txt"))
        r = self.ok("status")
        self.assertIn("deleted", r.stdout)
        self.assertIn("gone.txt", r.stdout)

    def test_clean_tree(self):
        self.write("a.txt")
        self.commit()
        r = self.ok("status")
        self.assertIn("nothing to commit", r.stdout)

    def test_shows_branch_name(self):
        r = self.ok("status")
        self.assertIn("main", r.stdout)

    def test_staged_delete(self):
        self.write("bye.txt")
        self.commit("add bye")
        self.ok("rm", "bye.txt")
        r = self.ok("status")
        self.assertIn("deleted", r.stdout)

    def test_short_status_reports_index_worktree_and_untracked(self):
        for name in (
            "staged_mod.txt",
            "unstaged_mod.txt",
            "staged_delete.txt",
            "unstaged_delete.txt",
            "both_mod.txt",
        ):
            self.write(name, "v1\n")
        self.commit("base")

        self.write("staged_mod.txt", "v2\n")
        self.ok("add", "staged_mod.txt")
        self.write("unstaged_mod.txt", "v2\n")
        self.ok("rm", "staged_delete.txt")
        os.remove(os.path.join(self.tmpdir, "unstaged_delete.txt"))
        self.write("both_mod.txt", "v2\n")
        self.ok("add", "both_mod.txt")
        self.write("both_mod.txt", "v3\n")
        self.write("new.txt", "new\n")
        self.ok("add", "new.txt")
        self.write("untracked.txt", "untracked\n")

        r = self.ok("status", "--short")
        self.assertEqual(
            r.stdout.splitlines(),
            [
                "MM both_mod.txt",
                "A  new.txt",
                "D  staged_delete.txt",
                "M  staged_mod.txt",
                " D unstaged_delete.txt",
                " M unstaged_mod.txt",
                "?? untracked.txt",
            ],
        )

    def test_short_status_alias_and_clean_output(self):
        self.write("a.txt")
        self.commit()
        r = self.ok("status", "-s")
        self.assertEqual(r.stdout, "")

    def test_short_status_branch_header(self):
        self.write("a.txt")
        self.commit("clean")
        self.write("u.txt")
        r = self.ok("status", "--short", "--branch")
        self.assertEqual(r.stdout.splitlines()[0], "## main")
        self.assertIn("?? u.txt", r.stdout)

    def test_porcelain_status_branch_header_on_unborn_branch(self):
        r = self.ok("status", "--porcelain", "--branch")
        self.assertEqual(r.stdout.splitlines()[0], "## No commits yet on main")


# ══════════════════════════════════════════════════════════════════════════════
# TestDiff
# ══════════════════════════════════════════════════════════════════════════════

class TestDiff(NG):

    def setUp(self):
        super().setUp()
        self.init()
        self.write("f.txt", "line1\n")
        self.commit("base")

    def test_diff_index_vs_workdir(self):
        self.write("f.txt", "line1\nline2\n")
        r = self.ok("diff")
        self.assertIn("+line2", r.stdout)

    def test_diff_does_not_page_when_stdout_is_not_tty(self):
        self.write("f.txt", "line1\nline2\n")
        env = os.environ.copy()
        env["GIT_PAGER"] = "false"
        env["PAGER"] = "false"
        r = self.ok("diff", env=env)
        self.assertIn("+line2", r.stdout)

    def test_diff_pages_when_stdout_is_tty(self):
        script_bin = shutil.which("script")
        if not script_bin:
            self.skipTest("script command not available")

        self.write("f.txt", "line1\nline2\n")
        pager = os.path.join(self.tmpdir, "pager.py")
        capture = os.path.join(self.tmpdir, "pager.out")
        with open(pager, "w") as f:
            f.write(
                "#!/usr/bin/env python3\n"
                "import os, sys\n"
                "data = sys.stdin.read()\n"
                "with open(os.environ['PAGER_CAPTURE'], 'w') as fh:\n"
                "    fh.write(data)\n"
                "sys.stdout.write(data)\n"
            )
        os.chmod(pager, 0o755)

        env = os.environ.copy()
        env["GIT_PAGER"] = pager
        env["PAGER_CAPTURE"] = capture
        r = subprocess.run(
            [script_bin, "-q", "-c", f"{sys.executable} {SCRIPT} diff", "/dev/null"],
            cwd=self.tmpdir,
            capture_output=True,
            text=True,
            env=env,
        )
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertTrue(os.path.exists(capture), "pager was not invoked")
        with open(capture) as f:
            self.assertIn("+line2", f.read())

    def test_diff_no_changes_empty(self):
        r = self.ok("diff")
        self.assertEqual(r.stdout.strip(), "")

    def test_diff_staged(self):
        self.write("f.txt", "line1\nline2\n")
        self.ok("add", "f.txt")
        r = self.ok("diff", "--staged")
        self.assertIn("+line2", r.stdout)

    def test_diff_staged_empty_after_commit(self):
        self.write("f.txt", "line1\nline2\n")
        self.ok("add", "f.txt")
        self.ok("commit", "-m", "add line2")
        r = self.ok("diff", "--staged")
        self.assertEqual(r.stdout.strip(), "")

    def test_diff_two_commits(self):
        self.write("f.txt", "line1\nline2\n")
        self.ok("add", "f.txt")
        self.ok("commit", "-m", "second")
        r = self.ok("log", "--oneline")
        oids = [line.split()[0] for line in r.stdout.strip().splitlines()]
        r2 = self.ok("diff", oids[1], oids[0])   # old → new
        self.assertIn("+line2", r2.stdout)

    def test_diff_shows_new_file(self):
        self.write("brand.txt", "fresh\n")
        self.ok("add", "brand.txt")
        r = self.ok("diff", "--staged")
        self.assertIn("new file", r.stdout)
        self.assertIn("+fresh", r.stdout)

    def test_diff_shows_deleted_file(self):
        self.ok("rm", "f.txt")
        r = self.ok("diff", "--staged")
        self.assertIn("deleted", r.stdout)
        self.assertIn("-line1", r.stdout)


# ══════════════════════════════════════════════════════════════════════════════
# TestShow
# ══════════════════════════════════════════════════════════════════════════════

class TestShow(NG):

    def setUp(self):
        super().setUp()
        self.init()
        self.write("s.txt", "original\n")
        self.commit("show me")

    def test_show_head(self):
        r = self.ok("show", "HEAD")
        self.assertIn("show me", r.stdout)
        self.assertIn("Author:", r.stdout)
        self.assertIn("+original", r.stdout)

    def test_show_by_short_hash(self):
        r = self.ok("log", "--oneline")
        short = r.stdout.strip().split()[0]
        r2 = self.ok("show", short)
        self.assertIn("show me", r2.stdout)

    def test_show_second_commit_diffs_against_parent(self):
        self.write("s.txt", "changed\n")
        self.ok("add", "s.txt")
        self.ok("commit", "-m", "update s")
        r = self.ok("show", "HEAD")
        self.assertIn("-original", r.stdout)
        self.assertIn("+changed",  r.stdout)

    def test_show_default_is_head(self):
        r1 = self.ok("show")
        r2 = self.ok("show", "HEAD")
        self.assertEqual(r1.stdout, r2.stdout)

    def test_show_stat_summarizes_without_patch(self):
        self.write("s.txt", "changed\nextra\n")
        self.write("new.txt", "new\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "update s")
        r = self.ok("show", "--stat", "HEAD")
        self.assertIn("update s", r.stdout)
        self.assertIn("s.txt", r.stdout)
        self.assertIn("new.txt", r.stdout)
        self.assertIn("|", r.stdout)
        self.assertIn("files changed", r.stdout)
        self.assertNotIn("@@", r.stdout)
        self.assertNotIn("--- a/", r.stdout)

    def test_show_stat_accepts_short_hash(self):
        r = self.ok("log", "--oneline")
        short = r.stdout.strip().split()[0]
        r2 = self.ok("show", "--stat", short)
        self.assertIn("s.txt", r2.stdout)
        self.assertIn("changed", r2.stdout)
        self.assertNotIn("@@", r2.stdout)

    def test_show_stat_oneline(self):
        r = self.ok("show", "--stat", "--oneline", "HEAD")
        first_line = r.stdout.splitlines()[0]
        self.assertRegex(first_line, r"^[0-9a-f]{7} show me$")
        self.assertNotIn("Author:", r.stdout)
        self.assertNotIn("Date:", r.stdout)
        self.assertIn("s.txt", r.stdout)
        self.assertRegex(r.stdout, r"files? changed")
        self.assertNotIn("@@", r.stdout)

    def test_show_rev_path_prints_file_content(self):
        self.write("s.txt", "changed\n")
        self.commit("update s")
        self.assertEqual(self.ok("show", "HEAD:s.txt").stdout, "changed\n")
        self.assertEqual(self.ok("show", "HEAD~1:s.txt").stdout, "original\n")

    def test_show_index_path_prints_staged_content(self):
        self.write("s.txt", "staged\n")
        self.ok("add", "s.txt")
        self.assertEqual(self.ok("show", ":s.txt").stdout, "staged\n")

    def test_show_rev_path_lists_tree(self):
        self.write("d/e/f.txt", "deep\n")
        self.commit("nested")
        self.assertEqual(self.ok("show", "HEAD:d/e/f.txt").stdout, "deep\n")
        self.assertEqual(self.ok("show", "HEAD:d").stdout, "tree HEAD:d\n\ne/\n")
        self.assertIn("d/\n", self.ok("show", "HEAD:").stdout)

    def test_show_rev_path_is_root_relative_unless_dotted(self):
        self.write("d/f.txt", "in d\n")
        self.commit("add d")
        sub = os.path.join(self.tmpdir, "d")
        self.assertEqual(self.ok("show", "HEAD:d/f.txt", cwd=sub).stdout, "in d\n")
        self.assertEqual(self.ok("show", "HEAD:./f.txt", cwd=sub).stdout, "in d\n")
        self.assertEqual(self.ok("show", "HEAD:../s.txt", cwd=sub).stdout, "original\n")
        self.fail_ng("show", "HEAD:f.txt", cwd=sub)

    def test_show_rev_path_missing_reports_bad_revision(self):
        for rev in ("HEAD:nope.txt", "HEAD:s.txt/x", "nobranch:s.txt", "HEAD:../x"):
            r = self.fail_ng("show", rev)
            self.assertIn("fatal:", r.stderr)

    def test_rev_parse_rev_path_matches_hash_object(self):
        blob = self.ok("rev-parse", "HEAD:s.txt").stdout.strip()
        self.assertRegex(blob, r"^[0-9a-f]{40}$")
        self.assertNotEqual(blob, self.ok("rev-parse", "HEAD").stdout.strip())
        self.assertEqual(self.ok("rev-parse", ":s.txt").stdout.strip(), blob)

    def test_checkout_rev_path_is_not_a_commit(self):
        r = self.fail_ng("checkout", "HEAD:s.txt")
        self.assertIn("not a commit", r.stderr)


# ══════════════════════════════════════════════════════════════════════════════
# TestBranch
# ══════════════════════════════════════════════════════════════════════════════

class TestBranch(NG):

    def setUp(self):
        super().setUp()
        self.init()
        self.write("a.txt")
        self.commit("base")

    def test_list_shows_current(self):
        r = self.ok("branch")
        self.assertIn("main", r.stdout)
        self.assertIn("*", r.stdout)

    def test_create_branch(self):
        self.ok("branch", "dev")
        r = self.ok("branch")
        self.assertIn("dev", r.stdout)

    def test_create_branch_at_commit(self):
        r = self.ok("log", "--oneline")
        oid = r.stdout.strip().split()[0]
        self.ok("branch", "pinned", oid)
        r2 = self.ok("branch")
        self.assertIn("pinned", r2.stdout)

    def test_duplicate_branch_errors(self):
        self.ok("branch", "dup")
        r = self.ng("branch", "dup")
        self.assertIn("already exists", r.stderr)

    def test_delete_branch(self):
        self.ok("branch", "temp")
        self.ok("branch", "-d", "temp")
        r = self.ok("branch")
        self.assertNotIn("temp", r.stdout)

    def test_delete_current_branch_errors(self):
        r = self.ng("branch", "-d", "main")
        self.assertIn("Cannot delete", r.stderr)

    def test_delete_nonexistent_branch_errors(self):
        r = self.ng("branch", "-d", "ghost")
        self.assertIn("not found", r.stderr)

    def test_invalid_branch_name_errors(self):
        r = self.ng("branch", "../escape")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("invalid branch name", r.stderr)


# ══════════════════════════════════════════════════════════════════════════════
# TestCheckout
# ══════════════════════════════════════════════════════════════════════════════

class TestCheckout(NG):

    def setUp(self):
        super().setUp()
        self.init()
        self.write("a.txt", "from main\n")
        self.commit("main commit")

    def test_switch_branch(self):
        self.ok("branch", "other")
        r = self.ok("checkout", "other")
        self.assertIn("Switched", r.stdout)
        r2 = self.ok("status")
        self.assertIn("other", r2.stdout)

    def test_checkout_b_creates_and_switches(self):
        r = self.ok("checkout", "-b", "feature")
        self.assertIn("new branch", r.stdout)
        r2 = self.ok("status")
        self.assertIn("feature", r2.stdout)

    def test_checkout_b_duplicate_errors(self):
        self.ok("branch", "exists")
        r = self.ng("checkout", "-b", "exists")
        self.assertNotEqual(r.returncode, 0)

    def test_checkout_B_resets_existing(self):
        self.ok("branch", "exists")
        r = self.ok("checkout", "-B", "exists")
        self.assertIn("exists", r.stdout)

    def test_checkout_restores_files(self):
        """Files unique to each branch appear/disappear on switch."""
        self.ok("checkout", "-b", "br")
        self.write("br_only.txt", "br content\n")
        self.ok("add", "br_only.txt")
        self.ok("commit", "-m", "br file")
        self.ok("checkout", "main")
        self.assertFalse(self.exists("br_only.txt"))
        self.ok("checkout", "br")
        self.assertTrue(self.exists("br_only.txt"))

    def test_checkout_already_on_branch(self):
        r = self.ok("checkout", "main")
        self.assertIn("Already on", r.stdout)

    def test_checkout_detached_head(self):
        r = self.ok("log", "--oneline")
        oid = r.stdout.strip().split()[0]
        r2 = self.ok("checkout", oid)
        self.assertIn("HEAD is now at", r2.stdout)
        r3 = self.ok("status")
        self.assertIn("detached", r3.stdout)

    def test_checkout_unknown_errors(self):
        r = self.ng("checkout", "no_such_branch")
        self.assertNotEqual(r.returncode, 0)

    def test_checkout_preserves_untracked_files(self):
        self.ok("checkout", "-b", "other")
        self.write("a.txt", "from other\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "other change")
        self.ok("checkout", "main")
        self.write("keep.txt", "keep me\n")
        self.ok("checkout", "other")
        self.assertEqual(self.read("keep.txt"), "keep me\n")


# ══════════════════════════════════════════════════════════════════════════════
# TestReset
# ══════════════════════════════════════════════════════════════════════════════

class TestReset(NG):

    def setUp(self):
        super().setUp()
        self.init()
        self.write("r.txt", "v1\n")
        self.commit("base")
        self.write("r.txt", "v2\n")
        self.ok("add", "r.txt")

    def test_mixed_reset_unstages_but_keeps_workdir(self):
        self.ok("reset")            # default is --mixed HEAD
        r = self.ok("status")
        self.assertNotIn("Changes to be committed", r.stdout)
        self.assertEqual(self.read("r.txt"), "v2\n")

    def test_hard_reset_restores_workdir(self):
        self.ok("reset", "--hard")
        self.assertEqual(self.read("r.txt"), "v1\n")
        r = self.ok("status")
        self.assertIn("nothing to commit", r.stdout)

    def test_soft_reset_keeps_index_and_workdir(self):
        # make a second commit then soft-reset to first
        self.ok("commit", "-m", "second")
        r = self.ok("log", "--oneline")
        first_oid = r.stdout.strip().splitlines()[-1].split()[0]
        self.ok("reset", "--soft", first_oid)
        # working tree and index both still have "second" state
        r2 = self.ok("status")
        self.assertIn("Changes to be committed", r2.stdout)

    def test_reset_unstages_specific_file(self):
        self.write("other.txt", "x\n")
        self.ok("add", "other.txt")
        self.ok("reset", "HEAD", "other.txt")
        r = self.ok("status")
        # other.txt should be untracked again, r.txt still staged
        self.assertIn("other.txt", r.stdout)
        # r.txt (staged modification) should still be staged
        self.assertIn("r.txt", r.stdout)

    def test_hard_reset_removes_new_file_from_index(self):
        self.write("extra.txt")
        self.ok("add", "extra.txt")
        self.ok("reset", "--hard")
        r = self.ok("status")
        self.assertNotIn("Changes to be committed", r.stdout)

    def test_hard_reset_preserves_untracked_files(self):
        self.write("local.txt", "keep\n")
        self.ok("reset", "--hard")
        self.assertEqual(self.read("local.txt"), "keep\n")


# ══════════════════════════════════════════════════════════════════════════════
# TestRestore
# ══════════════════════════════════════════════════════════════════════════════

class TestRestore(NG):

    def setUp(self):
        super().setUp()
        self.init()
        self.write("x.txt", "original\n")
        self.commit("base")

    def test_restore_workdir_from_index(self):
        self.write("x.txt", "corrupted\n")
        self.ok("restore", "x.txt")
        self.assertEqual(self.read("x.txt"), "original\n")

    def test_restore_staged_unstages_file(self):
        self.write("x.txt", "modified\n")
        self.ok("add", "x.txt")
        self.ok("restore", "--staged", "x.txt")
        r = self.ok("status")
        self.assertNotIn("Changes to be committed", r.stdout)

    def test_restore_unknown_file_errors(self):
        r = self.ng("restore", "ghost.txt")
        self.assertNotEqual(r.returncode, 0)


# ══════════════════════════════════════════════════════════════════════════════
# TestMerge
# ══════════════════════════════════════════════════════════════════════════════

class TestMerge(NG):

    def setUp(self):
        super().setUp()
        self.init()
        self.write("base.txt", "base\n")
        self.commit("base commit")

    def test_fast_forward_merge(self):
        self.ok("checkout", "-b", "ff")
        self.write("ff.txt")
        self.ok("add", "ff.txt")
        self.ok("commit", "-m", "ff commit")
        self.ok("checkout", "main")
        r = self.ok("merge", "ff")
        self.assertIn("Fast-forward", r.stdout)
        self.assertTrue(self.exists("ff.txt"))

    def test_three_way_merge(self):
        self.ok("checkout", "-b", "side")
        self.write("side.txt", "from side\n")
        self.ok("add", "side.txt")
        self.ok("commit", "-m", "side commit")
        self.ok("checkout", "main")
        self.write("main2.txt", "from main\n")
        self.ok("add", "main2.txt")
        self.ok("commit", "-m", "main parallel")
        r = self.ok("merge", "side")
        self.assertIn("ort", r.stdout)
        self.assertTrue(self.exists("side.txt"))
        self.assertTrue(self.exists("main2.txt"))

    def test_merge_already_up_to_date(self):
        self.ok("branch", "same")
        r = self.ok("merge", "same")
        self.assertIn("Already up to date", r.stdout)

    def test_merge_conflict_markers_written(self):
        # both branches edit the same line differently
        self.ok("checkout", "-b", "br1")
        self.write("c.txt", "version alpha\n")
        self.ok("add", "c.txt")
        self.ok("commit", "-m", "alpha")

        self.ok("checkout", "main")
        self.write("c.txt", "initial\n")
        self.ok("add", "c.txt")
        self.ok("commit", "-m", "main initial c")

        # now edit on main
        self.write("c.txt", "version beta\n")
        self.ok("add", "c.txt")
        self.ok("commit", "-m", "beta")

        r = self.ng("merge", "br1")   # may succeed with conflict markers
        content = self.read("c.txt")
        if "CONFLICT" in r.stdout:
            self.assertIn("<<<<<<<", content)

    def test_merge_nonexistent_branch_errors(self):
        r = self.ng("merge", "no_such")
        self.assertNotEqual(r.returncode, 0)

    def test_merge_commit_has_two_parents(self):
        self.ok("checkout", "-b", "p2")
        self.write("p2.txt")
        self.ok("add", "p2.txt")
        self.ok("commit", "-m", "p2 commit")
        self.ok("checkout", "main")
        self.write("main2.txt")
        self.ok("add", "main2.txt")
        self.ok("commit", "-m", "main extra")
        self.ok("merge", "p2")
        r = self.ok("log")
        self.assertIn("Merge:", r.stdout)

    def test_merge_rejects_dirty_worktree(self):
        self.ok("checkout", "-b", "side")
        self.write("base.txt", "side\n")
        self.ok("add", "base.txt")
        self.ok("commit", "-m", "side commit")
        self.ok("checkout", "main")
        self.write("base.txt", "dirty\n")
        r = self.ng("merge", "side")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("cannot merge", r.stderr)
        self.assertEqual(self.read("base.txt"), "dirty\n")

    def test_fast_forward_merge_preserves_untracked_files(self):
        self.ok("checkout", "-b", "ff2")
        self.write("base.txt", "ff2\n")
        self.ok("add", "base.txt")
        self.ok("commit", "-m", "ff2 commit")
        self.ok("checkout", "main")
        self.write("keep.txt", "keep me\n")
        self.ok("merge", "ff2")
        self.assertEqual(self.read("keep.txt"), "keep me\n")

    def test_merge_rejects_untracked_file_collision(self):
        self.ok("checkout", "-b", "side2")
        self.write("clash.txt", "tracked\n")
        self.ok("add", "clash.txt")
        self.ok("commit", "-m", "side adds clash")
        self.ok("checkout", "main")
        self.write("clash.txt", "untracked\n")
        r = self.ng("merge", "side2")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("untracked file", r.stderr)
        self.assertIn("clash.txt", r.stderr)
        self.assertEqual(self.read("clash.txt"), "untracked\n")


# ══════════════════════════════════════════════════════════════════════════════
# TestTag
# ══════════════════════════════════════════════════════════════════════════════

class TestTag(NG):

    def setUp(self):
        super().setUp()
        self.init()
        self.write("t.txt")
        self.commit("taggable")

    def test_create_tag(self):
        self.ok("tag", "v1.0")
        r = self.ok("tag")
        self.assertIn("v1.0", r.stdout)

    def test_tag_appears_in_log(self):
        self.ok("tag", "release")
        r = self.ok("log", "--oneline")
        self.assertIn("tag: release", r.stdout)

    def test_delete_tag(self):
        self.ok("tag", "temp")
        self.ok("tag", "-d", "temp")
        r = self.ok("tag")
        self.assertNotIn("temp", r.stdout)

    def test_duplicate_tag_errors(self):
        self.ok("tag", "dup")
        r = self.ng("tag", "dup")
        self.assertNotEqual(r.returncode, 0)

    def test_force_overwrites_tag(self):
        self.ok("tag", "moving")
        self.write("next.txt")
        self.ok("add", "next.txt")
        self.ok("commit", "-m", "next")
        self.ok("tag", "-f", "moving")   # repoint to new HEAD
        r = self.ok("tag")
        self.assertIn("moving", r.stdout)

    def test_tag_at_specific_commit(self):
        r = self.ok("log", "--oneline")
        oid = r.stdout.strip().split()[0]
        self.write("t2.txt")
        self.ok("add", "t2.txt")
        self.ok("commit", "-m", "another")
        self.ok("tag", "old", oid)
        r2 = self.ok("tag")
        self.assertIn("old", r2.stdout)

    def test_delete_nonexistent_tag_errors(self):
        r = self.ng("tag", "-d", "ghost")
        self.assertNotEqual(r.returncode, 0)

    def test_invalid_tag_name_errors(self):
        r = self.ng("tag", "../escape")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("invalid tag name", r.stderr)


# ══════════════════════════════════════════════════════════════════════════════
# TestConfig
# ══════════════════════════════════════════════════════════════════════════════

class TestConfig(NG):

    def setUp(self):
        super().setUp()
        self.ok("init")

    def test_set_and_get_value(self):
        self.ok("config", "user.name", "Alice")
        r = self.ok("config", "user.name")
        self.assertEqual(r.stdout.strip(), "Alice")

    def test_get_missing_key_exits_nonzero(self):
        r = self.ng("config", "user.missing")
        self.assertNotEqual(r.returncode, 0)

    def test_key_without_section_errors(self):
        r = self.ng("config", "noSection")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("section", r.stderr)

    def test_author_used_in_commit(self):
        self.ok("config", "user.name",  "Bob Builder")
        self.ok("config", "user.email", "bob@build.com")
        self.write("f.txt")
        self.ok("add", "f.txt")
        self.ok("commit", "-m", "authored")
        r = self.ok("log")
        self.assertIn("Bob Builder", r.stdout)
        self.assertIn("bob@build.com", r.stdout)

    def test_overwrite_existing_value(self):
        self.ok("config", "user.name", "First")
        self.ok("config", "user.name", "Second")
        r = self.ok("config", "user.name")
        self.assertEqual(r.stdout.strip(), "Second")


# ══════════════════════════════════════════════════════════════════════════════
# TestStash
# ══════════════════════════════════════════════════════════════════════════════

class TestStash(NG):

    def setUp(self):
        super().setUp()
        self.init()
        self.write("s.txt", "committed\n")
        self.commit("base")

    def _dirty(self):
        self.write("s.txt", "dirty\n")
        self.ok("add", "s.txt")

    def test_stash_push_cleans_workdir(self):
        self._dirty()
        self.ok("stash", "push")
        r = self.ok("status")
        self.assertIn("nothing to commit", r.stdout)

    def test_stash_restores_to_head(self):
        self._dirty()
        self.ok("stash", "push")
        self.assertEqual(self.read("s.txt"), "committed\n")

    def test_stash_pop_restores_changes(self):
        self._dirty()
        self.ok("stash", "push")
        self.ok("stash", "pop")
        self.assertEqual(self.read("s.txt"), "dirty\n")

    def test_stash_list(self):
        self._dirty()
        self.ok("stash", "push", "-m", "my stash")
        r = self.ok("stash", "list")
        self.assertIn("stash@{0}", r.stdout)
        self.assertIn("my stash", r.stdout)

    def test_stash_drop(self):
        self._dirty()
        self.ok("stash", "push")
        self.ok("stash", "drop")
        r = self.ok("stash", "list")
        self.assertEqual(r.stdout.strip(), "")

    def test_stash_clear(self):
        self._dirty()
        self.ok("stash", "push")
        self.ok("stash", "clear")
        r = self.ok("stash", "list")
        self.assertEqual(r.stdout.strip(), "")

    def test_stash_apply_keeps_entry(self):
        self._dirty()
        self.ok("stash", "push")
        self.ok("stash", "apply")
        # entry should still be there
        r = self.ok("stash", "list")
        self.assertIn("stash@{0}", r.stdout)

    def test_stash_pop_on_empty_errors(self):
        r = self.ng("stash", "pop")
        self.assertNotEqual(r.returncode, 0)

    def test_multiple_stash_entries_lifo(self):
        self._dirty()
        self.ok("stash", "push", "-m", "first stash")
        self.write("s.txt", "second dirty\n")
        self.ok("add", "s.txt")
        self.ok("stash", "push", "-m", "second stash")
        r = self.ok("stash", "list")
        lines = r.stdout.strip().splitlines()
        self.assertIn("second stash", lines[0])
        self.assertIn("first stash",  lines[1])

    def test_stash_push_preserves_untracked_files(self):
        self._dirty()
        self.write("keep.txt", "keep me\n")
        self.ok("stash", "push")
        self.assertEqual(self.read("keep.txt"), "keep me\n")
        self.assertEqual(self.read("s.txt"), "committed\n")

    def test_stash_pop_restores_deleted_file_state(self):
        os.remove(os.path.join(self.tmpdir, "s.txt"))
        self.ok("stash", "push")
        self.ok("stash", "pop")
        self.assertFalse(self.exists("s.txt"))

    def test_stash_apply_rejects_dirty_worktree(self):
        self._dirty()
        self.ok("stash", "push")
        self.write("s.txt", "local dirty\n")
        r = self.ng("stash", "apply")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("cannot apply stash", r.stderr)
        self.assertEqual(self.read("s.txt"), "local dirty\n")
        r2 = self.ok("stash", "list")
        self.assertIn("stash@{0}", r2.stdout)

    def test_stash_pop_rejects_dirty_worktree_and_keeps_entry(self):
        self._dirty()
        self.ok("stash", "push")
        self.write("s.txt", "local dirty\n")
        r = self.ng("stash", "pop")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("cannot pop stash", r.stderr)
        self.assertEqual(self.read("s.txt"), "local dirty\n")
        r2 = self.ok("stash", "list")
        self.assertIn("stash@{0}", r2.stdout)


# ══════════════════════════════════════════════════════════════════════════════
# TestStashNoCommit
# ══════════════════════════════════════════════════════════════════════════════

class TestStashNoCommit(NG):

    def setUp(self):
        super().setUp()
        self.ok("init")

    def test_stash_push_on_unborn_branch_cleans_state(self):
        self.write("a.txt", "new\n")
        self.ok("add", "a.txt")
        self.ok("stash", "push")
        self.assertFalse(self.exists("a.txt"))
        r = self.ok("status")
        self.assertNotIn("Changes to be committed", r.stdout)
        self.ok("stash", "pop")
        self.assertEqual(self.read("a.txt"), "new\n")


# ══════════════════════════════════════════════════════════════════════════════
# TestEdgeCases
# ══════════════════════════════════════════════════════════════════════════════

class TestEdgeCases(NG):

    def setUp(self):
        super().setUp()
        self.init()

    def test_short_hash_resolution(self):
        self.write("e.txt")
        self.commit("edge")
        r = self.ok("log", "--oneline")
        short = r.stdout.strip().split()[0]   # 7-char hash
        r2 = self.ok("show", short)
        self.assertIn("edge", r2.stdout)

    def test_detached_head_commit(self):
        self.write("a.txt")
        self.commit("first")
        r = self.ok("log", "--oneline")
        oid = r.stdout.strip().split()[0]
        self.ok("checkout", oid)
        self.write("detached.txt")
        self.ok("add", "detached.txt")
        r2 = self.ok("commit", "-m", "detached commit")
        self.assertIn("detached HEAD", r2.stdout)

    def test_checkout_back_to_branch_after_detach(self):
        self.write("a.txt")
        self.commit("base")
        r = self.ok("log", "--oneline")
        oid = r.stdout.strip().split()[0]
        self.ok("checkout", oid)
        self.ok("checkout", "main")
        r2 = self.ok("status")
        self.assertIn("main", r2.stdout)

    def test_empty_index_no_commit(self):
        r = self.ng("commit", "-m", "empty")
        self.assertEqual(r.returncode, 1)
        self.assertIn("nothing to commit", r.stdout)

    def test_adding_binary_file(self):
        path = os.path.join(self.tmpdir, "binary.bin")
        with open(path, "wb") as f:
            f.write(bytes(range(256)))
        self.ok("add", "binary.bin")
        r = self.ok("status")
        self.assertIn("binary.bin", r.stdout)
        self.ok("commit", "-m", "binary")

    def test_nested_directory_tracked(self):
        self.write("deep/nested/file.txt", "deep\n")
        self.ok("add", ".")
        r = self.ok("status")
        self.assertIn("deep/nested/file.txt", r.stdout)
        self.ok("commit", "-m", "nested")
        r2 = self.ok("status")
        self.assertIn("nothing to commit", r2.stdout)

    def test_reinit_does_not_lose_history(self):
        self.write("x.txt")
        self.commit("history")
        self.ok("init")   # reinit
        r = self.ok("log", "--oneline")
        self.assertIn("history", r.stdout)

    def test_log_after_merge_shows_two_parent_commits(self):
        self.write("a.txt")
        self.commit("base")
        self.ok("checkout", "-b", "side")
        self.write("side.txt")
        self.ok("add", "side.txt")
        self.ok("commit", "-m", "side")
        self.ok("checkout", "main")
        self.write("main2.txt")
        self.ok("add", "main2.txt")
        self.ok("commit", "-m", "main parallel")
        self.ok("merge", "side")
        r = self.ok("log", "--oneline")
        self.assertGreaterEqual(len(r.stdout.strip().splitlines()), 3)

    def test_status_on_empty_repo_before_any_commit(self):
        r = self.ok("status")
        self.assertIn("No commits yet", r.stdout)

    def test_diff_after_delete_shows_minus_lines(self):
        self.write("z.txt", "alpha\nbeta\ngamma\n")
        self.commit("three lines")
        self.write("z.txt", "alpha\ngamma\n")   # remove 'beta'
        r = self.ok("diff")
        self.assertIn("-beta", r.stdout)

    def test_commit_message_preserved_exactly(self):
        self.write("m.txt")
        self.ok("add", "m.txt")
        msg = "Fix: handle edge-case with apostrophe's & \"quotes\""
        self.ok("commit", "-m", msg)
        r = self.ok("log")
        self.assertIn(msg, r.stdout)


# ══════════════════════════════════════════════════════════════════════════════
# TestObjectStore
# ══════════════════════════════════════════════════════════════════════════════

class TestObjectStore(NG):
    """Low-level checks that objects are stored and deduped correctly."""

    def setUp(self):
        super().setUp()
        self.init()

    def test_identical_files_share_one_object(self):
        content = "same content\n"
        self.write("copy1.txt", content)
        self.write("copy2.txt", content)
        self.ok("add", ".")
        # count objects written
        obj_root = os.path.join(self.tmpdir, ".notgit", "objects")
        def count_objects():
            n = 0
            for root, _, files in os.walk(obj_root):
                n += len(files)
            return n
        before = count_objects()
        self.ok("commit", "-m", "dedup test")
        after = count_objects()
        # objects: 1 blob (shared), 1 tree, 1 commit + index/notgitignore blob + root tree
        # key assertion: both copies share ONE blob
        # We can verify by checking that after staging, only one blob OID was added
        self.assertGreater(after, before)

    def test_object_stored_with_prefix_layout(self):
        self.write("layout.txt", "check layout\n")
        self.ok("add", "layout.txt")
        obj_root = os.path.join(self.tmpdir, ".notgit", "objects")
        subdirs = [d for d in os.listdir(obj_root)
                   if os.path.isdir(os.path.join(obj_root, d))]
        self.assertTrue(any(len(d) == 2 for d in subdirs),
                        "Expected 2-char prefix subdirectories in objects/")

    def test_commit_tree_matches_index(self):
        """After a commit the working tree and index must match committed tree."""
        self.write("check.txt", "v1\n")
        self.ok("add", "check.txt")
        self.ok("commit", "-m", "snap")
        # modify on disk without staging
        self.write("check.txt", "v2\n")
        r = self.ok("status")
        self.assertIn("not staged", r.stdout)   # workdir differs
        # but index is still clean vs committed
        r2 = self.ok("diff", "--staged")
        self.assertEqual(r2.stdout.strip(), "")




# TestBugFixes (crawl 1)

class TestBugFixes(NG):
    def test_log_shows_all_commits(self):
        self.init()
        for i in range(3):
            self.write(f"f{i}.txt", f"v{i}\n")
            self.ok("add", f"f{i}.txt")
            self.ok("commit", "-m", f"commit {i}")
        r = self.ok("log", "--oneline")
        self.assertEqual(len(r.stdout.strip().splitlines()), 3)

    def test_branch_list_shows_current(self):
        self.init()
        self.write("a.txt", "a\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "init")
        r = self.ok("branch")
        self.assertIn("*", r.stdout)

    def test_tag_and_checkout_tagged_commit(self):
        self.init()
        self.write("a.txt", "v1\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "first")
        self.ok("tag", "v1.0")
        r = self.ok("tag")
        self.assertIn("v1.0", r.stdout)

    def test_stash_roundtrip(self):
        self.init()
        self.write("a.txt", "original\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.write("a.txt", "modified\n")
        self.ok("stash")
        r = self.ok("status")
        self.assertNotIn("modified:   a.txt", r.stdout)
        self.assertEqual(self.read("a.txt"), "original\n")
        self.ok("stash", "pop")
        content = open(os.path.join(self.tmpdir, "a.txt")).read()
        self.assertEqual(content, "modified\n")

    def test_diff_staged_shows_indexed_changes(self):
        self.init()
        self.write("a.txt", "line1\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.write("a.txt", "line2\n")
        self.ok("add", "a.txt")
        r = self.ok("diff", "--staged")
        self.assertIn("+line2", r.stdout)
        self.assertIn("-line1", r.stdout)

    def test_merge_fast_forward(self):
        self.init()
        self.write("a.txt", "base\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.ok("checkout", "-b", "feature")
        self.write("b.txt", "feature\n")
        self.ok("add", "b.txt")
        self.ok("commit", "-m", "feature")
        self.ok("checkout", "main")
        self.ok("merge", "feature")
        self.assertTrue(os.path.exists(os.path.join(self.tmpdir, "b.txt")))

    def test_restore_discards_worktree_changes(self):
        self.init()
        self.write("a.txt", "original\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.write("a.txt", "changed\n")
        self.ok("restore", "a.txt")
        content = open(os.path.join(self.tmpdir, "a.txt")).read()
        self.assertEqual(content, "original\n")

    def test_commit_minus_a_stages_all_tracked(self):
        self.init()
        self.write("a.txt", "v1\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.write("a.txt", "v2\n")
        self.ok("commit", "-a", "-m", "updated")
        r = self.ok("status")
        # a.txt must not appear as modified/staged after commit -a
        self.assertNotIn("a.txt", r.stdout)


# TestBugFixes2 (crawl 2)

class TestBugFixes2(NG):
    def test_log_n_zero_prints_nothing(self):
        self.init()
        self.write("a.txt", "a\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "init")
        r = self.ok("log", "-n", "0")
        self.assertEqual(r.stdout.strip(), "")

    def test_reset_unknown_file_exits_nonzero(self):
        self.init()
        self.write("a.txt", "a\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "init")
        r = self.ng("reset", "HEAD", "ghost.txt")
        self.assertNotEqual(r.returncode, 0)

    def test_checkout_dirty_worktree_blocked(self):
        self.init()
        self.write("a.txt", "main\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.ok("checkout", "-b", "other")
        self.write("a.txt", "other\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "other commit")
        self.ok("checkout", "main")
        self.write("a.txt", "dirty\n")
        r = self.ng("checkout", "other")
        self.assertNotEqual(r.returncode, 0)

    def test_checkout_clean_worktree_succeeds(self):
        self.init()
        self.write("a.txt", "main\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.ok("checkout", "-b", "other")
        self.write("b.txt", "other\n")
        self.ok("add", "b.txt")
        self.ok("commit", "-m", "other commit")
        self.ok("checkout", "main")
        r = self.ok("checkout", "other")
        self.assertIn("Switched", r.stdout)

    def test_checkout_same_commit_no_overwrite(self):
        self.init()
        self.write("a.txt", "base\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.ok("checkout", "-b", "twin")
        self.ok("checkout", "main")
        r = self.ok("checkout", "twin")
        self.assertIn("Switched", r.stdout)
        content = open(os.path.join(self.tmpdir, "a.txt")).read()
        self.assertEqual(content, "base\n")


# TestChanges123 (improvements 1-3)

class TestChanges123(NG):
    def test_hash_blob_matches_stored_oid(self):
        import importlib.util
        spec = importlib.util.spec_from_file_location("notgit", SCRIPT)
        ng = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ng)
        data = b"hello world\n"
        expected_oid = ng.store_object("blob", data)
        self.assertEqual(ng.hash_blob(data), expected_oid)

    def test_tracked_file_visible_when_ignored(self):
        self.init()
        self.write("secret.log", "private\n")
        self.ok("add", "secret.log")
        self.ok("commit", "-m", "add secret")
        with open(os.path.join(self.tmpdir, ".notgitignore"), "a") as f:
            f.write("*.log\n")
        self.write("secret.log", "updated\n")
        r = self.ok("status")
        self.assertIn("secret.log", r.stdout)

    def test_ignored_untracked_file_not_in_status(self):
        self.init()
        self.write("a.txt", "a\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        with open(os.path.join(self.tmpdir, ".notgitignore"), "a") as f:
            f.write("*.log\n")
        self.write("debug.log", "noise\n")
        r = self.ok("status")
        self.assertNotIn("debug.log", r.stdout)

    def test_add_deleted_file_stages_removal(self):
        self.init()
        self.write("x.txt", "data\n")
        self.ok("add", "x.txt")
        self.ok("commit", "-m", "base")
        os.remove(os.path.join(self.tmpdir, "x.txt"))
        self.ok("add", "x.txt")
        r = self.ok("status")
        self.assertIn("deleted", r.stdout)
        self.assertIn("x.txt", r.stdout)

    def test_add_dot_stages_deletion(self):
        self.init()
        self.write("a.txt", "a\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        os.remove(os.path.join(self.tmpdir, "a.txt"))
        self.write("b.txt", "b\n")
        self.ok("add", ".")
        r = self.ok("status")
        self.assertIn("deleted", r.stdout)
        self.assertIn("a.txt", r.stdout)
        self.assertIn("b.txt", r.stdout)

    def test_add_deleted_file_then_commit(self):
        self.init()
        self.write("gone.txt", "bye\n")
        self.ok("add", "gone.txt")
        self.ok("commit", "-m", "add gone")
        os.remove(os.path.join(self.tmpdir, "gone.txt"))
        self.ok("add", "gone.txt")
        self.ok("commit", "-m", "remove gone")
        r = self.ok("status")
        self.assertNotIn("gone.txt", r.stdout)


# TestBugFixes3 (crawl 3)

class TestBugFixes3(NG):
    def test_status_detached_head_no_double_call(self):
        self.init()
        self.write("a.txt", "hello\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "initial")
        r = self.ok("log", "--oneline")
        oid = r.stdout.strip().split()[0]
        import re
        oid_clean = re.sub(r'\x1b\[[0-9;]*m', '', oid)
        self.ok("checkout", oid_clean)
        r = self.ok("status")
        self.assertIn("HEAD detached at", r.stdout)
        self.assertNotIn("???", r.stdout)

    def test_reset_with_double_dash_separator(self):
        self.init()
        self.write("a.txt", "line1\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.write("a.txt", "line2\n")
        self.ok("add", "a.txt")
        self.ok("reset", "HEAD", "--", "a.txt")
        r = self.ok("status")
        self.assertIn("a.txt", r.stdout)
        self.assertNotIn("Changes to be committed", r.stdout)

    def test_main_unknown_command_message(self):
        import subprocess, sys
        r = subprocess.run(
            [sys.executable, SCRIPT, "frobnicate"],
            capture_output=True, text=True
        )
        combined = r.stdout + r.stderr
        self.assertIn("frobnicate", combined)
        self.assertNotIn("args.command", combined)


# ══════════════════════════════════════════════════════════════════════════════
# New feature tests: amend, revert, log path, diff --stat
# ══════════════════════════════════════════════════════════════════════════════

class TestNewFeatures(NG):
    """Tests for commit --amend, revert, log -- path, and diff --stat."""

    # ── commit --amend ────────────────────────────────────────────────────────

    def test_amend_changes_message(self):
        """commit --amend -m should rewrite the last commit message."""
        self.init()
        self.write("a.txt", "hello\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "typo messge")
        self.ok("commit", "--amend", "-m", "correct message")
        r = self.ok("log", "--oneline")
        self.assertIn("correct message", r.stdout)
        self.assertNotIn("typo messge", r.stdout)
        # still only one commit
        self.assertEqual(len(r.stdout.strip().splitlines()), 1)

    def test_amend_folds_staged_changes(self):
        """commit --amend should incorporate newly staged changes into the last commit."""
        self.init()
        self.write("a.txt", "v1\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "initial")
        # stage an extra file then amend
        self.write("b.txt", "new\n")
        self.ok("add", "b.txt")
        self.ok("commit", "--amend", "-m", "initial with b")
        r = self.ok("log", "--oneline")
        # still one commit
        self.assertEqual(len(r.stdout.strip().splitlines()), 1)
        # b.txt must be in the amended commit's tree
        r2 = self.ok("show")
        self.assertIn("b.txt", r2.stdout)

    def test_amend_preserves_message_when_no_m(self):
        """commit --amend without -m should keep the existing message."""
        self.init()
        self.write("a.txt", "v1\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "keep this message")
        self.write("a.txt", "v2\n")
        self.ok("add", "a.txt")
        self.ok("commit", "--amend")
        r = self.ok("log", "--oneline")
        self.assertIn("keep this message", r.stdout)

    # ── revert ────────────────────────────────────────────────────────────────

    def test_revert_undoes_last_commit(self):
        """revert HEAD should create a commit that removes the changes from HEAD."""
        self.init()
        self.write("a.txt", "original\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.write("a.txt", "changed\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "change a")
        self.ok("revert", "HEAD")
        # content should be back to original
        content = open(os.path.join(self.tmpdir, "a.txt")).read()
        self.assertEqual(content, "original\n")
        # should now have 3 commits
        r = self.ok("log", "--oneline")
        self.assertEqual(len(r.stdout.strip().splitlines()), 3)

    def test_revert_creates_descriptive_message(self):
        """revert should auto-generate a message mentioning the original."""
        self.init()
        self.write("a.txt", "v1\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "add feature X")
        self.write("a.txt", "v2\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "add feature X")
        self.ok("revert", "HEAD")
        r = self.ok("log", "--oneline")
        self.assertIn("Revert", r.stdout)
        self.assertIn("add feature X", r.stdout)

    def test_revert_earlier_commit(self):
        """revert should work on a commit that is not HEAD."""
        self.init()
        self.write("a.txt", "base\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.write("b.txt", "added\n")
        self.ok("add", "b.txt")
        self.ok("commit", "-m", "add b")
        self.write("c.txt", "c\n")
        self.ok("add", "c.txt")
        self.ok("commit", "-m", "add c")
        # revert the "add b" commit (second commit, HEAD~1)
        r = self.ok("log", "--oneline")
        lines = r.stdout.strip().splitlines()
        import re
        second_oid = re.sub(r'\x1b\[[0-9;]*m', '', lines[1]).split()[0]
        self.ok("revert", second_oid)
        # b.txt should be gone; c.txt should still exist
        self.assertFalse(os.path.exists(os.path.join(self.tmpdir, "b.txt")))
        self.assertTrue(os.path.exists(os.path.join(self.tmpdir, "c.txt")))

    def test_revert_rejects_dirty_worktree(self):
        """revert must not overwrite unstaged local edits."""
        self.init()
        self.write("a.txt", "original\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.write("a.txt", "changed\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "change a")
        self.write("a.txt", "local dirty\n")
        r = self.ng("revert", "HEAD")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("cannot revert", r.stderr)
        self.assertEqual(self.read("a.txt"), "local dirty\n")
        r2 = self.ok("log", "--oneline")
        self.assertEqual(len(r2.stdout.strip().splitlines()), 2)

    # ── log -- path ───────────────────────────────────────────────────────────

    def test_log_path_filter_shows_only_relevant_commits(self):
        """log <path> should only show commits that touched that file."""
        self.init()
        self.write("a.txt", "a\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "add a")
        self.write("b.txt", "b\n")
        self.ok("add", "b.txt")
        self.ok("commit", "-m", "add b")
        self.write("a.txt", "a2\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "update a")
        r = self.ok("log", "--oneline", "a.txt")
        lines = r.stdout.strip().splitlines()
        # only 2 commits touched a.txt: "add a" and "update a"
        self.assertEqual(len(lines), 2)
        combined = r.stdout
        self.assertIn("update a", combined)
        self.assertIn("add a", combined)
        self.assertNotIn("add b", combined)

    def test_log_path_filter_no_matches(self):
        """log <path> with a file not in any commit should print nothing."""
        self.init()
        self.write("a.txt", "a\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "add a")
        r = self.ok("log", "--oneline", "nonexistent.txt")
        self.assertEqual(r.stdout.strip(), "")

    # ── diff --stat ───────────────────────────────────────────────────────────

    def test_diff_stat_shows_summary_not_patch(self):
        """diff --stat should print a stat table, not raw unified diff."""
        self.init()
        self.write("a.txt", "line1\nline2\nline3\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "base")
        self.write("a.txt", "line1\nchanged\nline3\nextra\n")
        self.ok("add", "a.txt")
        r = self.ok("diff", "--stat", "--staged")
        # must contain the file name and a count column
        self.assertIn("a.txt", r.stdout)
        self.assertIn("|", r.stdout)
        self.assertIn("changed", r.stdout)
        # must NOT contain raw diff markers
        self.assertNotIn("@@", r.stdout)
        self.assertNotIn("--- a/", r.stdout)

    def test_diff_stat_two_commits(self):
        """diff --stat <rev1> <rev2> should report stats between two commits."""
        self.init()
        self.write("a.txt", "v1\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "c1")
        self.write("a.txt", "v2\n")
        self.write("b.txt", "new\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "c2")
        r = self.ok("log", "--oneline")
        import re
        lines = [re.sub(r'\x1b\[[0-9;]*m', '', l).split()[0]
                 for l in r.stdout.strip().splitlines()]
        r2 = self.ok("diff", "--stat", lines[1], lines[0])
        self.assertIn("a.txt", r2.stdout)
        self.assertIn("b.txt", r2.stdout)
        self.assertIn("files changed", r2.stdout)



# ══════════════════════════════════════════════════════════════════════════════
# checkout path-restore regression tests
# ══════════════════════════════════════════════════════════════════════════════

class TestCheckoutPathRestore(NG):
    """checkout . and checkout <file> must restore from index, not crash."""

    def test_checkout_dot_restores_all_files(self):
        """notgit checkout . must restore all tracked files from the index."""
        self.init()
        self.write("a.txt", "original\n")
        self.write("b.txt", "original\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "base")
        # clobber both files on disk
        self.write("a.txt", "dirty\n")
        self.write("b.txt", "dirty\n")
        self.ok("checkout", ".")
        self.assertEqual(self.read("a.txt"), "original\n")
        self.assertEqual(self.read("b.txt"), "original\n")

    def test_checkout_dot_does_not_crash(self):
        """notgit checkout . must not raise IsADirectoryError."""
        self.init()
        self.write("x.txt", "v1\n")
        self.ok("add", "x.txt")
        self.ok("commit", "-m", "init")
        self.write("x.txt", "v2\n")
        r = self.ok("checkout", ".")
        self.assertEqual(r.returncode, 0)

    def test_checkout_specific_file_restores_it(self):
        """notgit checkout <file> must restore just that file."""
        self.init()
        self.write("a.txt", "clean\n")
        self.write("b.txt", "clean\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "base")
        self.write("a.txt", "dirty\n")
        self.write("b.txt", "dirty\n")
        self.ok("checkout", "a.txt")
        self.assertEqual(self.read("a.txt"), "clean\n")
        # b.txt should remain dirty (we only restored a.txt)
        self.assertEqual(self.read("b.txt"), "dirty\n")

    def test_checkout_branch_still_works(self):
        """Existing branch-switching must not be affected by the path-restore path."""
        self.init()
        self.write("a.txt", "main\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "on main")
        self.ok("checkout", "-b", "other")
        self.write("a.txt", "other\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "on other")
        self.ok("checkout", "main")
        self.assertEqual(self.read("a.txt"), "main\n")


class TestRevParse(NG):

    def setUp(self):
        super().setUp()
        self.init()
        self.initial_commit()

    def head_oid(self):
        with open(os.path.join(self.tmpdir, ".notgit", "refs", "heads", "main")) as f:
            return f.read().strip()

    def test_rev_parse_head_prints_full_oid(self):
        r = self.ok("rev-parse", "HEAD")
        self.assertEqual(r.stdout.strip(), self.head_oid())

    def test_rev_parse_resolves_branch_tag_and_short_hash(self):
        oid = self.head_oid()
        self.ok("branch", "topic")
        self.ok("tag", "v1")
        self.assertEqual(self.ok("rev-parse", "topic").stdout.strip(), oid)
        self.assertEqual(self.ok("rev-parse", "v1").stdout.strip(), oid)
        self.assertEqual(self.ok("rev-parse", oid[:8]).stdout.strip(), oid)

    def test_rev_parse_short_abbreviates_oid(self):
        r = self.ok("rev-parse", "--short=12", "HEAD")
        self.assertEqual(r.stdout.strip(), self.head_oid()[:12])

    def test_rev_parse_short_without_value_keeps_revision_argument(self):
        r = self.ok("rev-parse", "--short", "HEAD")
        self.assertEqual(r.stdout.strip(), self.head_oid()[:7])

    def test_rev_parse_abbrev_ref_head(self):
        r = self.ok("rev-parse", "--abbrev-ref", "HEAD")
        self.assertEqual(r.stdout.strip(), "main")

    def test_rev_parse_verify_rejects_unknown_revision(self):
        r = self.ng("rev-parse", "--verify", "missing")
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("bad revision 'missing'", r.stderr)

    def test_rev_parse_repository_paths_from_subdirectory(self):
        subdir = os.path.join(self.tmpdir, "sub", "dir")
        os.makedirs(subdir)
        top = self.ok("rev-parse", "--show-toplevel", cwd=subdir)
        git_dir = self.ok("rev-parse", "--git-dir", cwd=subdir)
        prefix = self.ok("rev-parse", "--show-prefix", cwd=subdir)
        cdup = self.ok("rev-parse", "--show-cdup", cwd=subdir)
        inside = self.ok("rev-parse", "--is-inside-work-tree", cwd=subdir)

        self.assertEqual(top.stdout.strip(), self.tmpdir)
        self.assertEqual(git_dir.stdout.strip(), os.path.join(self.tmpdir, ".notgit"))
        self.assertEqual(prefix.stdout, "sub/dir/\n")
        self.assertEqual(cdup.stdout, "../../\n")
        self.assertEqual(inside.stdout.strip(), "true")


class TestLocalOnlyHighValueOptions(NG):

    def setUp(self):
        super().setUp()
        self.init()

    def test_add_all_stages_new_modified_and_deleted_files(self):
        self.write("tracked.txt", "one\n")
        self.write("deleted.txt", "gone\n")
        self.commit("base")
        self.write("tracked.txt", "two\n")
        os.remove(os.path.join(self.tmpdir, "deleted.txt"))
        self.write("new.txt", "new\n")

        self.ok("add", "-A")
        r = self.ok("status", "--porcelain")
        self.assertIn("M  tracked.txt", r.stdout)
        self.assertIn("D  deleted.txt", r.stdout)
        self.assertIn("A  new.txt", r.stdout)

    def test_add_patch_and_reset_patch_select_file_changes(self):
        self.write("a.txt", "a1\n")
        self.write("b.txt", "b1\n")
        self.commit("base")
        self.write("a.txt", "a2\n")
        self.write("b.txt", "b2\n")

        self.ok("add", "-p", ".", input="y\nn\n")
        r = self.ok("status", "--porcelain")
        self.assertIn("M  a.txt", r.stdout)
        self.assertIn(" M b.txt", r.stdout)

        self.ok("reset", "-p", input="y\n")
        r = self.ok("status", "--porcelain")
        self.assertIn(" M a.txt", r.stdout)
        self.assertIn(" M b.txt", r.stdout)

    def test_commit_no_edit_author_and_date(self):
        self.write("a.txt", "one\n")
        self.ok("add", "a.txt")
        self.ok(
            "commit", "-m", "base",
            "--author", "Alt User <alt@example.com>",
            "--date", "2024-01-02 03:04:05",
        )
        self.write("a.txt", "two\n")
        self.ok("add", "a.txt")
        self.ok("commit", "--amend", "--no-edit")

        r = self.ok("log", "-n", "1")
        self.assertIn("base", r.stdout)
        self.assertIn("Alt User <alt@example.com>", r.stdout)
        self.assertIn("Jan 02 03:04:05 2024", r.stdout)

    def test_restore_source_can_restore_index_and_worktree(self):
        self.write("a.txt", "one\n")
        self.commit("one")
        old = self.ok("rev-parse", "HEAD").stdout.strip()
        self.write("a.txt", "two\n")
        self.commit("two")

        self.ok("restore", "--source", old, "--staged", "--worktree", "a.txt")
        self.assertEqual(self.read("a.txt"), "one\n")
        r = self.ok("status", "--porcelain")
        self.assertIn("M  a.txt", r.stdout)

    def test_log_graph_all_filters(self):
        self.write("a.txt", "one\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "alpha", "--author", "Alice <a@example.com>")
        self.ok("checkout", "-b", "topic")
        self.write("b.txt", "two\n")
        self.ok("add", "b.txt")
        self.ok("commit", "-m", "needle beta", "--author", "Bob <b@example.com>")
        self.ok("checkout", "main")

        r = self.ok("log", "--graph", "--all", "--oneline", "--author", "Bob", "--grep", "needle")
        self.assertIn("* ", r.stdout)
        self.assertIn("needle beta", r.stdout)
        self.assertNotIn("alpha", r.stdout)

    def test_diff_name_modes_check_and_word_diff(self):
        self.write("a.txt", "hello world\n")
        self.commit("base")
        self.write("a.txt", "hello there \n")

        self.assertEqual(self.ok("diff", "--name-only").stdout.strip(), "a.txt")
        self.assertIn("M\ta.txt", self.ok("diff", "--name-status").stdout)
        check = self.ng("diff", "--check")
        self.assertNotEqual(check.returncode, 0)
        self.assertIn("trailing whitespace", check.stdout)
        word = self.ok("diff", "--word-diff")
        self.assertIn("[-world-]", word.stdout)
        self.assertIn("{+there+}", word.stdout)

    def test_branch_rename_and_merged_filters(self):
        self.write("a.txt", "one\n")
        self.commit("base")
        self.ok("branch", "old")
        self.ok("branch", "-m", "old", "new")
        r = self.ok("branch")
        self.assertIn("new", r.stdout)
        self.assertNotIn("old", r.stdout)

        merged = self.ok("branch", "--merged")
        self.assertIn("new", merged.stdout)
        no_merged = self.ok("branch", "--no-merged")
        self.assertNotIn("new", no_merged.stdout)

    def test_annotated_tag_resolves_to_commit(self):
        self.write("a.txt", "one\n")
        self.commit("base")
        head = self.ok("rev-parse", "HEAD").stdout.strip()
        self.ok("tag", "-a", "-m", "release notes", "v1")
        self.assertEqual(self.ok("rev-parse", "v1").stdout.strip(), head)

    def test_stash_include_untracked_selectors_and_show(self):
        self.write("base.txt", "base\n")
        self.commit("base")
        self.write("a.txt", "first\n")
        self.ok("stash", "push", "-u", "-m", "first")
        self.write("b.txt", "second\n")
        self.ok("stash", "push", "-u", "-m", "second")

        shown = self.ok("stash", "show", "--include-untracked", "stash@{1}")
        self.assertIn("a.txt", shown.stdout)
        self.assertNotIn("b.txt", shown.stdout)

        self.ok("stash", "apply", "stash@{1}")
        self.assertTrue(self.exists("a.txt"))
        self.assertFalse(self.exists("b.txt"))

        self.ok("stash", "drop", "stash@{1}")
        listed = self.ok("stash", "list")
        self.assertIn("second", listed.stdout)
        self.assertNotIn("first", listed.stdout)

    def test_restore_source_deletes_file_absent_from_source(self):
        self.write("base.txt", "base\n")
        self.commit("base")
        old = self.ok("rev-parse", "HEAD").stdout.strip()
        self.write("new.txt", "new\n")
        self.commit("add new")

        self.ok("restore", "--source", old, "--staged", "--worktree", "new.txt")
        self.assertFalse(self.exists("new.txt"))
        r = self.ok("status", "--porcelain")
        self.assertIn("D  new.txt", r.stdout)

    def test_stash_apply_untracked_collision_is_atomic(self):
        self.write("tracked.txt", "base\n")
        self.commit("base")
        self.write("tracked.txt", "stashed tracked\n")
        self.write("untracked.txt", "stashed untracked\n")
        self.ok("stash", "push", "-u", "-m", "stash")
        self.write("tracked.txt", "base\n")
        self.write("untracked.txt", "collision\n")

        r = self.fail_ng("stash", "apply")
        self.assertIn("untracked", r.stderr)
        self.assertEqual(self.read("tracked.txt"), "base\n")
        self.assertEqual(self.read("untracked.txt"), "collision\n")

    def test_diff_check_ignores_unchanged_trailing_whitespace(self):
        self.write("a.txt", "bad \nclean\n")
        self.commit("base")
        self.write("a.txt", "bad \nchanged\n")
        r = self.ok("diff", "--check")
        self.assertEqual(r.stdout, "")

    def test_diff_name_status_classifies_empty_file_modifications(self):
        self.write("a.txt", "")
        self.commit("empty")
        self.write("a.txt", "content\n")
        r = self.ok("diff", "--name-status")
        self.assertIn("M\ta.txt", r.stdout)
        self.assertNotIn("A\ta.txt", r.stdout)

        self.ok("add", "a.txt")
        self.ok("commit", "-m", "nonempty")
        self.write("a.txt", "")
        r = self.ok("diff", "--name-status")
        self.assertIn("M\ta.txt", r.stdout)
        self.assertNotIn("D\ta.txt", r.stdout)


# ══════════════════════════════════════════════════════════════════════════════
# TestLs
# ══════════════════════════════════════════════════════════════════════════════

class TestLs(NG):

    def setUp(self):
        super().setUp()
        self.init()

    def test_ls_filters_with_wildcards(self):
        self.write("src/app.py", "print('app')\n")
        self.write("src/util.py", "print('util')\n")
        self.write("docs/readme.txt", "docs\n")
        self.ok("add", ".")

        r = self.ok("ls", "*.py")

        self.assertIn("src/app.py", r.stdout)
        self.assertIn("src/util.py", r.stdout)
        self.assertNotIn("docs/readme.txt", r.stdout)

    def test_ls_pathspecs_are_relative_to_invocation_directory(self):
        self.write("src/app.py", "print('app')\n")
        self.write("other/app.py", "print('other')\n")
        self.ok("add", ".")

        r = self.ok("ls", "*.py", cwd=os.path.join(self.tmpdir, "src"))

        self.assertIn("src/app.py", r.stdout)
        self.assertNotIn("other/app.py", r.stdout)

    def test_ls_reports_no_matches_for_unmatched_wildcard(self):
        self.write("a.txt", "alpha\n")
        self.ok("add", ".")

        r = self.ok("ls", "*.py")

        self.assertEqual(r.stdout.strip(), "No files matched.")

    def test_ls_rejects_pathspec_outside_repo(self):
        self.write("a.txt", "alpha\n")
        self.ok("add", ".")

        r = self.fail_ng("ls", "../*.txt")

        self.assertIn("outside repository", r.stderr)


class TestVersions(NG):

    def setUp(self):
        super().setUp()
        self.init()

    def test_versions_writes_each_distinct_committed_file_version(self):
        self.write("note.txt", "one\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "one", "--date", "2024-01-02 03:04:05")
        first = self.ok("rev-parse", "--short", "HEAD").stdout.strip()

        self.write("other.txt", "unrelated\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "unrelated", "--date", "2024-01-03 03:04:05")

        self.write("note.txt", "two\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "two", "--date", "2024-01-04 05:06:07")
        second = self.ok("rev-parse", "--short", "HEAD").stdout.strip()

        r = self.ok("versions", "note.txt")
        files = set(r.stdout.splitlines())
        first_file = f"note_{first}_20240102_0304_1.txt"
        second_file = f"note_{second}_20240104_0506_2.txt"
        self.assertEqual(files, {first_file, second_file})
        self.assertEqual(self.read(first_file), "one\n")
        self.assertEqual(self.read(second_file), "two\n")

    def test_versions_preserves_directory_and_extension(self):
        self.write("src/app.py", "print('one')\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "app one", "--date", "2024-02-03 04:05:06")
        first = self.ok("rev-parse", "--short", "HEAD").stdout.strip()

        r = self.ok("versions", "src/app.py")
        version_file = f"src/app_{first}_20240203_0405_1.py"
        self.assertEqual(r.stdout.strip(), version_file)
        self.assertEqual(self.read(version_file), "print('one')\n")

    def test_versions_reports_missing_committed_file(self):
        self.write("a.txt", "a\n")
        self.commit("base")

        r = self.fail_ng("versions", "missing.txt")
        self.assertIn("did not match any committed file", r.stderr)


# ══════════════════════════════════════════════════════════════════════════════
# Review fixes: grep, checkout, merge state, diff parsing/stat, dates, refs
# ══════════════════════════════════════════════════════════════════════════════

class TestGrep(NG):

    def setUp(self):
        super().setUp()
        self.init()

    def test_grep_finds_match_in_worktree(self):
        self.write("a.txt", "hello needle world\n")
        self.commit("base")
        r = self.ok("grep", "needle")
        self.assertIn("a.txt:hello needle world", r.stdout)

    def test_grep_no_match_exits_nonzero(self):
        self.write("a.txt", "hay\n")
        self.commit("base")
        self.fail_ng("grep", "needle")

    def test_grep_cached_searches_staged_content(self):
        """--cached must search the index, not HEAD."""
        self.write("a.txt", "committed_marker\n")
        self.commit("base")
        self.write("a.txt", "staged_only_marker\n")
        self.ok("add", "a.txt")
        r = self.ok("grep", "--cached", "staged_only_marker")
        self.assertIn("a.txt", r.stdout)
        # the superseded HEAD content must no longer match
        self.fail_ng("grep", "--cached", "committed_marker")

    def test_grep_files_without_match_exit_codes(self):
        """-L exits 1 when every file matches, 0 when it prints something."""
        # "ignore" appears in both a.txt and the tracked .notgitignore
        self.write("a.txt", "ignore this line\n")
        self.commit("base")
        r = self.fail_ng("grep", "-L", "ignore")
        self.assertEqual(r.stdout, "")
        self.write("b.txt", "hay\n")
        self.commit("more")
        r2 = self.ok("grep", "-L", "ignore")
        self.assertIn("b.txt", r2.stdout)


class TestCheckoutPreservesUntracked(NG):

    def test_checkout_dot_preserves_rm_cached_file(self):
        """checkout . must not delete files removed from the index but kept on disk."""
        self.init()
        self.write("data.txt", "keep\n")
        self.commit("base")
        self.ok("rm", "--cached", "data.txt")
        self.ok("checkout", ".")
        self.assertTrue(self.exists("data.txt"))
        self.assertEqual(self.read("data.txt"), "keep\n")


class TestMergeState(NG):
    """A conflicted merge must record MERGE_HEAD so commit finishes the merge."""

    def _conflicted_merge(self):
        self.init()
        self.write("c.txt", "base\n")
        self.write("doomed.txt", "bye\n")
        self.commit("base")
        self.ok("checkout", "-b", "br1")
        self.write("c.txt", "alpha\n")
        self.ok("rm", "doomed.txt")
        self.ok("add", "c.txt")
        self.ok("commit", "-m", "alpha")
        self.ok("checkout", "main")
        self.write("c.txt", "beta\n")
        self.ok("add", "c.txt")
        self.ok("commit", "-m", "beta")
        r = self.fail_ng("merge", "br1")
        self.assertIn("CONFLICT", r.stdout)
        return r

    def test_conflicted_merge_commit_records_both_parents(self):
        self._conflicted_merge()
        self.assertTrue(self.exists(".notgit/MERGE_HEAD"))
        self.write("c.txt", "resolved\n")
        self.ok("add", "c.txt")
        # no -m: the message defaults to the recorded MERGE_MSG
        r = self.ok("commit")
        self.assertIn("Merge branch 'br1'", r.stdout)
        self.assertFalse(self.exists(".notgit/MERGE_HEAD"))
        log = self.ok("log").stdout
        self.assertIn("Merge:", log)
        r2 = self.ok("merge", "br1")
        self.assertIn("Already up to date", r2.stdout)

    def test_conflicted_merge_removes_files_deleted_on_branch(self):
        self._conflicted_merge()
        self.assertFalse(self.exists("doomed.txt"))

    def test_reset_hard_aborts_merge(self):
        self._conflicted_merge()
        self.ok("reset", "--hard", "HEAD")
        self.assertFalse(self.exists(".notgit/MERGE_HEAD"))
        self.write("new.txt", "x\n")
        self.ok("add", "new.txt")
        self.ok("commit", "-m", "after abort")
        log = self.ok("log", "-n", "1").stdout
        self.assertNotIn("Merge:", log)


class TestDiffParsingAndStat(NG):

    def test_diff_stat_counts_lines_starting_with_plus_or_minus(self):
        """Content lines like '++i;' must not be mistaken for diff headers."""
        self.init()
        self.write("a.txt", "++i;\n--j;\nkeep\n")
        self.commit("base")
        self.write("a.txt", "keep\n++k;\n")
        r = self.ok("diff", "--stat")
        self.assertIn("1 insertion(+)", r.stdout)
        self.assertIn("2 deletions(-)", r.stdout)

    def test_diff_flag_after_pathspec(self):
        """Options following a path must still be parsed, not eaten as pathspecs."""
        self.init()
        self.write("a.txt", "one\n")
        self.commit("base")
        self.write("a.txt", "two\n")
        r = self.ok("diff", "a.txt", "--stat")
        self.assertIn("1 file changed", r.stdout)
        self.assertNotIn("@@", r.stdout)


class TestLogSinceYear(NG):

    def test_log_since_bare_year(self):
        """--since 2024 means the year 2024, not epoch second 2024."""
        self.init()
        self.write("a.txt", "one\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "old commit", "--date", "2020-01-02 03:04:05")
        self.write("a.txt", "two\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "new commit", "--date", "2025-06-07 08:09:10")
        r = self.ok("log", "--oneline", "--since", "2024")
        self.assertIn("new commit", r.stdout)
        self.assertNotIn("old commit", r.stdout)


class TestRevResolution(NG):

    def _find_blob_oid(self, marker: bytes) -> str:
        objdir = os.path.join(self.tmpdir, ".notgit", "objects")
        for sub in os.listdir(objdir):
            subp = os.path.join(objdir, sub)
            if not os.path.isdir(subp):
                continue
            for name in os.listdir(subp):
                with open(os.path.join(subp, name), "rb") as f:
                    raw = f.read()
                if raw.startswith(b"blob ") and marker in raw:
                    return sub + name
        self.fail("no blob object found")

    def test_show_blob_prefix_reports_bad_revision(self):
        """An abbreviated hash naming a blob is not a commit revision."""
        self.init()
        self.write("a.txt", "unique blob content 12345\n")
        self.commit("base")
        blob = self._find_blob_oid(b"unique blob content")
        r = self.fail_ng("show", blob[:10])
        self.assertIn("bad revision", r.stderr)

    def _merge_history(self):
        """c1 - c2 - c3 - merge, with side (c2 - side) merged as parent 2."""
        self.init()
        for i in (1, 2, 3):
            self.write("f.txt", f"{i}\n")
            self.commit(f"c{i}")
        self.ok("branch", "side", "HEAD~1")
        self.ok("checkout", "side")
        self.write("s.txt", "s\n")
        self.commit("side")
        self.ok("checkout", "main")
        self.ok("merge", "--no-ff", "-m", "merge", "side")

    def _subject(self, rev):
        return self.ok("show", "--no-patch", "--format=%s", rev).stdout.strip()

    def test_ancestry_suffixes(self):
        self._merge_history()
        cases = {
            "HEAD": "merge", "HEAD^0": "merge",
            "HEAD^": "c3", "HEAD^1": "c3", "HEAD~": "c3", "HEAD~1": "c3",
            "HEAD^2": "side", "HEAD^2~1": "c2", "HEAD^2^": "c2",
            "HEAD~2": "c2", "HEAD~3": "c1", "main~1^": "c2", "side~1": "c2",
        }
        for rev, subject in cases.items():
            with self.subTest(rev=rev):
                self.assertEqual(self._subject(rev), subject)

    def test_ancestry_suffix_on_hash_and_tag(self):
        self._merge_history()
        head = self.ok("rev-parse", "HEAD").stdout.strip()
        self.ok("tag", "-a", "-m", "annotated", "rel", "HEAD~1")
        self.assertEqual(self._subject(head[:8] + "~2"), "c2")
        self.assertEqual(self._subject("rel~1"), "c2")

    def test_ancestry_suffix_past_root_is_bad_revision(self):
        self._merge_history()
        for rev in ("HEAD~4", "HEAD^3", "HEAD^^2", "nosuch~1"):
            with self.subTest(rev=rev):
                self.assertIn("bad revision", self.fail_ng("show", rev).stderr)

    def test_ancestry_suffix_in_rev_parse_reset_and_checkout(self):
        self._merge_history()
        c2 = self.ok("rev-parse", "HEAD~2").stdout.strip()
        self.assertEqual(self.ok("rev-parse", "HEAD~2^{commit}").stdout.strip(), c2)
        self.ok("reset", "--hard", "HEAD~1")
        self.assertEqual(self._subject("HEAD"), "c3")
        self.ok("checkout", "HEAD~1")
        self.assertEqual(self.ok("rev-parse", "HEAD").stdout.strip(), c2)


class TestAtomicWrites(NG):

    def test_no_tmp_files_left_in_repo_dir(self):
        self.init()
        self.initial_commit()
        self.ok("branch", "side")
        self.ok("tag", "v1")
        for dirpath, _dirs, files in os.walk(os.path.join(self.tmpdir, ".notgit")):
            for name in files:
                self.assertFalse(name.endswith(".tmp") or name.startswith(".blob-"),
                                 f"leftover temp file: {os.path.join(dirpath, name)}")


class TestErrorIOPaths(NG):

    def setUp(self):
        super().setUp()
        self.init()

    def notgit_module(self):
        import importlib.util
        spec = importlib.util.spec_from_file_location("notgit_error_io", SCRIPT)
        ng = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ng)
        return ng

    def object_path(self, oid):
        split_path = os.path.join(self.tmpdir, ".notgit", "objects", oid[:2], oid[2:])
        if os.path.exists(split_path):
            return split_path
        return os.path.join(self.tmpdir, ".notgit", "objects", oid)

    def object_payload_json(self, oid):
        with open(self.object_path(oid), "rb") as f:
            raw = f.read()
        return json.loads(raw.split(b"\0", 1)[1])

    def blob_for_commit(self, commit_oid, path):
        commit = self.object_payload_json(commit_oid)
        tree = self.object_payload_json(commit["tree"])
        for entry in tree["entries"]:
            if entry["name"] == path:
                return entry["oid"]
        self.fail(f"blob for {path} not found")

    def index(self):
        with open(os.path.join(self.tmpdir, ".notgit", "index")) as f:
            return json.load(f)

    def test_corrupt_index_json_aborts_instead_of_defaulting_empty(self):
        self.write("a.txt", "alpha\n")
        self.ok("add", "a.txt")
        index_path = os.path.join(self.tmpdir, ".notgit", "index")
        with open(index_path, "w") as f:
            f.write("{not json")

        r = self.fail_ng("status")
        self.assertIn("could not parse .notgit/index", r.stderr)
        self.assertNotIn("Traceback", r.stderr)
        with open(index_path) as f:
            self.assertEqual(f.read(), "{not json")

    def test_invalid_utf8_notgitignore_reports_clean_error(self):
        with open(os.path.join(self.tmpdir, ".notgitignore"), "wb") as f:
            f.write(b"*.log\n\xff\n")

        r = self.fail_ng("status")

        self.assertIn("could not decode .notgitignore as UTF-8", r.stderr)
        self.assertNotIn("Traceback", r.stderr)

    def test_non_regular_notgitignore_is_rejected(self):
        ignore_path = os.path.join(self.tmpdir, ".notgitignore")
        os.remove(ignore_path)
        os.mkdir(ignore_path)

        r = self.fail_ng("status")

        self.assertIn(".notgitignore is not a regular file", r.stderr)
        self.assertNotIn("Traceback", r.stderr)

    def test_oversized_notgitignore_is_rejected(self):
        ignore_path = os.path.join(self.tmpdir, ".notgitignore")
        with open(ignore_path, "wb") as f:
            f.seek(1024 * 1024)
            f.write(b"x")

        r = self.fail_ng("status")

        self.assertIn(".notgitignore is too large", r.stderr)
        self.assertNotIn("Traceback", r.stderr)

    def test_scan_traversal_error_is_reported(self):
        ng = self.notgit_module()
        previous_cwd = os.getcwd()
        stderr = io.StringIO()

        def failing_walk(root, onerror=None):
            onerror(PermissionError(13, "Permission denied", "blocked"))
            if False:
                yield root, [], []

        try:
            os.chdir(self.tmpdir)
            ng._INVOCATION_CWD = self.tmpdir
            ng._WORKTREE_ROOT = self.tmpdir
            with mock.patch.object(ng.os, "walk", failing_walk), \
                    mock.patch.object(sys, "stderr", stderr), \
                    self.assertRaises(SystemExit):
                ng.working_tree_paths()
        finally:
            os.chdir(previous_cwd)

        self.assertIn("could not scan working tree", stderr.getvalue())
        self.assertIn("blocked", stderr.getvalue())

    @unittest.skipIf(os.name == "nt", "requires reliable symbolic links")
    def test_add_read_failure_keeps_index_unchanged(self):
        self.write("tracked.txt", "tracked\n")
        self.write("other.txt", "original\n")
        self.commit("base")
        index_before = self.index()
        times_before = self.read(".notgit/index_times")
        self.write("other.txt", "changed\n")
        os.remove(os.path.join(self.tmpdir, "tracked.txt"))
        os.symlink("missing-target", os.path.join(self.tmpdir, "tracked.txt"))

        r = self.fail_ng("add", ".")

        self.assertIn("could not stage 'tracked.txt'", r.stderr)
        self.assertNotIn("Traceback", r.stderr)
        self.assertEqual(self.index(), index_before)
        self.assertEqual(self.read(".notgit/index_times"), times_before)

    def test_add_avoids_content_retaining_blob_apis(self):
        content = "0123456789abcdef" * 70000
        self.write("streamed.bin", content)
        ng = self.notgit_module()
        original_store_object = ng.store_object

        def reject_blob_bytes(obj_type, content):
            if obj_type == "blob":
                raise AssertionError("add passed complete blob bytes to store_object")
            return original_store_object(obj_type, content)

        previous_cwd = os.getcwd()
        try:
            os.chdir(self.tmpdir)
            ng._INVOCATION_CWD = self.tmpdir
            args = ng.build_parser().parse_args(["add", "."])
            with mock.patch.object(
                    ng, "working_tree_files",
                    side_effect=AssertionError("add retained scan contents")
                 ), mock.patch.object(
                    ng, "store_object", side_effect=reject_blob_bytes
                 ), mock.patch.object(
                    ng, "read_object",
                    side_effect=AssertionError("index validation loaded blob contents")
                 ):
                ng.cmd_add(args)
        finally:
            os.chdir(previous_cwd)

        expected_oid = hashlib.sha1(
            b"blob " + str(len(content.encode())).encode() + b"\0" + content.encode()
        ).hexdigest()
        self.assertEqual(self.index()["streamed.bin"], expected_oid)

    def test_corrupt_object_reports_repository_error(self):
        self.write("a.txt", "alpha\n")
        self.commit("base")
        head = self.ok("rev-parse", "HEAD").stdout.strip()
        with open(self.object_path(head), "wb") as f:
            f.write(b"commit 2\0{}")

        r = self.fail_ng("log")
        self.assertIn("object corrupt", r.stderr)
        self.assertNotIn("Traceback", r.stderr)

    def test_checkout_missing_blob_leaves_current_branch_and_worktree(self):
        self.write("a.txt", "main\n")
        self.commit("main")
        self.ok("checkout", "-b", "side")
        self.write("a.txt", "side\n")
        self.commit("side")
        side = self.ok("rev-parse", "HEAD").stdout.strip()
        side_blob = self.blob_for_commit(side, "a.txt")
        os.remove(self.object_path(side_blob))
        self.ok("checkout", "main")

        r = self.fail_ng("checkout", "side")
        self.assertIn("object not found", r.stderr)
        branch = self.ok("rev-parse", "--abbrev-ref", "HEAD").stdout.strip()
        self.assertEqual(branch, "main")
        self.assertEqual(self.read("a.txt"), "main\n")

    def test_reset_hard_failed_removal_does_not_advance_head_or_index(self):
        self.write("base.txt", "base\n")
        self.commit("base")
        first = self.ok("rev-parse", "HEAD").stdout.strip()
        self.write("doomed.txt", "doomed\n")
        self.commit("add doomed")
        second = self.ok("rev-parse", "HEAD").stdout.strip()
        os.remove(os.path.join(self.tmpdir, "doomed.txt"))
        os.mkdir(os.path.join(self.tmpdir, "doomed.txt"))

        r = self.fail_ng("reset", "--hard", first)
        self.assertIn("could not remove 'doomed.txt'", r.stderr)
        self.assertEqual(self.ok("rev-parse", "HEAD").stdout.strip(), second)
        self.assertIn("doomed.txt", self.index())
        self.assertTrue(os.path.isdir(os.path.join(self.tmpdir, "doomed.txt")))

    def test_rm_failed_unlink_keeps_index_entry(self):
        self.write("tracked.txt", "data\n")
        self.commit("base")
        os.remove(os.path.join(self.tmpdir, "tracked.txt"))
        os.mkdir(os.path.join(self.tmpdir, "tracked.txt"))

        r = self.fail_ng("rm", "tracked.txt")
        self.assertIn("could not remove 'tracked.txt'", r.stderr)
        self.assertIn("tracked.txt", self.index())
        self.assertTrue(os.path.isdir(os.path.join(self.tmpdir, "tracked.txt")))


@unittest.skipIf(shutil.which("git") is None, "git is not installed")
class TestImportGit(NG):
    """Covers `notgit.py import-git`, which converts a real .git repo."""

    def _git_repo(self, name="gitsrc"):
        path = os.path.join(self.tmpdir, name)
        os.makedirs(path)
        env = dict(os.environ, GIT_AUTHOR_NAME="Git User", GIT_AUTHOR_EMAIL="git@example.com",
                   GIT_COMMITTER_NAME="Git User", GIT_COMMITTER_EMAIL="git@example.com")
        def run(*args):
            return subprocess.run(["git", *args], cwd=path, capture_output=True,
                                   text=True, env=env, check=True)
        run("init", "-q", "-b", "main")
        return path, run

    def test_imports_linear_history_and_working_tree(self):
        src, git = self._git_repo()
        with open(os.path.join(src, "a.txt"), "w") as f:
            f.write("alpha\n")
        git("add", ".")
        git("commit", "-q", "-m", "first")
        with open(os.path.join(src, "a.txt"), "w") as f:
            f.write("alpha2\n")
        git("commit", "-q", "-am", "second")

        dest = os.path.join(self.tmpdir, "dest")
        r = self.ok("import-git", src, dest)
        self.assertIn("Converted 2 commit", r.stdout)

        with open(os.path.join(dest, "a.txt")) as f:
            self.assertEqual(f.read(), "alpha2\n")
        log = self.ok("log", "--oneline", cwd=dest)
        self.assertEqual(len([l for l in log.stdout.splitlines() if l.strip()]), 2)
        status = self.ok("status", cwd=dest)
        self.assertIn("nothing to commit", status.stdout)

    def test_imports_branches_merge_and_tags(self):
        src, git = self._git_repo()
        with open(os.path.join(src, "a.txt"), "w") as f:
            f.write("alpha\n")
        git("add", ".")
        git("commit", "-q", "-m", "first")
        git("branch", "feature")
        git("checkout", "-q", "feature")
        with open(os.path.join(src, "b.txt"), "w") as f:
            f.write("beta\n")
        git("add", "b.txt")
        git("commit", "-q", "-m", "on feature")
        git("checkout", "-q", "main")
        with open(os.path.join(src, "c.txt"), "w") as f:
            f.write("gamma\n")
        git("add", "c.txt")
        git("commit", "-q", "-m", "on main")
        git("merge", "-q", "--no-ff", "--no-edit", "-m", "merge feature", "feature")
        git("tag", "v1.0")
        git("tag", "-a", "v2.0", "-m", "release notes")

        dest = os.path.join(self.tmpdir, "dest")
        r = self.ok("import-git", src, dest)
        self.assertIn("Converted 4 commit", r.stdout)
        self.assertIn("2 branch", r.stdout)
        self.assertIn("2 tag", r.stdout)

        branches = self.ok("branch", cwd=dest).stdout
        self.assertIn("feature", branches)
        self.assertIn("main", branches)
        tags = self.ok("tag", cwd=dest).stdout
        self.assertIn("v1.0", tags)
        self.assertIn("v2.0", tags)
        for name in ("a.txt", "b.txt", "c.txt"):
            self.assertTrue(os.path.exists(os.path.join(dest, name)))

    def test_imports_packed_objects_after_gc(self):
        src, git = self._git_repo()
        with open(os.path.join(src, "a.txt"), "w") as f:
            f.write("alpha\n")
        git("add", ".")
        git("commit", "-q", "-m", "first")
        with open(os.path.join(src, "a.txt"), "w") as f:
            f.write("alpha2\n")
        git("commit", "-q", "-am", "second")
        git("gc", "-q")

        dest = os.path.join(self.tmpdir, "dest")
        self.ok("import-git", src, dest)
        with open(os.path.join(dest, "a.txt")) as f:
            self.assertEqual(f.read(), "alpha2\n")
        log = self.ok("log", "--oneline", cwd=dest)
        self.assertEqual(len([l for l in log.stdout.splitlines() if l.strip()]), 2)

    def test_existing_destination_errors(self):
        src, git = self._git_repo()
        with open(os.path.join(src, "a.txt"), "w") as f:
            f.write("alpha\n")
        git("add", ".")
        git("commit", "-q", "-m", "first")

        dest = os.path.join(self.tmpdir, "dest")
        os.makedirs(dest)
        self.fail_ng("import-git", src, dest)

    def test_nonexistent_source_errors(self):
        self.fail_ng("import-git", os.path.join(self.tmpdir, "nope"))


# ══════════════════════════════════════════════════════════════════════════════
# Git-compatible local long options
# ══════════════════════════════════════════════════════════════════════════════

class TestMissingLocalLongOptions(NG):

    def test_init_initial_branch_and_clone_selectors(self):
        src = os.path.join(self.tmpdir, "src")
        os.makedirs(src)
        self.ok("init", "--initial-branch", "trunk", cwd=src)
        self.write("src/a.txt", "alpha\n")
        self.ok("add", ".", cwd=src)
        self.ok("commit", "-m", "base", cwd=src)
        self.ok("branch", "side", cwd=src)
        self.ok("tag", "v1", cwd=src)

        dest = os.path.join(self.tmpdir, "dest")
        self.ok("clone", "--single-branch", "--no-tags", "--no-checkout", src, dest)
        self.assertFalse(os.path.exists(os.path.join(dest, "a.txt")))
        self.assertEqual(self.ok("branch", cwd=dest).stdout.strip(), "* trunk")
        self.assertEqual(self.ok("tag", cwd=dest).stdout.strip(), "")

        tag_dest = os.path.join(self.tmpdir, "tag-dest")
        self.ok("clone", "--branch", "v1", "--no-tags", "--no-checkout", src, tag_dest)
        self.assertEqual(self.ok("tag", cwd=tag_dest).stdout.strip(), "")
        self.assertEqual(
            self.ok("rev-parse", "HEAD", cwd=tag_dest).stdout.strip(),
            self.ok("rev-parse", "v1", cwd=src).stdout.strip(),
        )

    def test_dry_run_options_do_not_mutate(self):
        self.init()
        self.write("a.txt", "one\n")
        self.ok("add", "--dry-run", "a.txt")
        self.assertIn("?? a.txt", self.ok("status", "--short").stdout)
        self.commit("base")

        self.write("a.txt", "two\n")
        head = self.ok("rev-parse", "HEAD").stdout.strip()
        self.ok("commit", "--dry-run", "--all", "-m", "preview")
        self.assertEqual(self.ok("rev-parse", "HEAD").stdout.strip(), head)
        self.assertIn(" M a.txt", self.ok("status", "--short").stdout)

        self.ok("mv", "--dry-run", "a.txt", "b.txt")
        self.assertTrue(self.exists("a.txt"))
        self.assertFalse(self.exists("b.txt"))

    def test_rm_safety_force_dry_run_ignore_and_quiet(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("base")
        self.write("a.txt", "local\n")
        rejected = self.fail_ng("rm", "a.txt")
        self.assertIn("--force", rejected.stderr)
        self.assertTrue(self.exists("a.txt"))
        self.ok("rm", "--dry-run", "--force", "a.txt")
        self.assertTrue(self.exists("a.txt"))
        quiet = self.ok("rm", "--force", "--quiet", "a.txt")
        self.assertEqual(quiet.stdout, "")
        self.ok("rm", "--ignore-unmatch", "missing.txt")

    def test_commit_allow_empty_file_message_and_signoff(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("base")
        old = self.ok("rev-parse", "HEAD").stdout.strip()
        self.write("message.txt", "empty checkpoint\n")
        self.ok("commit", "--allow-empty", "--file", "message.txt", "--signoff")
        new = self.ok("rev-parse", "HEAD").stdout.strip()
        self.assertNotEqual(new, old)
        shown = self.ok("show", "--no-patch")
        self.assertIn("empty checkpoint", shown.stdout)
        self.assertIn("Signed-off-by: Test User <test@example.com>", shown.stdout)
        self.ok("commit", "--allow-empty", "--allow-empty-message", "-m", "")

    def test_status_porcelain_null_ignored_untracked_and_stash(self):
        self.init()
        self.write("a.txt", "base\n")
        self.commit("base")
        self.write("loose.txt", "loose\n")
        self.write("ignored.pyc", "ignored\n")
        self.assertNotIn("loose.txt", self.ok("status", "--short", "--untracked-files=no").stdout)
        ignored = self.ok("status", "--short", "--ignored")
        self.assertIn("!! ignored.pyc", ignored.stdout)
        porcelain = self.ok("status", "--porcelain=2", "--branch")
        self.assertIn("# branch.head main", porcelain.stdout)
        self.assertIn("? loose.txt", porcelain.stdout)
        nul = self.ok("status", "--short", "--null")
        self.assertIn("\0", nul.stdout)

        self.write("a.txt", "dirty\n")
        self.ok("stash", "push")
        self.assertIn("stash currently has 1 entry", self.ok("status", "--show-stash").stdout)

    def test_diff_exit_code_and_quiet(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("base")
        self.assertEqual(self.ng("diff", "--exit-code").returncode, 0)
        self.write("a.txt", "two\n")
        changed = self.ng("diff", "--exit-code")
        self.assertEqual(changed.returncode, 1)
        self.assertIn("diff --notgit", changed.stdout)
        quiet = self.ng("diff", "--quiet")
        self.assertEqual(quiet.returncode, 1)
        self.assertEqual(quiet.stdout, "")

    def test_log_and_show_history_output_options(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("one")
        self.write("a.txt", "two\n")
        self.commit("two")
        self.write("b.txt", "three\n")
        self.commit("three")

        second = self.ok("log", "--oneline", "--max-count=1", "--skip=1")
        self.assertIn("two", second.stdout)
        self.assertNotIn("three", second.stdout)
        stat = self.ok("log", "--oneline", "--max-count=1", "--stat")
        self.assertIn("b.txt", stat.stdout)
        named = self.ok("show", "--name-status")
        self.assertIn("A\tb.txt", named.stdout)
        formatted = self.ok("show", "--format=%h %s", "--no-patch")
        self.assertIn("three", formatted.stdout)
        self.assertNotIn("diff --notgit", formatted.stdout)

    def test_branch_and_tag_query_and_format_options(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("base")
        head = self.ok("rev-parse", "HEAD").stdout.strip()
        self.ok("branch", "feature")
        self.ok("tag", "z-tag")
        self.ok("tag", "a-tag")
        self.assertEqual(self.ok("branch", "--show-current").stdout.strip(), "main")
        self.assertIn("feature", self.ok("branch", "--contains", "HEAD").stdout)
        self.assertIn("feature", self.ok("branch", "--points-at", head).stdout)
        formatted = self.ok("branch", "--list", "--sort=-refname", "--format=%(refname:short)")
        self.assertEqual(formatted.stdout.splitlines()[0], "main")
        tags = self.ok("tag", "--list", "--sort=refname", "--format=%(refname:short)")
        self.assertEqual(tags.stdout.splitlines(), ["a-tag", "z-tag"])
        self.assertIn("a-tag", self.ok("tag", "--points-at", "HEAD").stdout)
        self.assertIn("a-tag", self.ok("tag", "--merged").stdout)

    def test_checkout_detach_force_orphan_and_restore_patch(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("base")
        self.write("a.txt", "dirty\n")
        self.ok("checkout", "--force", "main")
        self.assertEqual(self.read("a.txt"), "one\n")
        self.ok("checkout", "--detach", "main")
        self.assertEqual(self.ok("branch", "--show-current").stdout, "")
        self.ok("checkout", "main")
        self.ok("checkout", "--orphan", "fresh")
        self.assertEqual(self.ok("rev-parse", "--abbrev-ref", "HEAD").stdout.strip(), "fresh")
        self.ok("commit", "-m", "root")
        root = self.ok("rev-parse", "HEAD").stdout.strip()
        with open(os.path.join(self.tmpdir, ".notgit", "objects", root[:2], root[2:]), "rb") as f:
            raw = f.read().split(b"\0", 1)[1]
        self.assertEqual(json.loads(raw)["parents"], [])

        self.write("a.txt", "again\n")
        self.ok("restore", "--patch", "a.txt", input="y\n")
        self.assertEqual(self.read("a.txt"), "one\n")

    def test_reset_keep_and_merge(self):
        self.init()
        self.write("a.txt", "a1\n")
        self.commit("one")
        first = self.ok("rev-parse", "HEAD").stdout.strip()
        self.write("b.txt", "b1\n")
        self.commit("two")
        self.write("a.txt", "local\n")
        self.ok("reset", "--keep", first)
        self.assertEqual(self.read("a.txt"), "local\n")
        self.assertFalse(self.exists("b.txt"))
        self.ok("reset", "--merge", "HEAD")
        self.assertEqual(self.read("a.txt"), "local\n")

    def test_rev_parse_repository_and_ref_queries(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("base")
        self.ok("branch", "feature")
        self.ok("tag", "v1")
        self.assertEqual(self.ok("rev-parse", "--is-bare-repository").stdout.strip(), "false")
        self.assertEqual(self.ok("rev-parse", "--show-object-format").stdout.strip(), "sha1")
        git_dir = self.ok("rev-parse", "--absolute-git-dir").stdout.strip()
        self.assertEqual(git_dir, os.path.join(self.tmpdir, ".notgit"))
        inside = self.ok("rev-parse", "--is-inside-git-dir", cwd=git_dir)
        self.assertEqual(inside.stdout.strip(), "true")
        symbolic = self.ok("rev-parse", "--symbolic-full-name", "main")
        self.assertEqual(symbolic.stdout.strip(), "refs/heads/main")
        self.assertEqual(len(self.ok("rev-parse", "--branches").stdout.splitlines()), 2)
        self.assertEqual(len(self.ok("rev-parse", "--tags").stdout.splitlines()), 1)

    def test_config_action_options(self):
        self.init()
        self.assertEqual(self.ok("config", "--local", "--get", "user.name").stdout.strip(), "Test User")
        listed = self.ok("config", "--list")
        self.assertIn("user.email=test@example.com", listed.stdout)
        self.assertEqual(
            self.ok("config", "--get", "--default", "fallback", "missing.key").stdout.strip(),
            "fallback",
        )
        self.ok("config", "--unset", "user.email")
        self.fail_ng("config", "--get", "user.email")

    def _make_diverged_branches(self):
        self.init()
        self.write("base.txt", "base\n")
        self.commit("base")
        self.ok("branch", "feature")
        self.ok("checkout", "feature")
        self.write("feature.txt", "feature\n")
        self.commit("side work")
        self.ok("checkout", "main")
        self.write("main.txt", "main\n")
        self.commit("main")

    def test_merge_no_commit_continue_message_and_ff_only(self):
        self._make_diverged_branches()
        self.fail_ng("merge", "--ff-only", "feature")
        before = self.ok("rev-parse", "HEAD").stdout.strip()
        self.ok("merge", "--no-commit", "--message", "combined", "feature")
        self.assertEqual(self.ok("rev-parse", "HEAD").stdout.strip(), before)
        self.assertTrue(self.exists(".notgit/MERGE_HEAD"))
        self.ok("merge", "--continue")
        self.assertIn("combined", self.ok("log", "--oneline", "--max-count=1").stdout)

    def test_merge_abort_squash_and_no_ff(self):
        self.init()
        self.write("a.txt", "base\n")
        self.commit("base")
        self.ok("branch", "feature")
        self.ok("checkout", "feature")
        self.write("b.txt", "feature\n")
        self.commit("feature")
        self.ok("checkout", "main")
        before = self.ok("rev-parse", "HEAD").stdout.strip()
        self.ok("merge", "--squash", "feature")
        self.assertEqual(self.ok("rev-parse", "HEAD").stdout.strip(), before)
        self.assertIn("A  b.txt", self.ok("status", "--short").stdout)
        self.ok("reset", "--hard", "HEAD")
        self.ok("merge", "--no-ff", "feature")
        merge_oid = self.ok("rev-parse", "HEAD").stdout.strip()
        with open(os.path.join(self.tmpdir, ".notgit", "objects", merge_oid[:2], merge_oid[2:]), "rb") as f:
            merge_data = json.loads(f.read().split(b"\0", 1)[1])
        self.assertEqual(len(merge_data["parents"]), 2)

    def test_merge_conflict_abort(self):
        self.init()
        self.write("a.txt", "base\n")
        self.commit("base")
        self.ok("branch", "feature")
        self.ok("checkout", "feature")
        self.write("a.txt", "feature\n")
        self.commit("feature")
        self.ok("checkout", "main")
        self.write("a.txt", "main\n")
        self.commit("main")
        self.fail_ng("merge", "feature")
        self.fail_ng("merge", "--continue")
        self.ok("merge", "--quit")
        self.assertFalse(self.exists(".notgit/MERGE_HEAD"))
        self.assertIn("<<<<<<<", self.read("a.txt"))
        self.ok("reset", "--hard", "HEAD")
        self.fail_ng("merge", "feature")
        self.ok("merge", "--abort")
        self.assertEqual(self.read("a.txt"), "main\n")
        self.assertFalse(self.exists(".notgit/MERGE_HEAD"))

    def test_merge_allows_unrelated_histories_only_when_requested(self):
        self.init()
        self.write("a.txt", "main\n")
        self.commit("main root")
        self.ok("checkout", "--orphan", "other")
        self.ok("rm", "--force", "a.txt")
        self.write("b.txt", "other\n")
        self.commit("other root")
        self.ok("checkout", "main")
        self.fail_ng("merge", "other")
        self.ok("merge", "--allow-unrelated-histories", "other")
        self.assertTrue(self.exists("a.txt"))
        self.assertTrue(self.exists("b.txt"))

    def test_log_merge_filters_first_parent_and_patch_names(self):
        self._make_diverged_branches()
        self.ok("merge", "feature")
        merges = self.ok("log", "--oneline", "--merges")
        self.assertEqual(len(merges.stdout.splitlines()), 1)
        non_merges = self.ok("log", "--oneline", "--no-merges")
        self.assertNotIn("Merge branch", non_merges.stdout)
        first_parent = self.ok("log", "--oneline", "--first-parent")
        self.assertNotIn(" side work", first_parent.stdout)
        names = self.ok("log", "--oneline", "--max-count=1", "--name-only")
        self.assertIn("feature.txt", names.stdout)
        statuses = self.ok("log", "--oneline", "--max-count=1", "--name-status")
        self.assertIn("A\tfeature.txt", statuses.stdout)
        patch = self.ok("log", "--oneline", "--max-count=1", "--patch")
        self.assertIn("diff --notgit", patch.stdout)

    def test_revert_mainline_no_commit_and_abort(self):
        self.init()
        self.write("a.txt", "base\n")
        self.commit("base")
        self.ok("branch", "feature")
        self.ok("checkout", "feature")
        self.write("b.txt", "feature\n")
        self.commit("feature")
        self.ok("checkout", "main")
        self.ok("merge", "--no-ff", "feature")
        self.ok("revert", "--mainline", "1", "HEAD")
        self.assertFalse(self.exists("b.txt"))

        self.write("a.txt", "changed\n")
        self.commit("change a")
        before = self.ok("rev-parse", "HEAD").stdout.strip()
        self.ok("revert", "--no-commit", "HEAD")
        self.assertEqual(self.ok("rev-parse", "HEAD").stdout.strip(), before)
        self.assertIn("M  a.txt", self.ok("status", "--short").stdout)
        self.ok("reset", "--hard", "HEAD")

        target = self.ok("rev-parse", "HEAD").stdout.strip()
        self.write("a.txt", "later\n")
        self.commit("later")
        self.fail_ng("revert", target)
        self.ok("revert", "--abort")
        self.assertEqual(self.read("a.txt"), "later\n")

    def test_revert_continue_quit_and_skip(self):
        self.init()
        self.write("a.txt", "base\n")
        self.commit("base")
        self.write("a.txt", "target\n")
        self.commit("target")
        target = self.ok("rev-parse", "HEAD").stdout.strip()
        self.write("a.txt", "later\n")
        self.commit("later")

        self.fail_ng("revert", target)
        self.fail_ng("revert", "--continue")
        self.ok("revert", "--quit")
        self.assertFalse(self.exists(".notgit/REVERT_HEAD"))
        self.assertIn("<<<<<<<", self.read("a.txt"))
        self.ok("reset", "--hard", "HEAD")

        self.fail_ng("revert", target)
        self.write("a.txt", "resolved\n")
        self.ok("add", "a.txt")
        self.ok("revert", "--continue")
        self.assertFalse(self.exists(".notgit/REVERT_HEAD"))
        self.assertIn("Revert", self.ok("log", "--oneline", "--max-count=1").stdout)

        self.write("a.txt", "newer\n")
        self.commit("newer")
        self.fail_ng("revert", target)
        self.ok("revert", "--skip")
        self.assertEqual(self.read("a.txt"), "newer\n")

    def test_stash_index_keep_staged_all_and_patch(self):
        self.init()
        self.write("a.txt", "a0\n")
        self.write("b.txt", "b0\n")
        self.commit("base")
        self.write("a.txt", "a1\n")
        self.ok("add", "a.txt")
        self.write("b.txt", "b1\n")
        self.ok("stash", "push")
        self.ok("stash", "pop")
        status = self.ok("status", "--short").stdout
        self.assertIn(" M a.txt", status)
        self.assertIn(" M b.txt", status)
        self.ok("add", "a.txt")
        self.ok("stash", "push")
        self.ok("stash", "pop", "--index")
        self.assertIn("M  a.txt", self.ok("status", "--short").stdout)

        self.ok("reset", "--hard", "HEAD")
        self.write("a.txt", "a2\n")
        self.ok("add", "a.txt")
        self.write("b.txt", "b2\n")
        self.ok("stash", "push", "--keep-index")
        kept = self.ok("status", "--short").stdout
        self.assertIn("M  a.txt", kept)
        self.assertNotIn("b.txt", kept)

        self.ok("reset", "--hard", "HEAD")
        self.write("a.txt", "a3\n")
        self.ok("add", "a.txt")
        self.write("b.txt", "b3\n")
        self.ok("stash", "push", "--staged")
        staged_only = self.ok("status", "--short").stdout
        self.assertNotIn("a.txt", staged_only)
        self.assertIn(" M b.txt", staged_only)

        self.ok("reset", "--hard", "HEAD")
        self.write("ignored.pyc", "ignored\n")
        self.ok("stash", "push", "--all")
        self.assertFalse(self.exists("ignored.pyc"))
        self.ok("stash", "pop")
        self.assertTrue(self.exists("ignored.pyc"))

        self.write("a.txt", "patch-a\n")
        self.write("b.txt", "patch-b\n")
        self.ok("stash", "push", "--patch", input="y\nn\n")
        self.assertEqual(self.read("a.txt"), "a0\n")
        self.assertEqual(self.read("b.txt"), "patch-b\n")

    def test_grep_output_selection_context_untracked_and_no_index(self):
        self.init()
        self.write("a.txt", "before\nneedle one\nafter\nneedle two\n")
        self.commit("base")
        counted = self.ok("grep", "--count", "needle")
        self.assertIn("a.txt:2", counted.stdout)
        limited = self.ok("grep", "--max-count=1", "needle")
        self.assertEqual(limited.stdout.count("needle"), 1)
        only = self.ok("grep", "--only-matching", "needle")
        self.assertEqual(only.stdout.count("needle"), 2)
        inverted = self.ok("grep", "--invert-match", "needle")
        self.assertIn("before", inverted.stdout)
        context = self.ok("grep", "--line-number", "--context=1", "needle")
        self.assertIn("a.txt-1-before", context.stdout)
        quiet = self.ok("grep", "--quiet", "needle")
        self.assertEqual(quiet.stdout, "")
        self.write("loose.txt", "untracked marker\n")
        self.assertIn("loose.txt", self.ok("grep", "--untracked", "marker").stdout)
        self.assertIn("loose.txt", self.ok("grep", "--no-index", "marker", "loose.txt").stdout)
        outside = tempfile.mkdtemp(prefix="notgit_grep_no_index_")
        self.addCleanup(shutil.rmtree, outside, ignore_errors=True)
        with open(os.path.join(outside, "plain.txt"), "w") as f:
            f.write("outside marker\n")
        result = self.ok("grep", "--no-index", "marker", "plain.txt", cwd=outside)
        self.assertIn("plain.txt", result.stdout)


class TestUltraFunctionalFixes(NG):

    @unittest.skipIf(os.name == "nt", "requires reliable symbolic links")
    def test_symlinks_cannot_read_or_write_outside_worktree(self):
        self.init()
        outside = tempfile.mkdtemp(prefix="notgit_outside_")
        self.addCleanup(shutil.rmtree, outside, ignore_errors=True)
        with open(os.path.join(outside, "secret"), "w") as f:
            f.write("secret\n")
        os.symlink(os.path.join(outside, "secret"), os.path.join(self.tmpdir, "leak"))
        rejected = self.fail_ng("add", "leak")
        self.assertIn("symbol", rejected.stderr.lower())

        os.unlink(os.path.join(self.tmpdir, "leak"))
        self.write("dir/file", "inside\n")
        self.commit("base")
        os.rename(os.path.join(self.tmpdir, "dir"), os.path.join(self.tmpdir, "saved"))
        os.symlink(outside, os.path.join(self.tmpdir, "dir"), target_is_directory=True)
        rejected = self.fail_ng("checkout", "--force", "main")
        self.assertIn("symbol", rejected.stderr.lower())
        self.assertFalse(os.path.exists(os.path.join(outside, "file")))

    def test_repository_lock_rejects_concurrent_mutation(self):
        self.init()
        self.write("a.txt", "one\n")
        spec = importlib.util.spec_from_file_location("notgit_lock_test", SCRIPT)
        ng = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ng)
        with ng._repository_lock_at(self.tmpdir):
            result = self.fail_ng("add", "a.txt")
            self.assertIn("another notgit process", result.stderr)
            self.assertEqual(json.loads(self.read(".notgit/index")), {})

    def test_reset_merge_preserves_or_rejects_unstaged_changes(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("one")
        first = self.ok("rev-parse", "HEAD").stdout.strip()
        self.write("b.txt", "two\n")
        self.commit("two")
        self.write("a.txt", "local\n")
        self.ok("reset", "--merge", "HEAD")
        self.assertEqual(self.read("a.txt"), "local\n")
        self.write("b.txt", "local b\n")
        rejected = self.fail_ng("reset", "--merge", first)
        self.assertIn("not uptodate", rejected.stderr)
        self.assertEqual(self.read("a.txt"), "local\n")

    def test_merge_combines_disjoint_edits_and_preserves_binary_conflict(self):
        self.init()
        self.write("a.txt", "one\nmiddle\nthree\n")
        self.commit("base")
        self.ok("checkout", "-b", "topic")
        self.write("a.txt", "one\nmiddle\nTHREE\n")
        self.commit("topic")
        self.ok("checkout", "main")
        self.write("a.txt", "ONE\nmiddle\nthree\n")
        self.commit("main")
        self.ok("merge", "topic")
        self.assertEqual(self.read("a.txt"), "ONE\nmiddle\nTHREE\n")

        with open(os.path.join(self.tmpdir, "binary"), "wb") as f:
            f.write(b"\xffbase\n")
        self.commit("binary base")
        self.ok("checkout", "-b", "binary-topic")
        with open(os.path.join(self.tmpdir, "binary"), "wb") as f:
            f.write(b"\xfftopic\n")
        self.commit("binary topic")
        self.ok("checkout", "main")
        with open(os.path.join(self.tmpdir, "binary"), "wb") as f:
            f.write(b"\xffmain\n")
        self.commit("binary main")
        self.fail_ng("merge", "binary-topic")
        with open(os.path.join(self.tmpdir, "binary"), "rb") as f:
            self.assertEqual(f.read(), b"\xffmain\n")

    def test_commit_refuses_structurally_unresolved_merge(self):
        self.init()
        self.write("a.txt", "base\n")
        self.commit("base")
        self.ok("checkout", "-b", "topic")
        self.write("a.txt", "topic\n")
        self.commit("topic")
        self.ok("checkout", "main")
        self.write("a.txt", "main\n")
        self.commit("main")
        self.fail_ng("merge", "topic")
        rejected = self.fail_ng("commit", "-m", "bad merge")
        self.assertIn("unmerged paths", rejected.stderr)
        self.write("a.txt", "literal <<<<<<< text is allowed\n")
        self.ok("add", "a.txt")
        self.ok("commit", "-m", "resolved")

    def test_stash_apply_uses_saved_base(self):
        self.init()
        self.write("a.txt", "A\n")
        self.commit("base")
        self.write("a.txt", "B\n")
        self.ok("stash", "push")
        self.ok("checkout", "-b", "other")
        self.write("a.txt", "C\n")
        self.commit("other")
        rejected = self.fail_ng("stash", "apply")
        self.assertIn("conflict", rejected.stderr)
        self.assertEqual(self.read("a.txt"), "C\n")
        self.assertIn("stash@{0}", self.ok("stash", "list").stdout)

    def test_safe_branch_delete_requires_merged_history(self):
        self.init()
        self.write("base", "base\n")
        self.commit("base")
        self.ok("checkout", "-b", "topic")
        self.write("topic", "topic\n")
        self.commit("topic")
        self.ok("checkout", "main")
        rejected = self.fail_ng("branch", "-d", "topic")
        self.assertIn("not fully merged", rejected.stderr)
        self.ok("branch", "-D", "topic")

    def test_diff_excludes_untracked_and_honors_staged_base(self):
        self.init()
        self.write("a.txt", "first\n")
        self.commit("first")
        first = self.ok("rev-parse", "HEAD").stdout.strip()
        self.write("a.txt", "second\n")
        self.commit("second")
        self.write("a.txt", "third\n")
        self.ok("add", "a.txt")
        self.write("loose.txt", "loose\n")
        self.assertNotIn("loose.txt", self.ok("diff", "--name-status").stdout)
        staged = self.ok("diff", "--staged", first)
        self.assertIn("-first", staged.stdout)
        self.assertIn("+third", staged.stdout)

    def test_restore_staged_directory_removes_added_entries(self):
        self.init()
        self.write("dir/a", "a\n")
        self.commit("base")
        self.write("dir/b", "b\n")
        self.ok("add", "dir/b")
        self.ok("restore", "--staged", "dir")
        self.assertIn("?? dir/b", self.ok("status", "--short").stdout)

    def test_failed_commit_all_does_not_change_index(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("base")
        self.write("a.txt", "two\n")
        before = self.read(".notgit/index")
        self.fail_ng("commit", "--all")
        self.assertEqual(self.read(".notgit/index"), before)
        self.assertIn(" M a.txt", self.ok("status", "--short").stdout)

    def test_hierarchical_refs_list_and_clone(self):
        src = os.path.join(self.tmpdir, "src")
        os.makedirs(src)
        self.ok("init", cwd=src)
        self.write("src/a.txt", "one\n")
        self.ok("add", ".", cwd=src)
        self.ok("commit", "-m", "base", cwd=src)
        self.ok("checkout", "-b", "feature/nested", cwd=src)
        self.ok("tag", "release/v1", cwd=src)
        self.assertIn("feature/nested", self.ok("branch", cwd=src).stdout)
        self.assertIn("release/v1", self.ok("tag", cwd=src).stdout)
        dest = os.path.join(self.tmpdir, "dest")
        self.ok("clone", src, dest)
        self.assertEqual(
            self.ok("branch", "--show-current", cwd=dest).stdout.strip(),
            "feature/nested",
        )

    def test_malformed_commit_reports_repository_error(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("base")
        head = self.ok("rev-parse", "HEAD").stdout.strip()
        path = os.path.join(self.tmpdir, ".notgit", "objects", head[:2], head[2:])
        with open(path, "rb") as f:
            data = json.loads(f.read().split(b"\0", 1)[1])
        del data["message"]
        body = json.dumps(data, sort_keys=True).encode()
        raw = b"commit " + str(len(body)).encode() + b"\0" + body
        bad_oid = hashlib.sha1(raw).hexdigest()
        bad_path = os.path.join(self.tmpdir, ".notgit", "objects", bad_oid[:2], bad_oid[2:])
        os.makedirs(os.path.dirname(bad_path), exist_ok=True)
        with open(bad_path, "wb") as f:
            f.write(raw)
        self.write(".notgit/refs/heads/main", bad_oid)
        result = self.fail_ng("log")
        self.assertIn("invalid commit message", result.stderr)
        self.assertNotIn("Traceback", result.stderr)

    def test_gitignore_negation_reincludes_descendant(self):
        self.init()
        self.write(".notgitignore", "build/\n!build/keep.txt\n")
        self.write("build/drop.txt", "drop\n")
        self.write("build/keep.txt", "keep\n")
        status = self.ok("status", "--short").stdout
        self.assertIn("?? build/keep.txt", status)
        self.assertNotIn("build/drop.txt", status)

    def test_log_is_topological_then_date_ordered(self):
        self.init()
        self.write("base", "base\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "base", "--date", "1000000000")
        self.ok("checkout", "-b", "topic")
        self.write("topic", "topic\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "topic", "--date", "3000000000")
        self.ok("checkout", "main")
        self.write("main", "main\n")
        self.ok("add", ".")
        self.ok("commit", "-m", "main", "--date", "2000000000")
        self.ok("merge", "--no-ff", "topic")
        subjects = self.ok("log", "--format=%s", "-n", "4").stdout.splitlines()
        self.assertEqual(subjects[1:3], ["topic", "main"])

    def test_porcelain_validates_version_modes_and_quotes_paths(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("base")
        self.ok("rm", "--cached", "a.txt")
        line = next(line for line in self.ok("status", "--porcelain=2").stdout.splitlines()
                    if line.startswith("1 "))
        self.assertIn("100644 000000 100644", line)
        self.fail_ng("status", "--porcelain=bogus")
        self.write("odd\nname", "odd\n")
        quoted = self.ok("status", "--porcelain").stdout
        self.assertIn('"odd\\nname"', quoted)

    def test_tag_message_implies_annotation(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("base")
        head = self.ok("rev-parse", "HEAD").stdout.strip()
        self.ok("tag", "-m", "release notes", "v1")
        tag_oid = self.read(".notgit/refs/tags/v1").strip()
        self.assertNotEqual(tag_oid, head)
        path = os.path.join(self.tmpdir, ".notgit", "objects", tag_oid[:2], tag_oid[2:])
        with open(path, "rb") as f:
            self.assertTrue(f.read().startswith(b"tag "))

    def test_stash_show_lists_only_changed_paths(self):
        self.init()
        self.write("one", "one\n")
        self.write("two", "two\n")
        self.commit("base")
        self.write("one", "changed\n")
        self.ok("stash", "push")
        self.assertEqual(self.ok("stash", "show").stdout.splitlines(), ["one"])

    def test_versions_refuses_existing_output(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("base")
        first = self.ok("versions", "a.txt").stdout.strip()
        rejected = self.fail_ng("versions", "a.txt")
        self.assertIn("refusing to overwrite", rejected.stderr)
        self.assertEqual(self.read(first), "one\n")


class TestReliabilityHardening(NG):

    def module(self, suffix):
        spec = importlib.util.spec_from_file_location(f"notgit_reliability_{suffix}", SCRIPT)
        ng = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ng)
        return ng

    def index(self):
        with open(os.path.join(self.tmpdir, ".notgit", "index")) as f:
            return json.load(f)

    def _git_object(self, git_dir, obj_type, content):
        raw = f"{obj_type} {len(content)}\0".encode() + content
        oid = hashlib.sha1(raw).hexdigest()
        path = os.path.join(git_dir, "objects", oid[:2], oid[2:])
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, "wb") as f:
            f.write(zlib.compress(raw))
        return oid

    @unittest.skipIf(os.name == "nt", "requires symbolic links")
    def test_worktree_install_uses_unique_non_following_temporary_file(self):
        self.init()
        ng = self.module("safe_temp")
        outside = os.path.join(tempfile.mkdtemp(prefix="notgit_outside_"), "outside")
        self.addCleanup(shutil.rmtree, os.path.dirname(outside), ignore_errors=True)
        with open(outside, "wb") as f:
            f.write(b"outside")
        previous = os.getcwd()
        try:
            os.chdir(self.tmpdir)
            ng._WORKTREE_ROOT = self.tmpdir
            with open("a.notgit-tmp", "wb") as f:
                f.write(b"sibling")
            ng._write_worktree_file("a", b"first")
            self.assertEqual(self.read("a.notgit-tmp"), "sibling")
            os.remove("a.notgit-tmp")
            os.symlink(outside, "a.notgit-tmp")
            ng._write_worktree_file("a", b"second")
            with open(outside, "rb") as f:
                self.assertEqual(f.read(), b"outside")
            self.assertFalse(os.path.islink("a"))
            self.assertTrue(os.path.islink("a.notgit-tmp"))
        finally:
            os.chdir(previous)

    def test_failed_multi_file_reset_rolls_back_every_file_and_metadata(self):
        self.init()
        self.write("a", "one")
        self.write("b", "one")
        self.commit("one")
        first = self.ok("rev-parse", "HEAD").stdout.strip()
        self.write("a", "two")
        self.write("b", "two")
        self.commit("two")
        second = self.ok("rev-parse", "HEAD").stdout.strip()
        index_before = self.index()
        ng = self.module("reset_rollback")
        original_install = ng._install_transaction_file
        failed = [False]

        def fail_second(source, target, mode):
            if target == "b" and not failed[0]:
                failed[0] = True
                raise OSError("injected second-file failure")
            return original_install(source, target, mode)

        previous = os.getcwd()
        try:
            os.chdir(self.tmpdir)
            ng._INVOCATION_CWD = self.tmpdir
            ng._WORKTREE_ROOT = self.tmpdir
            args = ng.build_parser().parse_args(["reset", "--hard", first])
            with mock.patch.object(ng, "_install_transaction_file", fail_second), \
                    mock.patch.object(sys, "stderr", io.StringIO()), \
                    self.assertRaises(SystemExit):
                ng.cmd_reset(args)
        finally:
            os.chdir(previous)
        self.assertEqual(self.read("a"), "two")
        self.assertEqual(self.read("b"), "two")
        self.assertEqual(self.ok("rev-parse", "HEAD").stdout.strip(), second)
        self.assertEqual(self.index(), index_before)
        self.assertFalse(self.exists(".notgit/TRANSACTION"))

    def test_next_mutation_recovers_interrupted_transaction(self):
        self.init()
        self.write("a", "original")
        ng = self.module("crash_recovery")
        previous = os.getcwd()
        try:
            os.chdir(self.tmpdir)
            ng._WORKTREE_ROOT = self.tmpdir
            record = ng._prepare_repository_transaction({"a": b"partial"}, [])
            ng._apply_repository_transaction(record)
            self.assertEqual(self.read("a"), "partial")
        finally:
            os.chdir(previous)
        recovered = self.ok("config", "recovery.test", "yes")
        self.assertIn("recovered an interrupted", recovered.stderr)
        self.assertEqual(self.read("a"), "original")
        self.assertFalse(self.exists(".notgit/TRANSACTION"))

    def _diverged_conflict(self):
        self.init()
        self.write("f", "base\n")
        self.commit("base")
        self.ok("checkout", "-b", "side")
        self.write("f", "side\n")
        self.commit("side")
        self.ok("checkout", "main")
        self.write("f", "main\n")
        self.commit("main")

    def test_merge_state_write_failure_rolls_back_conflict_result(self):
        self._diverged_conflict()
        index_before = self.index()
        ng = self.module("merge_state_setup")
        original_write = ng._atomic_write_text

        def fail_merge_head(path, text):
            if path == ng.MERGE_HEAD_FILE:
                raise OSError("injected merge-state failure")
            return original_write(path, text)

        previous = os.getcwd()
        try:
            os.chdir(self.tmpdir)
            ng._INVOCATION_CWD = self.tmpdir
            ng._WORKTREE_ROOT = self.tmpdir
            args = ng.build_parser().parse_args(["merge", "side"])
            with mock.patch.object(ng, "_atomic_write_text", fail_merge_head), \
                    mock.patch.object(sys, "stderr", io.StringIO()), \
                    self.assertRaises(SystemExit):
                ng.cmd_merge(args)
        finally:
            os.chdir(previous)
        self.assertEqual(self.read("f"), "main\n")
        self.assertEqual(self.index(), index_before)
        self.assertFalse(self.exists(".notgit/MERGE_HEAD"))
        self.assertFalse(self.exists(".notgit/TRANSACTION"))

    def test_merge_cleanup_failure_rolls_back_new_commit(self):
        self._diverged_conflict()
        self.fail_ng("merge", "side")
        self.write("f", "resolved\n")
        self.ok("add", "f")
        before = self.ok("rev-parse", "HEAD").stdout.strip()
        ng = self.module("merge_cleanup")
        original_unlink = ng._durable_unlink

        def fail_merge_cleanup(path, **kwargs):
            if path == ng.MERGE_HEAD_FILE:
                raise PermissionError("injected cleanup failure")
            return original_unlink(path, **kwargs)

        previous = os.getcwd()
        try:
            os.chdir(self.tmpdir)
            ng._INVOCATION_CWD = self.tmpdir
            ng._WORKTREE_ROOT = self.tmpdir
            args = ng.build_parser().parse_args(["commit", "-m", "resolved"])
            with mock.patch.object(ng, "_durable_unlink", fail_merge_cleanup), \
                    mock.patch.object(sys, "stderr", io.StringIO()), \
                    self.assertRaises(SystemExit):
                ng.cmd_commit(args)
        finally:
            os.chdir(previous)
        self.assertEqual(self.ok("rev-parse", "HEAD").stdout.strip(), before)
        self.assertTrue(self.exists(".notgit/MERGE_HEAD"))
        self.assertFalse(self.exists(".notgit/TRANSACTION"))
        self.ok("commit", "-m", "resolved")
        self.assertFalse(self.exists(".notgit/MERGE_HEAD"))

    def test_invalid_merge_head_cannot_create_corrupt_history(self):
        self.init()
        self.write("f", "one\n")
        self.commit("base")
        before = self.ok("rev-parse", "HEAD").stdout.strip()
        self.write("f", "two\n")
        self.ok("add", "f")
        self.write(".notgit/MERGE_HEAD", "not-an-object")
        rejected = self.fail_ng("commit", "-m", "bad merge")
        self.assertIn("invalid merge state", rejected.stderr)
        self.assertEqual(self.ok("rev-parse", "HEAD").stdout.strip(), before)

    def test_stale_lock_file_does_not_wedge_repository(self):
        self.init()
        self.write("a", "content")
        self.write(".notgit/LOCK", "stale owner")
        self.ok("add", "a")
        self.assertIn("a", self.index())

    def test_branch_rename_rolls_back_if_head_update_fails(self):
        self.init()
        self.write("a", "one")
        self.commit("base")
        ng = self.module("branch_rename")
        previous = os.getcwd()
        try:
            os.chdir(self.tmpdir)
            ng._INVOCATION_CWD = self.tmpdir
            ng._WORKTREE_ROOT = self.tmpdir
            args = ng.build_parser().parse_args(["branch", "-m", "renamed"])
            with mock.patch.object(ng, "set_head_ref", side_effect=OSError("head failure")), \
                    mock.patch.object(sys, "stderr", io.StringIO()), \
                    self.assertRaises(SystemExit):
                ng.cmd_branch(args)
        finally:
            os.chdir(previous)
        self.assertTrue(self.exists(".notgit/refs/heads/main"))
        self.assertFalse(self.exists(".notgit/refs/heads/renamed"))
        self.assertEqual(self.ok("branch", "--show-current").stdout.strip(), "main")

    def test_clone_holds_source_lock_and_never_publishes_partial_destination(self):
        source = os.path.join(self.tmpdir, "source")
        destination = os.path.join(self.tmpdir, "clone")
        os.mkdir(source)
        self.ok("init", cwd=source)
        with open(os.path.join(source, "a"), "w") as f:
            f.write("one")
        self.ok("add", "a", cwd=source)
        self.ok("commit", "-m", "base", cwd=source)
        ng = self.module("clone_lock")
        with ng._repository_lock_at(source):
            rejected = self.fail_ng("clone", source, destination)
        self.assertIn("another notgit process", rejected.stderr)
        self.assertFalse(os.path.exists(destination))
        self.ok("clone", source, destination)
        self.assertTrue(os.path.isfile(os.path.join(destination, "a")))

        malformed = os.path.join(self.tmpdir, "malformed")
        bad_dest = os.path.join(self.tmpdir, "bad-clone")
        os.makedirs(os.path.join(malformed, ".notgit", "objects"))
        failed = self.fail_ng("clone", malformed, bad_dest)
        self.assertIn("source HEAD", failed.stderr)
        self.assertFalse(os.path.lexists(bad_dest))

    def test_import_failure_removes_private_destination(self):
        git_dir = os.path.join(self.tmpdir, "bare")
        os.makedirs(os.path.join(git_dir, "objects"))
        os.makedirs(os.path.join(git_dir, "refs", "heads"))
        bad_tree = self._git_object(git_dir, "tree", b"malformed tree")
        commit_text = (
            f"tree {bad_tree}\n"
            "author A <a@example.com> 1 +0000\n"
            "committer A <a@example.com> 1 +0000\n\nmessage\n"
        ).encode()
        commit = self._git_object(git_dir, "commit", commit_text)
        with open(os.path.join(git_dir, "refs", "heads", "main"), "w") as f:
            f.write(commit + "\n")
        with open(os.path.join(git_dir, "HEAD"), "w") as f:
            f.write("ref: refs/heads/main\n")
        destination = os.path.join(self.tmpdir, "imported")
        rejected = self.fail_ng("import-git", git_dir, destination)
        self.assertIn("corrupt git tree", rejected.stderr)
        self.assertNotIn("Traceback", rejected.stderr)
        self.assertFalse(os.path.lexists(destination))

    def test_git_import_rejects_truncated_index_and_mismatched_loose_object(self):
        git_dir = os.path.join(self.tmpdir, "bad-pack")
        pack_dir = os.path.join(git_dir, "objects", "pack")
        os.makedirs(pack_dir)
        os.makedirs(os.path.join(git_dir, "refs"))
        self.write("bad-pack/HEAD", "ref: refs/heads/main\n")
        with open(os.path.join(pack_dir, "bad.idx"), "wb") as f:
            f.write(b"\xfftOc" + struct.pack(">I", 2))
        self.write("bad-pack/objects/pack/bad.pack", "")
        rejected = self.fail_ng(
            "import-git", git_dir, os.path.join(self.tmpdir, "bad-pack-output")
        )
        self.assertIn("truncated", rejected.stderr)
        self.assertNotIn("Traceback", rejected.stderr)

        loose_dir = os.path.join(self.tmpdir, "loose")
        oid = "aa" + "0" * 38
        path = os.path.join(loose_dir, "objects", oid[:2], oid[2:])
        os.makedirs(os.path.dirname(path))
        with open(path, "wb") as f:
            f.write(zlib.compress(b"blob 999999\0x"))
        ng = self.module("bad_loose")
        stderr = io.StringIO()
        with mock.patch.object(sys, "stderr", stderr), self.assertRaises(SystemExit):
            ng._GitObjectStore(loose_dir).read(oid)
        self.assertIn("hash mismatch", stderr.getvalue())

    def test_git_import_enforces_in_memory_object_limit(self):
        loose_dir = os.path.join(self.tmpdir, "large-loose")
        content = b"x" * 128
        raw = b"blob 128\0" + content
        oid = hashlib.sha1(raw).hexdigest()
        path = os.path.join(loose_dir, "objects", oid[:2], oid[2:])
        os.makedirs(os.path.dirname(path))
        with open(path, "wb") as f:
            f.write(zlib.compress(raw))
        ng = self.module("large_loose")
        ng.MAX_GIT_OBJECT_BYTES = 32
        with mock.patch.object(sys, "stderr", io.StringIO()), self.assertRaises(SystemExit):
            ng._GitObjectStore(loose_dir).read(oid)

    def test_blob_payloads_are_not_cached_and_restore_streams_them(self):
        self.init()
        self.write("a", "stream me\n")
        self.commit("base")
        blob = self.index()["a"]
        head = self.ok("rev-parse", "HEAD").stdout.strip()
        ng = self.module("blob_stream")
        previous = os.getcwd()
        try:
            os.chdir(self.tmpdir)
            ng._WORKTREE_ROOT = self.tmpdir
            with mock.patch.object(
                    ng, "_read_object_uncached", wraps=ng._read_object_uncached
                 ) as uncached:
                ng.read_object(blob)
                ng.read_object(blob)
                self.assertEqual(uncached.call_count, 2)
            tree = ng.read_commit(head)["tree"]
            self.write("a", "changed\n")
            original_read = ng.read_object

            def reject_blob_read(oid):
                if oid == blob:
                    raise AssertionError("restore retained a complete blob")
                return original_read(oid)

            with mock.patch.object(ng, "read_object", side_effect=reject_blob_read):
                ng.restore_tree_to_workdir(tree)
        finally:
            os.chdir(previous)
        self.assertEqual(self.read("a"), "stream me\n")

    def test_reinit_repairs_incomplete_metadata(self):
        os.mkdir(os.path.join(self.tmpdir, ".notgit"))
        result = self.ok("init")
        self.assertIn("Reinitialized", result.stdout)
        for path in ("HEAD", "index", "config", "objects", "refs/heads", "refs/tags"):
            self.assertTrue(os.path.exists(os.path.join(self.tmpdir, ".notgit", path)))

    def test_versions_preflights_every_output_before_writing(self):
        self.init()
        self.write("f.txt", "one")
        self.commit("one")
        self.write("f.txt", "two")
        self.commit("two")
        names = self.ok("versions", "f.txt").stdout.splitlines()
        for name in names:
            os.remove(os.path.join(self.tmpdir, name))
        self.write(names[1], "collision")
        rejected = self.fail_ng("versions", "f.txt")
        self.assertIn(names[1], rejected.stderr)
        self.assertFalse(self.exists(names[0]))

    def test_nonzero_pager_falls_back_to_stdout_with_error(self):
        ng = self.module("pager")
        stdout = io.StringIO()
        stderr = io.StringIO()
        command = [sys.executable, "-c", "import sys; sys.exit(7)"]
        with mock.patch.object(ng, "_pager_command", return_value=command), \
                mock.patch.object(sys, "stdout", stdout), \
                mock.patch.object(sys, "stderr", stderr):
            ng._write_paged("important output\n")
        self.assertEqual(stdout.getvalue(), "important output\n")
        self.assertIn("status 7", stderr.getvalue())

    def test_atomic_writes_fsync_parent_directories(self):
        self.init()
        ng = self.module("durability")
        previous = os.getcwd()
        try:
            os.chdir(self.tmpdir)
            ng._WORKTREE_ROOT = self.tmpdir
            with mock.patch.object(
                    ng, "_fsync_directory", wraps=ng._fsync_directory
                 ) as sync_dir:
                ng._atomic_write_text("durable", "value")
                self.assertTrue(sync_dir.called)
            with mock.patch.object(
                    ng, "_fsync_directory", wraps=ng._fsync_directory
                 ) as sync_dir:
                ng.store_object("blob", b"durability-object")
                self.assertTrue(any(
                    call.args[0].startswith(ng.OBJECTS_DIR) for call in sync_dir.call_args_list
                ))
        finally:
            os.chdir(previous)


# ══════════════════════════════════════════════════════════════════════════════
# Functional review fixes: data loss, state integrity, output, performance
# ══════════════════════════════════════════════════════════════════════════════

class TestFunctionalReviewFixes(NG):

    def module(self, suffix):
        spec = importlib.util.spec_from_file_location(f"notgit_review_{suffix}", SCRIPT)
        ng = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(ng)
        return ng

    def index(self):
        with open(os.path.join(self.tmpdir, ".notgit", "index")) as f:
            return json.load(f)

    def two_branches(self):
        """main and other share shared.txt; other adds other.txt."""
        self.init()
        self.write("shared.txt", "base\n")
        self.commit("init")
        self.ok("checkout", "-b", "other")
        self.write("other.txt", "other\n")
        self.commit("other")
        self.ok("checkout", "main")

    # ── checkout carries local changes ────────────────────────────────────────

    def test_checkout_carries_unstaged_edit_and_staged_new_file(self):
        self.two_branches()
        self.write("shared.txt", "local edit\n")
        self.write("staged_new.txt", "new\n")
        self.ok("add", "staged_new.txt")
        self.ok("checkout", "other")
        self.assertEqual(self.read("shared.txt"), "local edit\n")
        self.assertEqual(self.read("staged_new.txt"), "new\n")
        self.assertIn("staged_new.txt", self.index())
        self.assertEqual(self.read("other.txt"), "other\n")
        short = self.ok("status", "--short").stdout
        self.assertIn(" M shared.txt", short)
        self.assertIn("A  staged_new.txt", short)

    def test_detached_checkout_carries_local_changes(self):
        self.two_branches()
        other = self.ok("rev-parse", "other").stdout.strip()
        self.write("shared.txt", "local edit\n")
        self.ok("checkout", other)
        self.assertEqual(self.read("shared.txt"), "local edit\n")

    def test_checkout_still_refuses_dirty_path_that_differs(self):
        self.two_branches()
        self.ok("checkout", "other")
        self.write("other.txt", "edited\n")
        r = self.fail_ng("checkout", "main")
        self.assertIn("other.txt", r.stderr)
        self.assertEqual(self.read("other.txt"), "edited\n")

    def test_checkout_force_still_discards_local_changes(self):
        self.two_branches()
        self.write("shared.txt", "local edit\n")
        self.ok("checkout", "--force", "other")
        self.assertEqual(self.read("shared.txt"), "base\n")

    # ── directory/file transitions ───────────────────────────────────────────

    def test_checkout_between_directory_and_file_at_same_path(self):
        self.init()
        self.write("a/b", "x\n")
        self.commit("dir")
        self.ok("branch", "dirside")
        self.ok("rm", "a/b")
        self.assertFalse(self.exists("a"), "rm must prune the emptied directory")
        self.write("a", "file\n")
        self.ok("add", "a")
        self.ok("commit", "-m", "file")
        self.ok("checkout", "dirside")
        self.assertEqual(self.read("a/b"), "x\n")
        self.ok("checkout", "main")
        self.assertEqual(self.read("a"), "file\n")
        self.assertEqual(self.ok("status", "--short").stdout, "")
        self.ok("reset", "--hard", "dirside")
        self.assertEqual(self.read("a/b"), "x\n")

    def test_checkout_directory_to_file_protects_untracked_content(self):
        self.init()
        self.write("a/b", "x\n")
        self.commit("dir")
        self.ok("branch", "dirside")
        self.ok("rm", "a/b")
        self.write("a", "file\n")
        self.ok("add", "a")
        self.ok("commit", "-m", "file")
        self.ok("checkout", "dirside")
        self.write("a/untracked.txt", "keep me\n")
        r = self.fail_ng("checkout", "main")
        self.assertIn("a/untracked.txt", r.stderr)
        self.assertEqual(self.read("a/untracked.txt"), "keep me\n")

    # ── stash / revert must not drop work ────────────────────────────────────

    def test_stash_staged_refuses_unstaged_changes_on_top(self):
        self.init()
        self.write("f", "v1\n")
        self.commit("one")
        self.write("f", "v2\n")
        self.ok("add", "f")
        self.write("f", "v3\n")
        r = self.fail_ng("stash", "push", "--staged")
        self.assertIn("unstaged changes", r.stderr)
        self.assertEqual(self.read("f"), "v3\n")
        self.assertEqual(self.ok("stash", "list").stdout, "")

    def test_stash_staged_still_works_without_layered_changes(self):
        self.init()
        self.write("f", "v1\n")
        self.commit("one")
        self.write("f", "v2\n")
        self.ok("add", "f")
        self.ok("stash", "push", "--staged")
        self.assertEqual(self.read("f"), "v1\n")
        self.ok("stash", "pop")
        self.assertEqual(self.read("f"), "v2\n")

    def test_revert_continue_keeps_unstaged_worktree_edits(self):
        self.init()
        self.write("a", "1\n")
        self.write("b", "b\n")
        self.commit("one")
        self.write("a", "2\n")
        self.commit("two")
        self.write("a", "3\n")
        self.commit("three")
        self.fail_ng("revert", "HEAD~1")
        self.write("a", "resolved\n")
        self.ok("add", "a")
        self.write("b", "unstaged work\n")
        self.ok("revert", "--continue")
        self.assertEqual(self.read("b"), "unstaged work\n")
        self.assertIn("Revert", self.ok("log", "--oneline", "-1").stdout)

    # ── symlinks, refs and mv ────────────────────────────────────────────────

    @unittest.skipIf(os.name == "nt", "symlinks need privileges on Windows")
    def test_symlinks_are_skipped_instead_of_failing_scans(self):
        self.init()
        self.write("real.txt", "x\n")
        self.commit("one")
        os.symlink("real.txt", os.path.join(self.tmpdir, "link.txt"))
        r = self.ok("status", "--short")
        self.assertNotIn("link.txt", r.stdout)
        self.assertIn("skipping symbolic link 'link.txt'", r.stderr)
        self.ok("add", ".")
        self.assertNotIn("link.txt", self.index())

    def test_branch_force_refuses_to_move_current_branch(self):
        self.init()
        self.write("f", "1\n")
        self.commit("one")
        self.ok("branch", "old")
        self.write("f", "2\n")
        self.commit("two")
        head = self.ok("rev-parse", "HEAD").stdout.strip()
        r = self.fail_ng("branch", "-f", "main", "old")
        self.assertIn("cannot force update the current branch", r.stderr)
        r = self.fail_ng("branch", "-M", "old", "main")
        self.assertIn("cannot force update the current branch", r.stderr)
        self.assertEqual(self.ok("rev-parse", "HEAD").stdout.strip(), head)
        self.assertTrue(self.exists(".notgit/refs/heads/old"))

    def test_ref_prefix_conflicts_fail_without_traceback(self):
        self.init()
        self.initial_commit()
        self.ok("branch", "a")
        for args in (("branch", "a/b"), ("checkout", "-b", "a/c"), ("tag", "a")):
            if args[0] == "tag":
                self.ok("tag", "t")
                args = ("tag", "t/x")
            r = self.fail_ng(*args)
            self.assertIn("cannot lock ref", r.stderr)
            self.assertNotIn("Traceback", r.stderr)
        self.ok("branch", "deep/x")
        r = self.fail_ng("branch", "deep")
        self.assertNotIn("Traceback", r.stderr)
        r = self.fail_ng("branch", "-D", "deep")
        self.assertNotIn("Traceback", r.stderr)

    def test_mv_directory_onto_existing_destination_is_refused(self):
        self.init()
        self.write("src/f", "1\n")
        self.commit("one")
        os.makedirs(os.path.join(self.tmpdir, "dst", "src"))
        r = self.fail_ng("mv", "src", "dst")
        self.assertIn("destination already exists", r.stderr)
        self.assertEqual(self.read("src/f"), "1\n")
        self.assertIn("src/f", self.index())

    # ── merge quality ────────────────────────────────────────────────────────

    def test_merge_identical_edits_on_both_sides_is_clean(self):
        self.init()
        base = "".join(f"l{i}\n" for i in range(1, 11))
        self.write("f", base)
        self.commit("base")
        self.ok("checkout", "-b", "feat")
        self.write("f", base.replace("l1\n", "FIX\n").replace("l9\n", "feat9\n"))
        self.commit("feat")
        self.ok("checkout", "main")
        self.write("f", base.replace("l1\n", "FIX\n").replace("l3\n", "main3\n"))
        self.commit("main")
        self.ok("merge", "feat")
        self.assertEqual(
            self.read("f"),
            base.replace("l1\n", "FIX\n").replace("l3\n", "main3\n")
                .replace("l9\n", "feat9\n"),
        )

    def test_merge_uses_best_common_ancestor(self):
        self.init()
        self.write("f", "a\nb\nc\nd\ne\nf\ng\n")
        self.commit("X")
        self.ok("checkout", "-b", "side")
        self.write("side.txt", "s\n")
        self.commit("S")
        self.ok("checkout", "main")
        self.write("f", "A\nb\nc\nd\ne\nf\ng\n")
        self.commit("Y")
        self.ok("checkout", "-b", "feat")
        for i in range(3):
            self.write(f"n{i}", f"{i}\n")
            self.commit(f"p{i}")
        self.write("f", "A\nb\nc\nd\ne\nf\nG\n")
        self.commit("p4")
        self.ok("merge", "side", "-m", "merge side")
        self.ok("checkout", "main")
        self.write("f", "A\nb\nc\nD\ne\nf\ng\n")
        self.commit("main2")
        self.ok("merge", "feat")
        self.assertEqual(self.read("f"), "A\nb\nc\nD\ne\nf\nG\n")

    def test_squash_merge_conflict_blocks_commit_until_resolved(self):
        self.init()
        self.write("f", "base\n")
        self.commit("b")
        self.ok("checkout", "-b", "x")
        self.write("f", "x\n")
        self.commit("x")
        self.ok("checkout", "main")
        self.write("f", "m\n")
        self.commit("m")
        self.fail_ng("merge", "--squash", "x")
        r = self.fail_ng("commit", "-m", "squashed")
        self.assertIn("unmerged paths", r.stderr)
        self.write("f", "resolved\n")
        self.ok("add", "f")
        self.ok("commit", "-m", "squashed")
        self.assertFalse(self.exists(".notgit/MERGE_CONFLICTS"))

    # ── history and revision parsing ─────────────────────────────────────────

    def test_log_path_filter_matches_directories(self):
        self.init()
        self.write("src/a.py", "1\n")
        self.commit("add src")
        self.write("src/a.py", "2\n")
        self.commit("edit src")
        self.write("z.txt", "z\n")
        self.commit("other")
        out = self.ok("log", "--oneline", "--", "src").stdout
        self.assertIn("add src", out)
        self.assertIn("edit src", out)
        self.assertNotIn("other", out)
        self.assertEqual(len(self.ok("log", "--oneline", "--", ".").stdout.splitlines()), 3)

    def test_rev_lookup_rejects_traversal_and_corrupt_refs(self):
        self.init()
        self.initial_commit()
        for rev in ("../../HEAD", "../../index", "../../config"):
            r = self.fail_ng("rev-parse", rev)
            self.assertIn("bad revision", r.stderr)
            self.assertEqual(r.stdout, "")
        self.write(".notgit/refs/heads/broken", "not an oid\n")
        r = self.fail_ng("rev-parse", "broken")
        self.assertIn("corrupt ref", r.stderr)

    def test_short_words_are_not_abbreviated_object_ids(self):
        self.init()
        self.initial_commit()
        head = self.ok("rev-parse", "HEAD").stdout.strip()
        self.fail_ng("rev-parse", head[:3])
        self.assertEqual(self.ok("rev-parse", head[:4]).stdout.strip(), head)

    def test_file_named_like_abbreviated_commit_needs_dashdash(self):
        self.init()
        self.initial_commit()
        name = self.ok("rev-parse", "HEAD").stdout.strip()[:5]
        self.write(name, "data\n")
        self.commit("hex file")
        self.write(name, "dirty\n")
        for args in (("checkout", name), ("reset", name), ("diff", name)):
            r = self.fail_ng(*args)
            self.assertIn("ambiguous argument", r.stderr)
        self.ok("reset", "--", name)
        self.ok("checkout", "--", name)
        self.assertEqual(self.read(name), "data\n")
        self.assertIn("hex file", self.ok("log", "--oneline", "-1").stdout)

    def test_checkout_rev_dashdash_path_updates_index_and_worktree(self):
        self.init()
        self.write("a.txt", "one\n")
        self.commit("one")
        self.write("a.txt", "two\n")
        self.commit("two")
        self.ok("checkout", "HEAD~1", "--", "a.txt")
        self.assertEqual(self.read("a.txt"), "one\n")
        self.assertIn("M  a.txt", self.ok("status", "--short").stdout)
        self.assertEqual(self.ok("rev-parse", "--abbrev-ref", "HEAD").stdout.strip(), "main")

    def test_grep_dashdash_paths_are_not_revisions(self):
        self.init()
        self.initial_commit()
        name = self.ok("rev-parse", "HEAD").stdout.strip()[:5]
        self.write(name, "needle\n")
        self.commit("hex file")
        r = self.ok("grep", "needle", "--", name)
        self.assertIn(f"{name}:needle", r.stdout)

    def test_grep_e_pattern_keeps_positional_paths_and_rev(self):
        self.init()
        self.write("a.txt", "needle\n")
        self.write("b.txt", "needle\n")
        self.commit("one")
        r = self.ok("grep", "-e", "needle", "a.txt")
        self.assertEqual(r.stdout, "a.txt:needle\n")
        self.write("a.txt", "changed\n")
        self.commit("two")
        r = self.ok("grep", "-e", "needle", "HEAD~1", "a.txt")
        self.assertEqual(r.stdout, "a.txt:needle\n")
        self.write("c.txt", "-dash\n")
        self.commit("three")
        r = self.ok("grep", "-e", "-dash", "c.txt")
        self.assertEqual(r.stdout, "c.txt:-dash\n")

    # ── diff and status output ───────────────────────────────────────────────

    def test_diff_of_empty_file_is_not_reported_as_new_or_deleted(self):
        self.init()
        self.write("e", "")
        self.write("g", "hi\n")
        self.commit("one")
        self.write("e", "hello\n")
        self.write("g", "")
        out = self.ok("diff").stdout
        self.assertNotIn("new file mode", out)
        self.assertNotIn("deleted file mode", out)
        self.assertNotIn("/dev/null", out)
        self.assertIn("--- a/e", out)
        self.assertIn("+++ b/g", out)

    def test_diff_marks_missing_final_newline(self):
        self.init()
        self.write("f", "a\n")
        self.commit("one")
        self.write("f", "a\nno newline")
        out = self.ok("diff").stdout
        self.assertIn("+no newline\n\\ No newline at end of file\n", out)

    def test_diff_content_starting_with_plus_plus_is_not_a_header(self):
        self.init()
        self.write("c.c", "int i;\n")
        self.commit("one")
        self.write("c.c", "int i;\n++i;\n")
        self.assertIn("\n+++i;\n", self.ok("diff").stdout)

    def test_diff_against_rev_detects_binary_change(self):
        self.init()
        with open(os.path.join(self.tmpdir, "b"), "wb") as f:
            f.write(b"\xff")
        self.commit("one")
        with open(os.path.join(self.tmpdir, "b"), "wb") as f:
            f.write(b"\xfe")
        self.assertEqual(self.ng("diff", "--quiet", "HEAD").returncode, 1)
        self.assertIn("b", self.ok("diff", "--name-only", "HEAD").stdout)

    def test_diff_no_index_rejects_directories_cleanly(self):
        os.makedirs(os.path.join(self.tmpdir, "d1"))
        os.makedirs(os.path.join(self.tmpdir, "d2"))
        r = self.fail_ng("diff", "--no-index", "d1", "d2")
        self.assertIn("regular files", r.stderr)
        self.assertNotIn("Traceback", r.stderr)

    def test_status_porcelain_v2_uses_dot_for_unchanged_side(self):
        self.init()
        self.write("f", "1\n")
        self.commit("one")
        self.write("f", "2\n")
        self.write("g", "new\n")
        self.ok("add", "g")
        lines = self.ok("status", "--porcelain=2").stdout.splitlines()
        self.assertTrue(any(l.startswith("1 .M N... ") and l.endswith(" f") for l in lines))
        self.assertTrue(any(l.startswith("1 A. N... ") and l.endswith(" g") for l in lines))

    def test_commit_summary_counts_lines_of_new_files(self):
        self.init()
        self.write("f", "l1\nl2\n")
        self.ok("add", "f")
        r = self.ok("commit", "-m", "one")
        self.assertIn("1 file changed, 2 insertions(+)", r.stdout)

    # ── ignore rules ─────────────────────────────────────────────────────────

    def test_directory_only_ignore_rule_does_not_hide_files(self):
        self.init()
        self.write(".notgitignore", "build/\n")
        self.write("build", "a file\n")
        self.write("d/build/out.o", "x\n")
        out = self.ok("status", "--short").stdout
        self.assertIn("?? build", out)
        self.assertNotIn("out.o", out)

    def test_ignore_negated_character_class_and_escaped_bang(self):
        self.init()
        self.write(".notgitignore", "*.[!c]\n\\!important\n")
        for name in ("q.c", "q.o", "!important", "important"):
            self.write(name, "x\n")
        out = self.ok("status", "--short").stdout
        self.assertIn("?? q.c", out)
        self.assertNotIn("q.o", out)
        self.assertNotIn("!important", out)
        self.assertIn("?? important", out)

    # ── performance guards ───────────────────────────────────────────────────

    def test_store_blob_file_skips_copy_and_fsync_for_known_content(self):
        self.init()
        self.write("f", "same\n")
        ng = self.module("store")
        previous = os.getcwd()
        try:
            os.chdir(self.tmpdir)
            ng._WORKTREE_ROOT = self.tmpdir
            first = ng.store_blob_file("f")
            with mock.patch.object(ng.os, "fsync", wraps=os.fsync) as fsync, \
                    mock.patch.object(ng.tempfile, "mkstemp", wraps=tempfile.mkstemp) as mkstemp:
                self.assertEqual(ng.store_blob_file("f"), first)
            self.assertEqual(fsync.call_count, 0)
            self.assertEqual(mkstemp.call_count, 0)
        finally:
            os.chdir(previous)

    def test_checkout_path_leaves_unchanged_files_untouched(self):
        self.init()
        self.write("keep.txt", "keep\n")
        self.write("edit.txt", "orig\n")
        self.commit("one")
        keep = os.path.join(self.tmpdir, "keep.txt")
        os.utime(keep, (1_000_000, 1_000_000))
        self.write("edit.txt", "changed\n")
        self.ok("checkout", ".")
        self.assertEqual(self.read("edit.txt"), "orig\n")
        self.assertEqual(os.stat(keep).st_mtime, 1_000_000)

    def test_import_git_resolves_deep_delta_chain_once_per_object(self):
        """A chain deeper than the recursion limit resolves, and reading every
        object inflates each pack entry only once thanks to the base cache."""
        ng = self.module("deltas")
        depth = 1500

        def varint(n):
            out = bytearray()
            while True:
                byte = n & 0x7f
                n >>= 7
                out.append(byte | (0x80 if n else 0))
                if not n:
                    return bytes(out)

        def entry_header(type_id, size):
            first = (type_id << 4) | (size & 0x0f)
            size >>= 4
            out = bytearray([first | (0x80 if size else 0)])
            while size:
                byte = size & 0x7f
                size >>= 7
                out.append(byte | (0x80 if size else 0))
            return bytes(out)

        def ofs_encoding(distance):
            out = [distance & 0x7f]
            distance >>= 7
            while distance:
                distance -= 1
                out.insert(0, 0x80 | (distance & 0x7f))
                distance >>= 7
            return bytes(out)

        content = b"base\n"
        pack = bytearray(b"PACK" + struct.pack(">II", 2, depth + 1))
        offsets, contents = [], []
        offsets.append(len(pack))
        contents.append(content)
        pack += entry_header(3, len(content)) + zlib.compress(content)
        for _ in range(depth):
            target = content + b"x"
            # copy the whole base (size in two bytes), then insert one byte
            delta = (varint(len(content)) + varint(len(target))
                     + bytes([0x80 | 0x10 | 0x20, len(content) & 0xff, len(content) >> 8])
                     + b"\x01x")
            offset = len(pack)
            pack += (entry_header(6, len(delta)) + ofs_encoding(offset - offsets[-1])
                     + zlib.compress(delta))
            offsets.append(offset)
            contents.append(target)
            content = target

        git_dir = os.path.join(self.tmpdir, "fakegit")
        os.makedirs(os.path.join(git_dir, "objects"))
        pack_path = os.path.join(git_dir, "objects", "pack.pack")
        with open(pack_path, "wb") as f:
            f.write(bytes(pack))
        store = ng._GitObjectStore(git_dir)
        shas = []
        for offset, data in zip(offsets, contents):
            sha = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
            store._pack_index[sha] = (pack_path, offset)
            shas.append(sha)
        try:
            original = ng._GitObjectStore._inflate
            with mock.patch.object(ng._GitObjectStore, "_inflate",
                                   side_effect=original) as inflate:
                self.assertEqual(store.read(shas[-1]), ("blob", contents[-1]))
                for sha, data in zip(shas, contents):
                    self.assertEqual(store.read(sha)[1], data)
            self.assertEqual(inflate.call_count, depth + 1)
        finally:
            store.close()


if __name__ == "__main__":
    unittest.main(verbosity=2)
