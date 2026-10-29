#!/usr/bin/env python3
"""Exact historical exceptions and real staged/commit whitespace checks."""

import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

import check_staged_whitespace as check


SCRIPT = Path(check.__file__).resolve()


def manifest(entries=()):
    return {"schema_version": 1, "policy": "exact-historical-blob-and-findings",
            "rationale": "Preserve exact historical fixture bytes; never future changes.", "files": list(entries)}


class DiagnosticTests(unittest.TestCase):
    def test_exact_known_diagnostics_and_crlf_payload(self):
        raw = b"folder/a: name.txt:2: trailing whitespace.\n+raw CRLF\r\nfolder/a: name.txt:4: new blank line at EOF.\n"
        self.assertEqual(check.parse_diagnostics(raw), [check.Finding("folder/a: name.txt", 2, "trailing-whitespace"),
                                                     check.Finding("folder/a: name.txt", 4, "blank-at-eof")])

    def test_unknown_malformed_and_conflict_diagnostics_fail_closed(self):
        for raw in [b"a:1: leftover conflict marker\n+<<<<<<< branch\n", b"a:1: space before tab in indent.\n+ \tx\n",
                    b"a:1: trailing whitespace.\n", b"a:0: trailing whitespace.\n+x \n", b"garbage\n",
                    b"a:1: new blank line at EOF.\n+extra\n", b"\xff:1: trailing whitespace.\n+x \n"]:
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                check.parse_diagnostics(raw)

    def test_manifest_rejects_duplicate_keys_paths_and_disallowed_kinds(self):
        with self.assertRaises(ValueError):
            check.load_manifest(b'{"schema_version":1,"schema_version":1}')
        entry = {"path": "a", "sha256": "0" * 64, "findings": [{"line": 1, "kind": "trailing-whitespace"}]}
        for entries in [[entry, entry], [{**entry, "path": "../a"}], [{**entry, "sha256": "unknown"}],
                        [{**entry, "findings": [{"line": 1, "kind": "leftover-conflict-marker"}]}],
                        [{**entry, "findings": [{"line": True, "kind": "trailing-whitespace"}]}]]:
            with self.subTest(entries=entries), self.assertRaises(ValueError):
                check.load_manifest(json.dumps(manifest(entries)).encode())


class GitTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.env = os.environ.copy()
        # Hook execution may export the real repository's index. Every fixture
        # must use its own repository/index, including the subprocess checker.
        for name in subprocess.check_output(["git", "rev-parse", "--local-env-vars"], cwd=SCRIPT.parent, text=True).splitlines():
            self.env.pop(name, None)
        self.env.update(LC_ALL="C", LANG="C", GIT_CONFIG_NOSYSTEM="1")
        self.git("init", "--quiet")
        self.git("config", "user.name", "Whitespace fixture")
        self.git("config", "user.email", "fixture@example.invalid")
        self.git("config", "core.hooksPath", str(self.root / "no-hooks"))
        self.write_manifest()

    def git(self, *args, **kwargs):
        return subprocess.run(["git", *args], cwd=self.root, env=self.env, capture_output=True, check=True, **kwargs)

    def put(self, name, content, stage=True):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        if stage:
            self.git("add", "--", name)

    def write_manifest(self, entries=(), stage=True):
        self.put(check.MANIFEST, (json.dumps(manifest(entries), indent=2) + "\n").encode(), stage)

    def entry(self, name, findings):
        return {"path": name, "sha256": hashlib.sha256(self.git("show", ":" + name).stdout).hexdigest(),
                "findings": [{"line": line, "kind": kind} for line, kind in findings]}

    def cli(self, *args):
        return subprocess.run([sys.executable, str(SCRIPT), *args], cwd=self.root, env=self.env,
                              capture_output=True, text=True)

    def assert_pass(self, *args):
        result = self.cli(*args)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def assert_fail(self, text=None, *args):
        result = self.cli(*args)
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        if text:
            self.assertIn(text, result.stderr)

    def test_clean_index_and_default_staged_mode(self):
        self.put("clean.txt", b"clean\n")
        self.assert_pass()
        self.assert_pass("--staged")

    def test_exact_historical_blob_and_both_finding_types_allowed(self):
        self.put("with spaces: fixture.txt", b"historic \n\n")
        self.write_manifest([self.entry("with spaces: fixture.txt", [(1, "trailing-whitespace"), (2, "blank-at-eof")])])
        self.assert_pass()

    def test_changed_blob_rejected_even_when_diagnostics_identical(self):
        self.put("a", b"old \n")
        self.write_manifest([self.entry("a", [(1, "trailing-whitespace")])])
        self.put("a", b"new \n")
        self.assert_fail("SHA256 differs")

    def test_new_file_and_new_finding_rejected(self):
        self.put("a", b"old \n")
        self.write_manifest([self.entry("a", [(1, "trailing-whitespace")])])
        self.put("new", b"bad \n")
        self.assert_fail("not in the historical manifest")
        self.git("rm", "--cached", "--", "new")
        self.put("a", b"old \nextra \n")
        self.assert_fail("findings differ")

    def test_exact_finding_list_required_independently_of_hash(self):
        self.put("a", b"old \n")
        self.write_manifest([self.entry("a", [(2, "trailing-whitespace")])])
        self.assert_fail("findings differ")

    def test_conflict_markers_never_preserved_by_matching_blob_hash(self):
        for marker in [b"<<<<<<< ours", b"=======", b">>>>>>> theirs"]:
            with self.subTest(marker=marker):
                self.put("a", marker + b"\n")
                self.write_manifest([self.entry("a", [(1, "trailing-whitespace")])])
                self.assert_fail("Unrecognized/disallowed Git diagnostic")

    def test_index_not_worktree_controls_findings_and_hashes(self):
        self.put("a", b"staged bad \n")
        self.put("a", b"working clean\n", stage=False)
        self.assert_fail("not in the historical manifest")
        self.put("a", b"staged clean\n")
        self.put("a", b"working bad \n", stage=False)
        self.assert_pass()
        self.put("a", b"preserved \n")
        self.write_manifest([self.entry("a", [(1, "trailing-whitespace")])])
        self.put("a", b"different working bytes \n", stage=False)
        self.assert_pass()

    def test_manifest_also_comes_from_index_unless_explicitly_overridden(self):
        self.put("a", b"old \n")
        entry = self.entry("a", [(1, "trailing-whitespace")])
        self.write_manifest([entry], stage=False)
        self.assert_fail("not in the historical manifest")
        self.assert_pass("--manifest", check.MANIFEST)
        self.write_manifest([entry])
        self.write_manifest([], stage=False)
        self.assert_pass()

    def test_external_whitespace_configuration_cannot_disable_checks(self):
        self.git("config", "core.whitespace", "-blank-at-eol,-blank-at-eof,-space-before-tab,cr-at-eol")
        attributes = self.root / "external-attributes"
        attributes.write_text("* -whitespace\n")
        self.git("config", "core.attributesFile", str(attributes))
        self.put("crlf.csv", b"column\r\n")
        self.assert_fail("not in the historical manifest")
        self.put("space-before-tab", b" \ttext\n")
        self.assert_fail("Unrecognized/disallowed Git diagnostic")

    def test_root_commit_and_followup_commit_use_their_own_blobs(self):
        self.put("a", b"historic \n")
        self.write_manifest([self.entry("a", [(1, "trailing-whitespace")])])
        self.git("commit", "--quiet", "-m", "exact historical root")
        self.assert_pass("--commit", "HEAD")
        self.put("a", b"working and staged changes \n")
        self.write_manifest([])
        self.assert_pass("--commit", "HEAD")
        self.git("commit", "--quiet", "-m", "unlisted new whitespace")
        self.assert_fail("not in the historical manifest", "--commit", "HEAD")

    def test_existing_parent_commit_checked_not_clean_index(self):
        self.put("clean", b"baseline\n")
        self.git("commit", "--quiet", "-m", "clean base")
        self.put("historical", b"preserved \n")
        self.write_manifest([self.entry("historical", [(1, "trailing-whitespace")])])
        self.git("commit", "--quiet", "-m", "preserved publication")
        self.assert_pass("--commit", "HEAD")
        self.put("historical", b"new \n")
        self.git("commit", "--quiet", "-m", "changed exception bytes")
        self.assert_fail("SHA256 differs", "--commit", "HEAD")

    def test_shallow_boundary_is_not_misidentified_as_root_commit(self):
        self.put("older", b"older unlisted whitespace \n")
        self.git("commit", "--quiet", "-m", "older history outside this check")
        self.put("new", b"clean new change\n")
        self.git("commit", "--quiet", "-m", "checked commit")
        (self.root / ".git/shallow").write_bytes(self.git("rev-parse", "HEAD").stdout)
        self.assert_pass("--commit", "HEAD")

    def test_missing_manifest_and_unknown_revision_fail_closed(self):
        self.git("rm", "--cached", "--", check.MANIFEST)
        self.assert_fail("Missing or nonregular checked blob")
        self.assert_fail(None, "--commit", "does-not-exist")


if __name__ == "__main__":
    unittest.main(verbosity=2)
