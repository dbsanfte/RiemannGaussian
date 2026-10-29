#!/usr/bin/env python3
"""Check Git whitespace, preserving only exact hash-pinned historical findings.

Default/--staged checks the index; --commit REV checks that commit against its
first parent (or the empty tree for a root commit). The exception manifest is
read from the same index/commit, never an unstaged working copy. --manifest FILE
explicitly selects a local manifest, for initial verification before staging.
There is deliberately no option to generate or update a baseline.

This is only a whitespace gate. It does not weaken proof, placeholder or axiom
checks. Existing repository .gitattributes rules still apply as in Git's gate.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys


MANIFEST = "docs/research-evidence/semiprime-publication-20261029/preserved-whitespace.json"
WHITESPACE = "blank-at-eol,blank-at-eof,space-before-tab"
MESSAGES = {"trailing whitespace.": "trailing-whitespace", "new blank line at EOF.": "blank-at-eof"}
HEADER = re.compile(r"(.+):([1-9][0-9]*): (trailing whitespace\.|new blank line at EOF\.)")
SHA256 = re.compile(r"[a-f0-9]{64}")


class CheckError(ValueError):
    """An unsafe input, unexpected Git diagnostic or invalid manifest."""


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    kind: str


def valid_path(path: str) -> bool:
    return (isinstance(path, str) and bool(path) and not PurePosixPath(path).is_absolute()
            and all(p not in {".", "..", ""} for p in path.split("/"))
            and not any(c in path for c in "\r\n\0"))


def parse_diagnostics(raw: bytes) -> list[Finding]:
    """Accept only the two preservable Git diagnostics and their exact structure."""
    lines = raw.decode("utf-8").split("\n")
    if lines[-1] == "":
        lines.pop()
    result, i = [], 0
    while i < len(lines):
        match = HEADER.fullmatch(lines[i])
        if not match or not valid_path(match[1]):
            raise CheckError(f"Unrecognized/disallowed Git diagnostic: {lines[i]!r}")
        path, line, message = match.groups()
        result.append(Finding(path, int(line), MESSAGES[message]))
        i += 1
        if message == "trailing whitespace.":
            if i == len(lines) or not lines[i].startswith("+"):
                raise CheckError("Missing added-line payload after trailing-whitespace diagnostic")
            i += 1
    if len(set(result)) != len(result):
        raise CheckError("Duplicate Git whitespace diagnostic")
    return result


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise CheckError(f"Duplicate manifest key: {key}")
        result[key] = value
    return result


def load_manifest(raw: bytes) -> dict[str, dict]:
    value = json.loads(raw, object_pairs_hook=unique_object)
    if not isinstance(value, dict) or type(value.get("schema_version")) is not int or value["schema_version"] != 1:
        raise CheckError("Unsupported whitespace manifest schema")
    if (value.get("policy") != "exact-historical-blob-and-findings"
            or not isinstance(value.get("rationale"), str) or not value["rationale"].strip()):
        raise CheckError("Manifest must explain its exact historical-byte preservation policy")
    entries = value.get("files")
    if not isinstance(entries, list):
        raise CheckError("Manifest files must be a list")
    result = {}
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != {"path", "sha256", "findings"}:
            raise CheckError("Malformed manifest file entry")
        path = entry["path"]
        if not valid_path(path) or path in result:
            raise CheckError(f"Invalid or duplicate manifest path: {path!r}")
        if not isinstance(entry["sha256"], str) or not SHA256.fullmatch(entry["sha256"]):
            raise CheckError(f"Invalid SHA256: {path}")
        findings = entry["findings"]
        if not isinstance(findings, list) or not findings:
            raise CheckError(f"Missing exact findings: {path}")
        seen = set()
        for item in findings:
            if not isinstance(item, dict) or set(item) != {"line", "kind"}:
                raise CheckError(f"Malformed finding: {path}")
            if type(item["line"]) is not int or item["line"] < 1 or item["kind"] not in MESSAGES.values():
                raise CheckError(f"Invalid finding: {path}")
            pair = (item["line"], item["kind"])
            if pair in seen:
                raise CheckError(f"Duplicate manifest finding: {path}")
            seen.add(pair)
        result[path] = entry
    return result


class GitView:
    def __init__(self, root: Path, commit: str | None):
        self.root = root
        self.env = dict(os.environ, LC_ALL="C", LANG="C", GIT_ATTR_NOSYSTEM="1")
        self.revision = None
        self.parent = None
        if commit is not None:
            self.revision = self.run("rev-parse", "--verify", "--end-of-options", commit + "^{commit}").stdout.decode().strip()
            # rev-list hides parents at shallow boundaries. Read the commit
            # header so a missing parent fails closed instead of posing as a
            # root commit. CI needs the checked commit and its first parent.
            header = self.run("cat-file", "-p", self.revision).stdout.split(b"\n\n", 1)[0]
            parents = [line[7:].decode("ascii") for line in header.splitlines() if line.startswith(b"parent ")]
            self.parent = parents[0] if parents else None
        self.entries = None

    def run(self, *args, check=True):
        command = ["git", "-c", "core.whitespace=" + WHITESPACE, "-c", "core.quotePath=false",
                   "-c", "core.attributesFile=" + os.devnull, "-c", "color.ui=false", *args]
        return subprocess.run(command, cwd=self.root, env=self.env, capture_output=True, check=check)

    def whitespace(self) -> list[Finding]:
        options = ["--check", "--no-ext-diff", "--no-textconv", "--no-color", "--no-renames"]
        if self.revision is None:
            result = self.run("diff", "--cached", *options, "--", check=False)
        elif self.parent is None:
            result = self.run("diff-tree", "--root", "--no-commit-id", "-r", *options, self.revision, "--", check=False)
        else:
            result = self.run("diff", *options, self.parent, self.revision, "--", check=False)
        if result.stderr or result.returncode not in {0, 2}:
            raise CheckError(f"Git whitespace check failed ({result.returncode}): {result.stderr.decode(errors='replace')}")
        findings = parse_diagnostics(result.stdout)
        if bool(findings) != (result.returncode == 2):
            raise CheckError("Git whitespace status and diagnostics disagree")
        return findings

    def blob(self, path: str) -> bytes:
        if self.entries is None:
            if self.revision is None:
                raw = self.run("ls-files", "--stage", "-z").stdout
            else:
                raw = self.run("ls-tree", "-r", "-z", self.revision).stdout
            self.entries = {}
            for row in raw.split(b"\0"):
                if not row:
                    continue
                meta, name = row.split(b"\t", 1)
                mode, second, third = meta.decode("ascii").split()
                name = name.decode("utf-8")
                if self.revision is None:
                    if third != "0":
                        raise CheckError(f"Unmerged index entry: {name}")
                    oid = second
                else:
                    if second != "blob":
                        continue
                    oid = third
                self.entries[name] = (mode, oid)
        entry = self.entries.get(path)
        if entry is None or entry[0] not in {"100644", "100755"}:
            raise CheckError(f"Missing or nonregular checked blob: {path}")
        return self.run("cat-file", "blob", entry[1]).stdout


def check_findings(findings: list[Finding], manifest: dict[str, dict], blob) -> list[str]:
    grouped = defaultdict(list)
    for finding in findings:
        grouped[finding.path].append(finding)
    failures = []
    for path, actual in sorted(grouped.items()):
        entry = manifest.get(path)
        if entry is None:
            failures.append(f"{path}: whitespace is not in the historical manifest")
            continue
        if hashlib.sha256(blob(path)).hexdigest() != entry["sha256"]:
            failures.append(f"{path}: checked blob SHA256 differs from preserved historical bytes")
        expected = {(i["line"], i["kind"]) for i in entry["findings"]}
        if {(i.line, i.kind) for i in actual} != expected:
            failures.append(f"{path}: findings differ from the exact historical list")
    return failures


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--staged", action="store_true", help="check the index (default)")
    mode.add_argument("--commit", metavar="REV", help="check this commit against its first parent")
    parser.add_argument("--manifest", type=Path, help="explicit local manifest instead of the checked Git blob")
    args = parser.parse_args(argv)
    try:
        root = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
        view = GitView(root, args.commit)
        manifest = load_manifest(args.manifest.read_bytes() if args.manifest else view.blob(MANIFEST))
        findings = view.whitespace()
        failures = check_findings(findings, manifest, view.blob)
        if failures:
            for failure in failures:
                print(failure, file=sys.stderr)
            return 1
    except (OSError, ValueError, TypeError, subprocess.CalledProcessError) as error:
        print(f"Whitespace check failed: {error}", file=sys.stderr)
        return 2
    print(f"Whitespace check passed ({len(findings)} exact preserved findings; {'commit ' + view.revision if view.revision else 'staged index'}).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
