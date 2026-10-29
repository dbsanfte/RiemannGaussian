#!/usr/bin/env python3
"""Reject Lean proof placeholders in tracked working files or the Git index.

This lexical check complements, and does not replace, the compiled declaration
and axiom audits. Comments and literal text are skipped; interpolation terms
and exact escaped identifier names are still checked as code.
"""

from __future__ import annotations

import argparse
from bisect import bisect_right
from dataclasses import dataclass
from pathlib import Path
import re
import subprocess
import sys
import unicodedata


FORBIDDEN = frozenset({"sorry", "admit", "sorryAx"})
FORBIDDEN_BYTES = tuple(token.encode("ascii") for token in FORBIDDEN)
RAW_START = re.compile(r'r(#+)?"')
CHAR_LITERAL = re.compile(r"'(?:[^'\\\n]|\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|[^\n]))'")
# Numeric certificate data is large. Skip ASCII whitespace/numeric punctuation
# in C, but visit every possible identifier, delimiter and non-ASCII character.
CODE_EVENT = re.compile(r'''--|/-|[A-Za-z_"«'{}\u0080-\U0010ffff]''')


@dataclass(frozen=True)
class Finding:
    token: str
    line: int
    column: int


class ScanError(ValueError):
    """A source cannot be scanned safely, for example an unfinished comment."""


def identifier_start(char: str) -> bool:
    return char == "_" or char.isalpha()


def identifier_part(char: str) -> bool:
    return char in "_'!?" or char.isalnum() or unicodedata.category(char).startswith("M")


class LeanScanner:
    def __init__(self, source: str):
        self.source = source
        self.position = 0
        self.newlines = [-1] + [m.start() for m in re.finditer("\n", source)]
        self.findings: list[Finding] = []

    def location(self, position: int) -> tuple[int, int]:
        line = bisect_right(self.newlines, position - 1)
        return line, position - self.newlines[line - 1]

    def error(self, message: str, position: int) -> None:
        line, column = self.location(position)
        raise ScanError(f"{line}:{column}: {message}")

    def check_identifier(self, token: str, position: int) -> None:
        if token in FORBIDDEN:
            line, column = self.location(position)
            self.findings.append(Finding(token, line, column))

    def block_comment(self) -> None:
        start = self.position
        self.position += 2
        depth = 1
        while self.position < len(self.source):
            if self.source.startswith("/-", self.position):
                depth += 1
                self.position += 2
            elif self.source.startswith("-/", self.position):
                depth -= 1
                self.position += 2
                if depth == 0:
                    return
            else:
                self.position += 1
        self.error("unterminated block comment", start)

    def string(self, interpolated: bool) -> None:
        start = self.position
        self.position += 1
        while self.position < len(self.source):
            char = self.source[self.position]
            if char == "\\":
                self.position += 2
            elif char == '"':
                self.position += 1
                return
            elif interpolated and char == "{":
                if self.source.startswith("{{", self.position):
                    self.position += 2
                else:
                    self.position += 1
                    self.code(interpolation=True)
            else:
                self.position += 1
        self.error("unterminated string", start)

    def code(self, interpolation: bool = False) -> None:
        depth = 0
        while self.position < len(self.source):
            event = CODE_EVENT.search(self.source, self.position)
            if event is None:
                self.position = len(self.source)
                break
            self.position = event.start()
            char = self.source[self.position]
            if self.source.startswith("--", self.position):
                end = self.source.find("\n", self.position)
                self.position = len(self.source) if end < 0 else end + 1
            elif self.source.startswith("/-", self.position):
                self.block_comment()
            elif char == "r" and (raw := RAW_START.match(self.source, self.position)):
                start = self.position
                end_marker = '"' + (raw.group(1) or "")
                end = self.source.find(end_marker, raw.end())
                if end < 0:
                    self.error("unterminated raw string", start)
                self.position = end + len(end_marker)
            elif char == '"':
                self.string(self.position > 0 and self.source[self.position - 1] == "!")
            elif char == "«":
                start = self.position
                end = self.source.find("»", start + 1)
                if end < 0:
                    self.error("unterminated escaped identifier", start)
                self.check_identifier(self.source[start + 1:end], start)
                self.position = end + 1
            elif char == "'" and (literal := CHAR_LITERAL.match(self.source, self.position)):
                self.position = literal.end()
            elif identifier_start(char):
                start = self.position
                self.position += 1
                while self.position < len(self.source) and identifier_part(self.source[self.position]):
                    self.position += 1
                self.check_identifier(self.source[start:self.position], start)
            elif interpolation and char == "}":
                self.position += 1
                if depth == 0:
                    return
                depth -= 1
            else:
                if interpolation and char == "{":
                    depth += 1
                self.position += 1
        if interpolation:
            self.error("unterminated string interpolation", self.position)


def find_placeholders(source: str) -> list[Finding]:
    scanner = LeanScanner(source)
    scanner.code()
    return scanner.findings


def git(root: Path, *args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=root)


def sources(root: Path, staged: bool):
    """Stream index blobs through one Git process, never reading working copies."""
    if not staged:
        for raw in git(root, "ls-files", "-z", "--", "*.lean").split(b"\0"):
            if raw:
                name = raw.decode("utf-8")
                path = root / name
                if path.is_symlink():
                    raise ScanError(f"{name}: refusing a symbolic-link Lean source")
                yield name, path.read_bytes()
        return

    entries = []
    for raw in git(root, "ls-files", "--stage", "-z", "--", "*.lean").split(b"\0"):
        if not raw:
            continue
        metadata, name = raw.split(b"\t", 1)
        mode, oid, stage = metadata.split()
        name = name.decode("utf-8")
        if stage != b"0" or mode not in {b"100644", b"100755"}:
            raise ScanError(f"{name}: unresolved or nonregular index entry")
        entries.append((name, oid))
    if not entries:
        return
    with subprocess.Popen(["git", "cat-file", "--batch"], cwd=root,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as process:
        assert process.stdin is not None and process.stdout is not None
        for name, oid in entries:
            process.stdin.write(oid + b"\n")
            process.stdin.flush()
            header = process.stdout.readline().split()
            if len(header) != 3 or header[:2] != [oid, b"blob"]:
                raise ScanError("unexpected Git blob response")
            size = int(header[2])
            content = process.stdout.read(size)
            if len(content) != size or process.stdout.read(1) != b"\n":
                raise ScanError("truncated Git blob response")
            yield name, content
        process.stdin.close()
        code = process.wait()
        if code:
            raise subprocess.CalledProcessError(code, process.args)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--staged", action="store_true", help="scan the Git index, not working copies")
    args = parser.parse_args(argv)
    count, failures = 0, 0
    try:
        root = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"], text=True).strip())
        for name, content in sources(root, args.staged):
            count += 1
            # Generated numerical data can be hundreds of megabytes. An exact
            # forbidden token necessarily contains these literal ASCII bytes.
            # Syntax/encoding validation still belongs to Lean's build gate.
            if not any(token in content for token in FORBIDDEN_BYTES):
                continue
            for hit in find_placeholders(content.decode("utf-8")):
                print(f"{name}:{hit.line}:{hit.column}: forbidden Lean placeholder {hit.token}", file=sys.stderr)
                failures += 1
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"Lean placeholder scan failed: {error}", file=sys.stderr)
        return 2
    if failures:
        return 1
    print(f"Lean placeholder scan passed ({count} {'index' if args.staged else 'tracked'} sources).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
