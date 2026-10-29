#!/usr/bin/env python3
"""Focused lexical and real-index tests for the Lean placeholder gate."""

from pathlib import Path
from contextlib import redirect_stdout
import io
import os
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

import check_lean_placeholders as check


SCANNER = Path(check.__file__).resolve()


class LeanLexicalTest(unittest.TestCase):
    def tokens(self, text):
        return [hit.token for hit in check.find_placeholders(text)]

    def test_actual_placeholders_and_qualified_constant(self):
        self.assertEqual(self.tokens("theorem a : True := by sorry\nby admit\nexact Lean.sorryAx _ true"),
                         ["sorry", "admit", "sorryAx"])

    def test_exact_identifier_boundaries(self):
        self.assertEqual(self.tokens("admitted sorryAxCount _sorry αsorry sorry₂ sorry' sorry?"), [])
        self.assertEqual(self.tokens("foo.sorryAx"), ["sorryAx"])
        self.assertEqual(self.tokens("[12345, 67890]; by sorry"), ["sorry"])

    def test_english_docstrings_and_line_comments(self):
        self.assertEqual(self.tokens("/-- All words admit a cap. -/\ndef x := 1 -- sorry admit sorryAx\n"), [])

    def test_nested_block_comments(self):
        text = "/- outer sorry /- nested admit /- sorryAx -/ -/ still admit -/\nby sorry"
        self.assertEqual(self.tokens(text), ["sorry"])

    def test_strings_escaped_quotes_and_comment_markers(self):
        self.assertEqual(self.tokens(r'"sorry \\" by admit'), ["admit"])
        self.assertEqual(self.tokens(r'"sorry \" admit /- sorryAx -/"'), [])
        self.assertEqual(self.tokens('"-- admit"\nby sorry'), ["sorry"])

    def test_raw_strings(self):
        self.assertEqual(self.tokens('r###"sorry "# admit /- sorryAx -/"###\nby admit'), ["admit"])
        self.assertEqual(self.tokens('r"sorry"\nby sorry'), ["sorry"])

    def test_interpolation_terms_are_code(self):
        self.assertEqual(self.tokens('s!"text sorry {by admit}"'), ["admit"])
        self.assertEqual(self.tokens('m!"{{sorry}} {({ x := by sorry })}"'), ["sorry"])
        self.assertEqual(self.tokens('s!"{s!"literal {by sorry}"}"'), ["sorry"])
        self.assertEqual(self.tokens('s!"{ /- } sorry -/ by admit }"'), ["admit"])

    def test_interpolated_literal_escaped_braces(self):
        self.assertEqual(self.tokens('s!"{{admit}} {{sorryAx}} {1}"'), [])

    def test_escaped_identifiers(self):
        self.assertEqual(self.tokens('Lean.«sorryAx» «admit» «sorry»'), ["sorryAx", "admit", "sorry"])
        self.assertEqual(self.tokens('«all words admit spaces» «sorryAxCount»'), [])

    def test_characters_and_apostrophes(self):
        self.assertEqual(self.tokens("'s' '\\'' '\\u0073' foo' sorry'"), [])
        self.assertEqual(self.tokens("'}' by admit"), ["admit"])

    def test_source_locations(self):
        hits = check.find_placeholders('/- admit -/\n  by sorry\n«sorryAx»')
        self.assertEqual([(h.token, h.line, h.column) for h in hits],
                         [("sorry", 2, 6), ("sorryAx", 3, 1)])

    def test_unfinished_lexemes_fail_closed(self):
        for text in ['/- admit', '"sorry', 'r##"admit"#', '«sorry', 's!"{by sorry']:
            with self.subTest(text=text), self.assertRaises(check.ScanError):
                check.find_placeholders(text)

    def test_cli_skips_lexing_irrelevant_large_numeric_data(self):
        content = b"def values : List Nat := [" + b"0, " * 500000 + b"0]\n"
        with patch.object(check, "sources", return_value=iter([("numeric.lean", content)])), \
                patch.object(check, "find_placeholders") as lexer, redirect_stdout(io.StringIO()):
            self.assertEqual(check.main([]), 0)
            lexer.assert_not_called()


class GitIndexTest(unittest.TestCase):
    def setUp(self):
        # Hooks can export their real staged index. Every fixture process must
        # discover only its temporary repository, never mutate that real index.
        self.environment = os.environ.copy()
        names = subprocess.check_output(["git", "rev-parse", "--local-env-vars"],
                                        cwd=SCANNER.parent, text=True)
        for name in names.splitlines():
            self.environment.pop(name, None)

    def run_process(self, args, root, **kwargs):
        return subprocess.run(args, cwd=root, env=self.environment, **kwargs)

    def test_index_and_working_copy_are_distinct(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.run_process(["git", "init", "--quiet"], root, check=True)
            source = root / "with spaces.lean"
            source.write_text('/-- These bounds admit all inputs. -/\ntheorem t : True := by trivial\n')
            (root / "numeric.lean").write_bytes(b"def xs := [" + b"0, " * 100000 + b"0]\n")
            self.run_process(["git", "add", source.name, "numeric.lean"], root, check=True)
            source.write_text("theorem t : True := by sorry\n")
            staged = self.run_process([sys.executable, str(SCANNER), "--staged"], root, capture_output=True, text=True)
            working = self.run_process([sys.executable, str(SCANNER)], root, capture_output=True, text=True)
            self.assertEqual(staged.returncode, 0, staged.stderr)
            self.assertEqual(working.returncode, 1, working.stderr)
            self.assertIn("with spaces.lean:1:24", working.stderr)
            self.run_process(["git", "add", source.name], root, check=True)
            source.write_text("theorem t : True := by trivial\n")
            staged = self.run_process([sys.executable, str(SCANNER), "--staged"], root, capture_output=True, text=True)
            working = self.run_process([sys.executable, str(SCANNER)], root, capture_output=True, text=True)
            self.assertEqual(staged.returncode, 1, staged.stderr)
            self.assertEqual(working.returncode, 0, working.stderr)

    def test_untracked_sources_are_not_silently_included(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self.run_process(["git", "init", "--quiet"], root, check=True)
            (root / "draft.lean").write_text("by sorry\n")
            result = self.run_process([sys.executable, str(SCANNER)], root, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("0 tracked sources", result.stdout)


if __name__ == "__main__":
    unittest.main()
