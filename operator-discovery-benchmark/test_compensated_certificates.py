"""Negative tests for infinite-case coverage and publication integrity."""
from contextlib import redirect_stdout
import copy
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_compensated_gap_family as checker
import compensated_shift_report as report

BASE = Path(__file__).resolve().parent
FAMILY = BASE / "compensated-shift-results/family-gap-run-001"


class CertificateIntegrity(unittest.TestCase):
    def audit_mutation(self, mutate):
        """Exercise the independent mathematical checker with damaged evidence."""
        with tempfile.TemporaryDirectory(prefix="signed-certificate-test-") as dirname:
            destination = Path(dirname)
            for name in ("protocol.json", "candidate_batch.json", "family_gap_search.json"):
                value = json.loads((FAMILY / name).read_text())
                if name == "family_gap_search.json": mutate(value)
                (destination / name).write_text(json.dumps(value))
            with patch.object(checker, "DEST", destination), redirect_stdout(io.StringIO()):
                with self.assertRaises(AssertionError): checker.main()
            self.assertFalse((destination / "family_gap_verification.json").exists())

    def test_missing_inequality_side_is_rejected(self):
        def mutate(value):
            region = next(r for r in value["records"][0]["finite_simplex_regions"] if "sides" in r)
            region["sides"] = region["sides"][:1]
        self.audit_mutation(mutate)

    def test_duplicate_inequality_side_is_rejected(self):
        def mutate(value):
            region = next(r for r in value["records"][0]["finite_simplex_regions"] if "sides" in r)
            region["sides"] = [region["sides"][0], copy.deepcopy(region["sides"][0])]
        self.audit_mutation(mutate)

    def test_missing_infinite_tail_is_rejected(self):
        self.audit_mutation(lambda value: value["records"][0]["uniform_tails"].pop())

    def test_missing_residual_region_is_rejected(self):
        self.audit_mutation(lambda value: value["records"][0]["finite_simplex_regions"].pop())

    def test_published_formula_proof_change_is_rejected(self):
        original_sha = report.sha
        def changed(path):
            return "0" * 64 if Path(path).name == "compensated_shift_proof.txt" else original_sha(path)
        with patch.object(report, "sha", changed), self.assertRaisesRegex(ValueError, "dependency changed"):
            report.summary(FAMILY)

    def test_published_uncertified_family_change_is_rejected(self):
        original_sha = report.sha
        def changed(path):
            return "0" * 64 if Path(path).name == "family_gap_search.json" else original_sha(path)
        with patch.object(report, "sha", changed), self.assertRaisesRegex(ValueError, "audit source changed"):
            report.summary(FAMILY)

    def test_verified_catalogue_preserves_scope_and_automatic_selection(self):
        value = report.summary(FAMILY)
        self.assertEqual((len(value["proved_global_estimates"]), len(value["counterexamples"]), len(value["numerical_leads"])), (7, 10, 4))
        best = value["automatically_selected_operator"]
        self.assertEqual((best["left"], best["right"], best["composite_absolute_bound"]), ("1/3", "5/7", "2/39"))
        self.assertFalse(value["attributed_to_autonomous_generic_grammar"])
        self.assertFalse(value["new_independent_prime_distribution_estimate_proved"])
        self.assertFalse(value["new_RH_estimate_proved"])
        self.assertEqual(value["verified_new_operators"], [])

    def test_native_evidence_belongs_to_the_selected_parameters(self):
        value = report.summary(FAMILY)
        winner = value["automatic_winner_native_zeta_audit"]
        self.assertEqual(winner["status"], "independently_verified")
        self.assertEqual((winner["left"], winner["right"], winner["groups"]), ("1/3", "5/7", 2))
        self.assertTrue(winner["post_selection_fresh_cases"])
        self.assertTrue(winner["evaluation_does_not_reselect_or_adapt"])
        representative = value["complete_native_zeta_audit"]
        self.assertEqual((representative["left"], representative["right"], representative["groups"]), ("1/3", "2/3", 2))
        self.assertFalse(value["main_registry_counts_changed"])


if __name__ == "__main__": unittest.main()
