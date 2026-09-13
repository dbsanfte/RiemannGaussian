#!/usr/bin/env python3
"""Scheduler failure and partition tests; no simulated run is a Lean proof."""
from contextlib import ExitStack, redirect_stdout, redirect_stderr
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify_numerical_certificate as driver


PREFIX = "RiemannGaussian.CertificateData."
COVER = PREFIX + "MontgomeryTaylorCover"


class SchedulerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.output = self.root / "result"
        self.manifest = self.root / "manifest.json"
        self.groups = [{"module": f"{COVER}.Group{i:04d}", "nodes": 3 + 2 * i,
                        "anchorLeaves": i} for i in range(12)]
        self.manifest.write_text(json.dumps({"groups": self.groups}))
        self.a, self.b, self.c = [PREFIX + name for name in ("Phase", "Ranges", "Anchors")]
        self.after = PREFIX + "AfterCover"
        self.imports = {
            self.a: {self.a}, self.b: {self.a, self.b}, self.c: {self.a, self.b, self.c},
            self.after: {self.a, self.after, self.groups[0]["module"]},
        }
        self.optional = dict.fromkeys([*self.imports, COVER, *(g["module"] for g in self.groups)])
        self.calls = []

    def context(self, codes=None, fingerprints=None, emit_report=True):
        stack = ExitStack()
        stack.enter_context(patch.object(driver, "ROOT", self.root))
        stack.enter_context(patch.object(driver, "MANIFEST", self.manifest))
        stack.enter_context(patch.object(driver, "config", return_value={"heavyModulePrefix": PREFIX}))
        stack.enter_context(patch.object(driver, "partition", return_value=({}, self.optional)))
        stack.enter_context(patch.object(driver, "closure", side_effect=lambda n: self.imports[n]))
        stack.enter_context(patch.object(driver, "lake_command", return_value=(["fixture-lake"], {})))
        if fingerprints is None:
            stack.enter_context(patch.object(driver, "fingerprint", return_value="fixture-input-digest"))
        else:
            stack.enter_context(patch.object(driver, "fingerprint", side_effect=fingerprints))
        calls = self.calls
        pending_codes = iter(codes) if codes is not None else None
        raw_audit = self.root / ".lake/numerical-certificate/audit.json"

        class FixtureProcess:
            def __init__(self, command, **kwargs):
                calls.append(command)
                self.command = command
                self.pid = 1000 + len(calls)

            def wait(self, timeout):
                code = next(pending_codes) if pending_codes is not None else 0
                if code == 0 and emit_report and self.command[-1].endswith("AuditNumericalCertificate.lean"):
                    raw_audit.parent.mkdir(parents=True, exist_ok=True)
                    raw_audit.write_text(json.dumps({"fixtureReport": True}))
                return code

        stack.enter_context(patch.object(driver.subprocess, "Popen", FixtureProcess))
        stack.enter_context(redirect_stdout(io.StringIO()))
        stack.enter_context(redirect_stderr(io.StringIO()))
        return stack

    def run_driver(self, args=(), **kwargs):
        with self.context(**kwargs), patch("sys.argv", ["verify", "--jobs", "2", "--output",
                                                        str(self.output), *args]):
            driver.main()
        return json.loads((self.output / "progress.json").read_text())

    def test_shards_cover_every_group_once(self):
        for count in range(1, 18):
            parts = [driver.select_groups(self.groups, i, count) for i in range(count)]
            modules = [g["module"] for part in parts for g in part]
            self.assertEqual(len(modules), len(set(modules)))
            self.assertEqual(set(modules), {g["module"] for g in self.groups})

    def test_data_dependencies_are_built_before_dependents(self):
        with self.context():
            batches = driver.prerequisite_batches(self.optional, self.groups, 2)
        built = set()
        for batch in batches:
            self.assertLessEqual(len(batch), 2)
            for name in batch:
                self.assertLessEqual(self.imports[name] - {name}, built)
            built.update(batch)
        self.assertEqual(built, {self.a, self.b, self.c})
        self.assertNotIn(self.after, built)

    def test_data_cycle_is_rejected(self):
        self.imports[self.a].add(self.b)
        with self.context(), self.assertRaisesRegex(ValueError, "cycle"):
            driver.prerequisite_batches(self.optional, self.groups, 2)

    def test_partial_shard_never_runs_final_assembly_or_audit(self):
        state = self.run_driver(["--groups-only", "--shard-count", "3", "--shard-index", "1"])
        self.assertEqual(state["state"], "passed")
        self.assertEqual(state["stage"], "pieces-only")
        self.assertEqual(state["totalGroups"], 12)
        self.assertEqual(state["selectedGroups"], 4)
        self.assertEqual(state["verifiedGroups"], 4)
        self.assertEqual(state["verifiedNodesInPieces"], sum(g["nodes"] for g in self.groups[1::3]))
        self.assertEqual(state["verifiedAnchorLeaves"], sum(g["anchorLeaves"] for g in self.groups[1::3]))
        selected = [a for call in self.calls for a in call if a.startswith(COVER)]
        self.assertEqual(selected, [g["module"] for g in self.groups[1::3]])
        self.assertFalse(any("NumericalCertificate" in c for c in self.calls))
        self.assertFalse(any("env" in c for c in self.calls))

    def test_prerequisite_only_run_does_not_build_cover(self):
        state = self.run_driver(["--data-only"])
        self.assertEqual(state["stage"], "data-only")
        self.assertEqual(state["verifiedDataModules"], 3)
        self.assertEqual(state["verifiedGroups"], 0)
        self.assertEqual(state["selectedGroups"], 0)
        self.assertFalse(any(a.startswith(COVER) for call in self.calls for a in call))

    def test_complete_run_requires_assembly_and_axiom_audit(self):
        state = self.run_driver()
        self.assertEqual(state["stage"], "complete-selected-target")
        self.assertEqual(state["verifiedGroups"], 12)
        self.assertEqual(self.calls[-2], ["fixture-lake", "build", "NumericalCertificate", "--wfail"])
        self.assertEqual(self.calls[-1], ["fixture-lake", "env", "lean", "-DwarningAsError=true",
                                          "scripts/AuditNumericalCertificate.lean"])
        report = json.loads((self.output / "audit.json").read_text())
        self.assertEqual(report["inputSha256"], "fixture-input-digest")

    def test_failed_group_cannot_produce_passed_state(self):
        with self.assertRaisesRegex(RuntimeError, "Lean verification failed"):
            self.run_driver(["--groups-only"], codes=[0, 0, 0, 1])
        state = json.loads((self.output / "progress.json").read_text())
        self.assertEqual(state["state"], "failed")
        self.assertEqual(state["verifiedGroups"], 0)
        self.assertFalse((self.output / "input-sha256.txt").exists())

    def test_failed_final_audit_cannot_produce_passed_state(self):
        with self.assertRaisesRegex(RuntimeError, "Lean verification failed"):
            self.run_driver(codes=[0] * 10 + [1])
        state = json.loads((self.output / "progress.json").read_text())
        self.assertEqual(state["state"], "failed")
        self.assertEqual(state["stage"], "axiom-audit")
        self.assertFalse((self.output / "input-sha256.txt").exists())

    def test_input_change_rejects_completed_piece_checks(self):
        with self.assertRaisesRegex(RuntimeError, "inputs changed"):
            self.run_driver(["--groups-only"], fingerprints=["before", "after"])
        state = json.loads((self.output / "progress.json").read_text())
        self.assertEqual(state["state"], "interrupted-or-failed")
        self.assertFalse((self.output / "input-sha256.txt").exists())

    def test_shard_cannot_claim_complete_target(self):
        with self.assertRaises(SystemExit) as error:
            self.run_driver(["--shard-count", "3", "--shard-index", "1"])
        self.assertEqual(error.exception.code, 2)
        self.assertEqual(self.calls, [])

    def test_failed_rerun_removes_stale_success_reports(self):
        self.output.mkdir()
        for name in ["input-sha256.txt", "audit.json"]:
            (self.output / name).write_text("stale fixture success")
        raw_audit = self.root / ".lake/numerical-certificate/audit.json"
        raw_audit.parent.mkdir(parents=True)
        raw_audit.write_text("stale fixture success")
        with self.assertRaisesRegex(RuntimeError, "Lean verification failed"):
            self.run_driver(codes=[1])
        self.assertFalse((self.output / "input-sha256.txt").exists())
        self.assertFalse((self.output / "audit.json").exists())
        self.assertFalse(raw_audit.exists())

    def test_missing_audit_report_is_not_complete(self):
        with self.assertRaisesRegex(RuntimeError, "without its report"):
            self.run_driver(emit_report=False)
        state = json.loads((self.output / "progress.json").read_text())
        self.assertEqual(state["state"], "interrupted-or-failed")
        self.assertFalse((self.output / "input-sha256.txt").exists())

    def test_input_change_after_audit_removes_its_success_report(self):
        with self.assertRaisesRegex(RuntimeError, "inputs changed"):
            self.run_driver(fingerprints=["before", "before", "after"])
        self.assertFalse((self.output / "audit.json").exists())
        self.assertFalse((self.root / ".lake/numerical-certificate/audit.json").exists())

    def test_separate_partial_run_preserves_another_full_audit(self):
        raw_audit = self.root / ".lake/numerical-certificate/audit.json"
        raw_audit.parent.mkdir(parents=True)
        raw_audit.write_text("separate existing fixture report")
        self.run_driver(["--groups-only"])
        self.assertEqual(raw_audit.read_text(), "separate existing fixture report")
        self.assertFalse((self.output / "audit.json").exists())


if __name__ == "__main__":
    unittest.main()
