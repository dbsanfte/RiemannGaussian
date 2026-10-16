#!/usr/bin/env python3
"""Check archival input integrity and rejection of an unverified current refresh."""

import copy
import gzip
import json
import os
import tempfile
import unittest
from unittest.mock import patch

import build_numerical_certificate_explorer as certificate
import numerical_certificate_checkpoint as checkpoint


class CertificateCheckpointTests(unittest.TestCase):
    def test_recorded_inputs_replay(self):
        overrides, manifest = checkpoint.checked_inputs()
        self.assertIn("lean-toolchain", overrides)
        self.assertEqual(overrides["lean-toolchain"].decode().strip(), "leanprover/lean4:v4.33.1")
        self.assertTrue(manifest["packages"])

    def test_modified_frozen_source_is_rejected(self):
        archive = json.loads(gzip.decompress((checkpoint.SITE / "lean433-inputs.json.gz").read_bytes()))
        archive = copy.deepcopy(archive)
        name = next(name for name in archive["archivedText"] if name.endswith(".lean"))
        archive["archivedText"][name] += "\n-- changed\n"
        with self.assertRaisesRegex(AssertionError, "Historical input changed"):
            checkpoint.checked_inputs(archive=archive)

    def test_archive_cannot_approve_current_refresh(self):
        with patch.object(certificate, "fingerprint", return_value="unverified-current-inputs"):
            with self.assertRaisesRegex(AssertionError, "rerun optional verification"):
                certificate.checked_audit(require_current=True)

    def test_historical_core_source_links_without_installed_toolchain(self):
        warm = certificate.build()
        with tempfile.TemporaryDirectory() as empty_elan:
            with patch.dict(os.environ, {"ELAN_HOME": empty_elan}):
                cold = certificate.build()
        self.assertEqual(cold, warm)
        data = json.loads(cold["data.js"].split(b"window.PROOF_DATA=", 1)[1].removesuffix(b";\n"))
        nodes = {node["id"]: node for node in data["nodes"]}
        raw = json.loads(gzip.decompress((certificate.SITE / "lean-graph.json.gz").read_bytes()))
        checked = 0
        for node in raw["nodes"]:
            location = node["location"]
            module = (location or {}).get("module") or node["module"] or ""
            if not location or module.split(".", 1)[0] not in {"Init", "Lean", "Std"}:
                continue
            path = module.replace(".", "/") + ".lean"
            self.assertEqual(nodes[node["id"]]["source"], {
                "url": f"https://github.com/leanprover/lean4/blob/v{raw['leanVersion']}/src/{path}#L{location['line']}",
                "path": path, "line": location["line"],
                "exact": location["exact"], "project": False,
            })
            checked += 1
        self.assertGreater(checked, 0, "The frozen graph must exercise compiler source links")


if __name__ == "__main__":
    unittest.main()
