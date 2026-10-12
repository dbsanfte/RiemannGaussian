#!/usr/bin/env python3
"""Check archival input integrity and rejection of an unverified current refresh."""

import copy
import gzip
import json
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


if __name__ == "__main__":
    unittest.main()
