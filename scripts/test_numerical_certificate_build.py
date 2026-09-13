#!/usr/bin/env python3
"""Regression checks for opt-in imports and certificate cache invalidation."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import numerical_certificate as build


class CertificateBuildTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.write("docs/numerical-certificate.json", json.dumps({
            "defaultTarget": "RiemannGaussian", "optionalTarget": "NumericalCertificate",
            "heavyModulePrefix": "RiemannGaussian.CertificateData."}))
        self.write("lakefile.toml", 'defaultTargets = ["RiemannGaussian"]\n')
        self.write("RiemannGaussian.lean", "import RiemannGaussian.Core\n")
        self.write("RiemannGaussian/Core.lean", "import RiemannGaussian.Shared\n")
        self.write("RiemannGaussian/Shared.lean", "-- shared analytic proof\n")
        self.write("NumericalCertificate.lean", "import RiemannGaussian.CertificateData.Bounds\n")
        self.write("RiemannGaussian/CertificateData/Bounds.lean", "import RiemannGaussian.Shared\n")
        for name in ("lean-toolchain", "lake-manifest.json", "vendor/zeta23/lakefile.toml",
                     "vendor/zeta23/lake-manifest.json", "scripts/numerical_certificate.py",
                     "scripts/verify_numerical_certificate.py", "scripts/generate_montgomery_taylor_cover.py",
                     "RiemannGaussian/CertificateData/MontgomeryTaylorCover/manifest.json",
                     "certificates/seven-window/cover-proposal.json.gz",
                     "scripts/test_numerical_certificate_build.py",
                     "scripts/test_numerical_certificate_build_config.py",
                     "scripts/test_numerical_certificate_scheduler.py",
                     "scripts/test_numerical_certificate_audit.py",
                     "scripts/AuditNumericalCertificate.lean",
                     ".github/workflows/numerical_certificate.yml"):
            self.write(name, "pinned input\n")
        for name, value in (("ROOT", self.root), ("CONFIG", self.root / "docs/numerical-certificate.json")):
            patcher = patch.object(build, name, value)
            patcher.start()
            self.addCleanup(patcher.stop)

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    def test_unrelated_proof_preserves_cache_but_shared_proof_invalidates(self):
        before = build.fingerprint()
        self.write("RiemannGaussian/Core.lean", "import RiemannGaussian.Shared\n-- new core-only proof\n")
        self.assertEqual(before, build.fingerprint())
        self.write("RiemannGaussian/Shared.lean", "-- changed shared proof\n")
        self.assertNotEqual(before, build.fingerprint())

    def test_data_and_dependency_pins_invalidate_cache(self):
        for name in ("RiemannGaussian/CertificateData/Bounds.lean", "lean-toolchain",
                     "lake-manifest.json", "scripts/AuditNumericalCertificate.lean",
                     "scripts/test_numerical_certificate_build.py",
                     "scripts/test_numerical_certificate_build_config.py",
                     "scripts/test_numerical_certificate_scheduler.py",
                     "scripts/test_numerical_certificate_audit.py"):
            with self.subTest(name=name):
                before = build.fingerprint()
                path = self.root / name
                path.write_text(path.read_text() + "\n-- changed input\n")
                self.assertNotEqual(before, build.fingerprint())

    def test_transitive_default_import_of_data_is_rejected(self):
        self.write("RiemannGaussian/Shared.lean", "import RiemannGaussian.CertificateData.Bounds\n")
        with self.assertRaisesRegex(ValueError, "Default build imports exhaustive"):
            build.partition()

    def test_unregistered_module_is_rejected(self):
        self.write("RiemannGaussian/Forgotten.lean", "-- unregistered proof\n")
        with self.assertRaisesRegex(ValueError, "Unimported source"):
            build.partition()

    def test_optional_target_cannot_become_a_default(self):
        self.write("lakefile.toml", 'defaultTargets = ["RiemannGaussian", "NumericalCertificate"]\n')
        with self.assertRaisesRegex(ValueError, "must not enter defaultTargets"):
            build.partition()


if __name__ == "__main__":
    unittest.main()
