#!/usr/bin/env python3
"""Exercise the actual Lake configuration without compiling certificate proofs.

Tiny Lean probes check the default import boundary and each library's actual
elaboration mode. External dependencies are omitted from this isolated fixture.
"""
from pathlib import Path
import re
import subprocess
import tempfile

from numerical_certificate import ROOT
from verify_numerical_certificate import lake_command


def main():
    command, env = lake_command()
    with tempfile.TemporaryDirectory(prefix="certificate-lake-config-") as tmp:
        root = Path(tmp)
        config = (ROOT / "lakefile.toml").read_text()
        config = re.sub(r"(?ms)^\[\[require\]\]\n.*?(?=^\[|\Z)", "", config)
        (root / "lakefile.toml").write_text(config)
        (root / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
        (root / "RiemannGaussian/CertificateData").mkdir(parents=True)
        (root / "RiemannGaussian.lean").write_text("import RiemannGaussian.Core\n")
        (root / "NumericalCertificate.lean").write_text(
            "import RiemannGaussian.CertificateData.Probe\n")
        probes = [("RiemannGaussian/Core.lean", "true"),
                  ("RiemannGaussian/CertificateData/Probe.lean", "false")]
        for filename, mode in probes:
            (root / filename).write_text(
                "import Lean\nopen Lean Elab Command\nrun_cmd do\n"
                f"  unless Elab.async.get (← getOptions) == {mode} do\n"
                '    throwError "Unexpected elaboration mode"\n')
        subprocess.run(command + ["build", "--wfail"], cwd=root, env=env, check=True)
        artifact = root / ".lake/build/lib/lean/RiemannGaussian/CertificateData/Probe.olean"
        assert not artifact.exists(), "Default build compiled optional data"
        subprocess.run(command + ["build", "NumericalCertificate", "--wfail"],
                       cwd=root, env=env, check=True)
        assert artifact.exists(), "Optional target omitted its data"
    print("Lake keeps ordinary elaboration unchanged and optional data serial.")


if __name__ == "__main__":
    main()
