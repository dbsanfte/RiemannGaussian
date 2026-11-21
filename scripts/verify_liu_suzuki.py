"""Check Liu's published Lean sources and their application to the Suzuki sum.

Pass a checkout of liubaiying101/Improved-zero-free-half-planes-for-the-quasi-
Riemann-hypothesis at 46d612c2b63a163665ef560afca1965f7c8f434b. The first
2923 foundation modules are supplied by this project's pinned OAI dependency.
"""

import argparse
import hashlib
import os
import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
HASHES = {
    "OAI08": "e113c4e9340a478af879435c6c9109f3266d011b12ae1f99d9bde829658ee1b7",
    "PartsI_III": "09325a31b65b92b2af397e484c0f3adcc21fe62ef0c39f8b02432b89baff572c",
    "PartIV": "060dcce2bc90f1d97df2f9dcbe4f0e04c1bb55213440db35810ef7b49ceac1b8",
}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path)
    args = parser.parse_args()
    out = ROOT / ".lake/suzuki-liu"
    out.mkdir(parents=True, exist_ok=True)
    for module, digest in HASHES.items():
        source = (args.checkout / f"{module}.lean").read_bytes()
        if hashlib.sha256(source).hexdigest() != digest:
            raise SystemExit(f"Published source hash mismatch in {module}.lean")
        if module == "OAI08":
            marker = b"/-! Original module: OAI.NumberTheory.DirichletL.Hecke.ConditionalNonvanishing"
            hecke_modules = source[source.index(marker):]
            source = b"import OAI.NumberTheory.DirichletL.Nonvanishing\n" + hecke_modules
        (out / f"{module}.lean").write_bytes(source)
    lake = shutil.which("lake") or Path.home() / ".elan/bin/lake"
    targets = [
        "+RiemannGaussian.SuzukiLocalCancellationCofactorTail:olean",
        "+RiemannGaussian.DyadicPrimeZeroBound:olean",
    ]
    subprocess.run([lake, "build", *targets, "--wfail"], cwd=ROOT, check=True)
    lean = subprocess.check_output([lake, "env", "which", "lean"], cwd=ROOT, text=True).strip()
    search = subprocess.check_output([lake, "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True)
    paths = [(ROOT / entry).resolve() for entry in search.strip().split(os.pathsep) if entry]
    env = dict(
        os.environ,
        LEAN_PATH=os.pathsep.join(map(str, [out, *paths])),
        PATH=os.pathsep.join([str(Path(lean).parent), os.environ["PATH"]]),
    )
    options = [
        lean, "-j4", "--trust=0", "-DautoImplicit=false",
        "-DwarningAsError=true", "-DmaxHeartbeats=0",
    ]
    shutil.copyfile(ROOT / "scripts/CheckLiuCofactor.lean", out / "CheckLiuCofactor.lean")
    for module in [*HASHES, "CheckLiuCofactor"]:
        print(f"Checking {module}", flush=True)
        with (out / f"{module}.log").open("w") as log:
            subprocess.run([*options, "-o", f"{module}.olean", f"{module}.lean"],
                           cwd=out, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
        subprocess.run([Path(lean).with_name("leanchecker"), module], cwd=out, env=env, check=True)


if __name__ == "__main__":
    main()
