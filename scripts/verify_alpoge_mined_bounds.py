"""Replay the four archived modules used for the zeta factorial and variation bounds.

Use the vendored sources or pass the path to the original extracted lean/src directory.
Optional checks join the bounds to the global or window criterion and a prime harmonic estimate.
"""

import argparse
import hashlib
import os
import re
from pathlib import Path
import shutil
import subprocess
from tempfile import TemporaryDirectory


ROOT = Path(__file__).resolve().parents[1]
HASHES = {
    "Formalism.Statement": "ae9733a3faa3c29aaff14c34b886081a05ca9849a50ebabcbd3a2c9df5101482",
    "Formalism.StatementOC": "0249562a8b70df61856f6fdce16afdf17fbe88c9945af4231700503d11027f8a",
    "Formalism.StatementU": "8f3f0e446fc494188419e861738af0061a00019b0efbfa8dea63a4c54cd1fd9e",
    "Formalism.ZetaNonvanishing.GzLipschitz": "c6c5805ce9f9697235230d737f20c2d476e618f6808c80934d0ee8a6d4856c44",
}


WINDOW_ROOTS = [
    "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow",
    "Formalism.GammaFactorNonvanishing.RhOfRight",
    "Formalism.ZetaNonvanishing.GzLipschitz",
]
WINDOW_DIGEST = "8db2c39e811def552dc2ec2e178e351a806095723c8757c1c66b05acc674fb9e"
FIXED_BAND_ROOTS = [
    "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindow",
    "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.poleData",
    "Formalism.GammaFactorNonvanishing.RhOfRight",
]
FIXED_BAND_DIGEST = "7430a8ef8f18ee8cb30fe17653c2cc72b554c2680ab7763bbc8787c81adf9652"
# These two headers are the only imports of the Mathlib umbrella in the
# fixed-band closure. The headers below also cover its local proof scripts.
FIXED_BAND_MATHLIB_IMPORTS = {
    "Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily": (
        "Mathlib.Analysis.Analytic.Order",
        "Mathlib.Data.Fintype.Option",
        "Mathlib.MeasureTheory.Function.Floor",
        "Mathlib.MeasureTheory.Order.Group.Lattice",
        "Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt",
        "Mathlib.NumberTheory.DirichletCharacter.Orthogonality",
        "Mathlib.NumberTheory.Harmonic.Bounds",
        "Mathlib.NumberTheory.Harmonic.EulerMascheroni",
        "Mathlib.NumberTheory.LSeries.Nonvanishing",
        "Mathlib.Tactic.Abel",
        "Mathlib.Tactic.FieldSimp",
        "Mathlib.Tactic.FunProp",
        "Mathlib.Tactic.GCongr",
        "Mathlib.Tactic.Linarith",
        "Mathlib.Tactic.LinearCombination",
        "Mathlib.Tactic.NormNum",
        "Mathlib.Tactic.Positivity",
        "Mathlib.Tactic.Push",
        "Mathlib.Tactic.Ring",
    ),
    "Formalism.GammaFactorNonvanishing.RhOfRight": (
        "Mathlib.NumberTheory.LSeries.RiemannZeta",
        "Mathlib.Tactic.LinearCombination",
        "Mathlib.Tactic.Linarith",
        "Mathlib.Tactic.NormNum",
        "Mathlib.Tactic.Push",
        "Mathlib.Tactic.Ring",
    ),
}
PRINCIPAL_ROOTS = WINDOW_ROOTS[:2] + ["Formalism.StatementOC"]
PRINCIPAL_DIGEST = "baf84fb6b388a2ad87b46a884fb7b818dc872e8bc789282bbb3745df0303e1af"
PRINCIPAL_WINDOW = "Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.Window"
PRINCIPAL_WINDOW_DIGEST = "18c9505eaa534a57b30f097453335045a795d0ac86d0e2f6224617b23fb68027"
MELLIN_PORT = "Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiOfNeOne"
MELLIN_ORIGINAL = "22192caa33f0e9b840298329573ca3ea15e3e5d9e60624efcda3562f8ddff26a"


def source_path(src: Path, module: str) -> Path:
    rel = Path(*module.split(".")).with_suffix(".lean")
    path = src / rel
    if module == MELLIN_PORT and hashlib.sha256(path.read_bytes()).hexdigest() == MELLIN_ORIGINAL:
        return ROOT / "vendor/alpoge-zeta" / rel
    return path


def pinned_sources(src: Path, roots: list[str], digest: str, *, original: bool = False) -> dict[str, str]:
    """Verify the source manifest and return its modules in dependency order."""
    hashes = {}

    def visit(module: str) -> None:
        if module in hashes:
            return
        path = src.joinpath(*module.split(".")).with_suffix(".lean") if original else source_path(src, module)
        if not path.is_file():
            return
        source = path.read_bytes()
        for line in re.findall(r"^[ \t]*(?:(?:public|private|meta)[ \t]+)*import[ \t]+([^\r\n]+)",
                               source.decode(), re.MULTILINE):
            for dep in line.partition("--")[0].split():
                visit(dep)
        hashes[module] = hashlib.sha256(source).hexdigest()

    for module in roots:
        visit(module)
    manifest = "".join(f"{module} {hashes[module]}\n" for module in sorted(hashes))
    if hashlib.sha256(manifest.encode()).hexdigest() != digest:
        raise ValueError("The selected source closure differs from the audited archive")
    return hashes


def global_sources(src: Path, prime_band: bool = False) -> dict[str, str]:
    roots = ["Formalism.ZetaNonvanishing.ZetaLandau", "Formalism.ZetaNonvanishing.RHofHalfPlane",
             "Formalism.ZetaNonvanishing.GzLipschitz"]
    digest = "3e6972f5eb0285bca7bc59d9bc663271d4a4ca452a9abd3bfa5d488e6d1cb7db"
    if prime_band:
        roots.append("Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MertensLogSum.PrimeLogOverPTop")
        digest = "a89aec6d6db8c954706cec21d4bbcc3243450a911010d55306a76f3d075de712"
    return pinned_sources(src, roots, digest)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("src", type=Path, nargs="?", default=ROOT / "vendor/alpoge-zeta",
                        help="Optional source directory. Defaults to the selected sources in vendor/alpoge-zeta.")
    parser.add_argument("--global-landau", action="store_true",
                        help="Check the shorter zeta-only implication for a bound on all fourth powers.")
    parser.add_argument("--cubic-samples", action="store_true",
                        help="Check the sufficient three-quarters prime cutoff using only the 20-module global route.")
    parser.add_argument("--prime-band", action="store_true",
                        help="Also check the averaged prime band and its global zeta criterion.")
    parser.add_argument("--liu", action="store_true",
                        help="Apply the previously replayed Liu half-plane from verify_liu_suzuki.py to the cubic tail.")
    parser.add_argument("--principal-level", action="store_true",
                        help="Check the direct principal cyclic level route with the sliced archive definitions.")
    parser.add_argument("--window-mass", action="store_true",
                        help="Check the finite positive-deficit mass criterion from the vendored window sources.")
    parser.add_argument("--mangoldt-window", action="store_true",
                        help="Check the direct signed Mangoldt window criterion through cubic quadrature.")
    parser.add_argument("--single-window", action="store_true",
                        help="Check the single fourth-power observation criterion without repeated averaging.")
    parser.add_argument("--local-prime-window", action="store_true",
                        help="Check the ordinary-prime criterion on long intervals crossing fourth powers.")
    parser.add_argument("--fixed-prime-band", action="store_true",
                        help="Check the fourth-power mass criterion using one fixed dyadic band per sample.")
    parser.add_argument("--fixed-prime-bounds", action="store_true",
                        help="Also check the reverse implication and the mass bound from a zero half-plane.")
    parser.add_argument("--fixed-prime-sieve", action="store_true",
                        help="Check the centered and truncated Möbius criteria and their local prefix energy.")
    parser.add_argument("--fixed-prime-short-inverse", action="store_true",
                        help="Check the exact quartic expression in Möbius values through the fourth root.")
    parser.add_argument("--fixed-prime-block", action="store_true",
                        help="Check single-multiple block cancellation and the off-diagonal bound by reduced ratio.")
    parser.add_argument("--fixed-prime-liu", action="store_true",
                        help="Apply the previously replayed Liu half-plane to the fixed-band mass bound.")
    parser.add_argument("--reuse-native", action="store_true",
                        help="Use the native Lean objects already installed in the Lake environment.")
    parser.add_argument("--window-port", type=Path,
                        help="Also recheck the prime criteria against the audited analytic worktree.")
    args = parser.parse_args()
    if args.fixed_prime_liu:
        args.fixed_prime_bounds = args.fixed_prime_sieve = True
    if args.fixed_prime_block or args.fixed_prime_short_inverse:
        args.fixed_prime_sieve = True
    if args.fixed_prime_bounds or args.fixed_prime_sieve:
        args.fixed_prime_band = True
    averaged_window = args.window_mass or args.mangoldt_window
    window_requested = averaged_window or args.single_window or args.local_prime_window
    fixed_only = args.fixed_prime_band and not any((window_requested, args.global_landau, args.prime_band,
                                                 args.cubic_samples, args.liu, args.principal_level))
    if args.principal_level and any((args.global_landau, args.cubic_samples, args.prime_band,
                                     args.liu, window_requested, args.window_port, args.fixed_prime_band)):
        parser.error("--principal-level uses its own isolated selection")
    if args.liu:
        args.prime_band = True
    if args.liu or args.fixed_prime_liu:
        liu = ROOT / ".lake/suzuki-liu"
        if not (liu / "CheckLiuCofactor.olean").is_file():
            parser.error("The Liu selections need the compiled adapter produced by scripts/verify_liu_suzuki.py")
    if args.prime_band:
        args.cubic_samples = True
    if args.cubic_samples:
        args.global_landau = True
    src = args.src.resolve()
    out = ROOT / ".lake" / ("alpoge-global" if args.global_landau else "alpoge-mined")
    if args.prime_band:
        out = ROOT / ".lake/alpoge-prime-band-port"
    elif args.cubic_samples:
        out = ROOT / ".lake/alpoge-cubic-samples"
    if args.window_mass:
        out = out.with_name(out.name + "-window-mass")
    elif args.mangoldt_window:
        out = out.with_name(out.name + "-mangoldt-window")
    elif args.local_prime_window:
        out = out.with_name(out.name + "-local-prime-window")
    elif args.single_window:
        out = out.with_name(out.name + "-single-window")
    if fixed_only:
        out = ROOT / ".lake/alpoge-fixed-prime-band"
    if args.principal_level:
        out = ROOT / ".lake/alpoge-principal-level"
    lake = os.environ.get("LAKE") or shutil.which("lake") or Path.home() / ".elan/bin/lake"
    target = "PrimeMassFromZeroBound" if args.prime_band else "AlpogeZetaSampleBounds"
    if not args.principal_level and not args.reuse_native:
        native = [f"+RiemannGaussian.{target}:olean"]
        if args.fixed_prime_band and not (args.window_mass or args.local_prime_window):
            native.append("+RiemannGaussian.AlpogeZetaShortIntervals:olean")
        if args.window_mass or args.local_prime_window:
            native.extend(["+RiemannGaussian.AlpogeZetaShortIntervals:olean",
                           "+RiemannGaussian.ZetaCenteredEulerZeroFree:olean",
                           "+RiemannGaussian.ZetaFirstZeroCompleteness:olean",
                           "+RiemannGaussian.AlpogeZetaPowerWindows:olean"])
        if args.fixed_prime_block:
            native.append("+RiemannGaussian.MoebiusHarmonicCancellation:olean")
        if args.fixed_prime_bounds and not (args.window_mass or args.local_prime_window):
            native.append("+RiemannGaussian.AlpogeZetaPowerWindows:olean")
        if args.local_prime_window:
            native.append("+RiemannGaussian.PrimeMassFromZeroBound:olean")
        if args.window_mass:
            native.extend(["+RiemannGaussian.ZetaVaughanIdentity:olean",
                           "+PrimeNumberTheoremAnd.Wiener:olean"])
        subprocess.run([lake, "build", *native, "--wfail"], cwd=ROOT, check=True)
    env_path = subprocess.check_output([lake, "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True)
    lean = subprocess.check_output([lake, "env", "which", "lean"], cwd=ROOT, text=True).strip()
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(out), env_path.strip()]),
               PATH=os.pathsep.join([str(Path(lean).parent), os.environ["PATH"]]))
    env.setdefault("LEAN_NUM_THREADS", "2")
    out.mkdir(parents=True, exist_ok=True)
    archive = global_sources(src, args.prime_band) if args.global_landau else HASHES.copy()
    if fixed_only:
        archive = {}
    if args.fixed_prime_band:
        archive.update(pinned_sources(src, FIXED_BAND_ROOTS, FIXED_BAND_DIGEST))
    if window_requested:
        archive.update(pinned_sources(src, WINDOW_ROOTS, WINDOW_DIGEST))
    if args.principal_level:
        archive = pinned_sources(src, PRINCIPAL_ROOTS, PRINCIPAL_DIGEST)
        archive[PRINCIPAL_WINDOW] = PRINCIPAL_WINDOW_DIGEST
    with TemporaryDirectory(prefix="source-headers-", dir=out) as headers:
        header_root = Path(headers)
        for module, digest in archive.items():
            rel = Path(*module.split(".")).with_suffix(".lean")
            source = (ROOT / "vendor/alpoge-principal" / rel if module == PRINCIPAL_WINDOW
                      else source_path(src, module))
            source_root = source.parents[len(rel.parts) - 1]
            contents = source.read_bytes()
            if hashlib.sha256(contents).hexdigest() != digest:
                raise ValueError(f"Archive source hash mismatch in {source}")
            if fixed_only and module in FIXED_BAND_MATHLIB_IMPORTS:
                umbrella = b"import Mathlib\n"
                if not contents.startswith(umbrella):
                    raise ValueError(f"Missing pinned Mathlib import header in {source}")
                imports = FIXED_BAND_MATHLIB_IMPORTS[module]
                header = "".join(f"import {name}\n" for name in imports).encode()
                source_root = header_root
                source = source_root / rel
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_bytes(header + contents[len(umbrella):])
            obj = out / rel.with_suffix(".olean")
            obj.parent.mkdir(parents=True, exist_ok=True)
            print(f"Checking {module}", flush=True)
            subprocess.run([lean, "--trust=0", f"--root={source_root}", "-DautoImplicit=false",
                            "-DrelaxedAutoImplicit=false", "-DmaxHeartbeats=4000000",
                            "-o", obj, source], env=env, cwd=ROOT, check=True)
    local = ["AlpogePrimeWindows", "CheckAlpogePrincipalLevel"] if args.principal_level else ["CheckAlpogeMinedBounds"]
    if args.global_landau or args.window_mass:
        local.extend(["AlpogeIntegerPrimeBand", "AlpogeQuadraticPatterns",
                      "AlpogeQuadraticPrefix", "AlpogeQuadraticSamples"])
    elif window_requested:
        local.append("AlpogeIntegerPrimeBand")
    if args.global_landau:
        local.extend(["CheckAlpogeGlobalSamples", "CheckAlpogeIntegerGlobal", "CheckAlpogeQuadraticGlobal"])
    if args.cubic_samples or averaged_window:
        local.extend(["CheckAlpogeResidueAverage", "CheckAlpogeRepeatedWeights"])
    if args.cubic_samples:
        local.append("CheckAlpogeRepeatedAverage")
    if args.prime_band:
        local.extend(["CheckAlpogePrimeBand", "CheckAlpogePrimeTailBounds"])
    if args.liu or args.fixed_prime_liu:
        env["LEAN_PATH"] = os.pathsep.join([str(liu), env["LEAN_PATH"]])
    if args.liu:
        local.append("CheckAlpogePrimeTailLiu")
    if window_requested:
        local.extend(["AlpogePrimeWindows", "CheckAlpogePrimeWindowMass"])
    if averaged_window:
        local.extend(["CheckAlpogeCubicWindowMass", "CheckAlpogeCubicQuadrature"])
    if args.single_window or args.window_mass or args.local_prime_window:
        local.append("CheckAlpogeIntegerBaseline")
    if args.local_prime_window or args.window_mass:
        local.append("CheckAlpogeZetaWindows")
    if args.local_prime_window:
        local.extend(["CheckAlpogeLocalPrimeWindow", "CheckAlpogeLocalPrimeIntervals"])
    if args.window_mass:
        local.extend(["CheckAlpogeCentralWindow", "CheckAlpogeCentralBlocks",
                      "CheckAlpogePrimeWindowCorrelation",
                      "CheckAlpogeQuadraticWindow", "CheckAlpogeCubicTypeI",
                      "CheckAlpogeCubicCross", "CheckAlpogeCubicVaughan", "CheckAlpogeCubicProducts",
                      "CheckAlpogeCubicRough", "CheckAlpogeCubicFourFactors",
                      "CheckAlpogeCubicSmallPrimes", "CheckAlpogeCubicSemiprimes",
                      "CheckAlpogeCubicSurplusDensity", "CheckAlpogeCubicRoughRange",
                      "CheckAlpogeCubicCrossingBound", "CheckAlpogeCubicMainTerm"])
    if fixed_only:
        local = []
    if args.fixed_prime_band:
        local.append("CheckAlpogeFixedPrimeBand")
    if args.fixed_prime_sieve:
        local.extend(["CheckAlpogeFixedPrimeBandMobius", "CheckAlpogeFixedPrimeBandCentered",
                      "CheckAlpogeFixedPrimeBandCorner", "CheckAlpogeFixedPrimeBandMoments",
                      "CheckAlpogeFixedPrimeBandFirstQuotient"])
    if args.fixed_prime_bounds:
        local.append("CheckAlpogeFixedPrimeBandBounds")
    if args.fixed_prime_short_inverse:
        local.append("CheckAlpogeFixedPrimeBandShortInverse")
    if args.fixed_prime_block:
        local.extend(["CheckAlpogeFixedPrimeBandBlock", "CheckAlpogeFixedPrimeBandRatios"])
    if args.fixed_prime_sieve and args.fixed_prime_bounds:
        local.append("CheckAlpogeFixedPrimeBandCenteredBounds")
    if args.fixed_prime_liu:
        local.append("CheckAlpogeFixedPrimeBandLiu")
    for name in local:
        subprocess.run([lean, "--trust=0", "-DwarningAsError=true", f"--root={ROOT / 'scripts'}",
                        "-o", out / f"{name}.olean", ROOT / "scripts" / f"{name}.lean"],
                       env=env, cwd=ROOT, check=True)
    targets = list(archive)
    if args.cubic_samples or window_requested or args.fixed_prime_band:
        # Only group by namespace when its objects exactly match the pinned selection.
        roots = sorted({name.split(".")[0] for name in archive})
        objects = {".".join(path.relative_to(out).with_suffix("").parts)
                   for root in roots for path in (out / root).rglob("*.olean")}
        if objects == set(archive):
            targets = roots
    if window_requested or args.fixed_prime_band:
        targets.append("RiemannGaussian.AlpogeZetaSampleBounds")
    if args.window_mass or args.local_prime_window or args.fixed_prime_band:
        targets.append("RiemannGaussian.AlpogeZetaShortIntervals")
    if args.fixed_prime_block:
        targets.append("RiemannGaussian.MoebiusHarmonicCancellation")
    if args.fixed_prime_bounds and not args.local_prime_window:
        targets.append("RiemannGaussian.AlpogeZetaPowerWindows")
    if args.local_prime_window:
        targets.extend(["RiemannGaussian.ZetaCenteredEulerZeroFree", "RiemannGaussian.ZetaFirstZeroCompleteness",
                        "RiemannGaussian.AlpogeZetaPowerWindows", "RiemannGaussian.PrimeMassFromZeroBound"])
    if args.window_mass:
        targets.extend(["RiemannGaussian.ZetaVaughanIdentity", "PrimeNumberTheoremAnd.Wiener"])
    subprocess.run([Path(lean).with_name("leanchecker"), "-v", *targets, *local],
                   env=env, cwd=ROOT, check=True)

    if args.window_port:
        port = args.window_port.resolve()
        subprocess.run([ROOT / "scripts/verify_alpoge_zeta_windows.sh", port], cwd=ROOT,
                       env=dict(os.environ, LAKE=str(lake), LEAN_NUM_THREADS=env["LEAN_NUM_THREADS"]), check=True)
        window = port / "vendor/alpoge-window/.lake/build/lib/lean"
        optional = ROOT / ".lake/dyadic-prime/optional"
        with TemporaryDirectory(dir=out) as tmp:
            # Lean resolves an entire top-level namespace against the first matching root.
            shared = Path(tmp) / "Formalism"
            shared.mkdir()
            for folder in [out / "Formalism", window / "Formalism"]:
                for entry in folder.iterdir():
                    link = shared / entry.name
                    if not link.exists():
                        link.symlink_to(entry, target_is_directory=entry.is_dir())
            combined = dict(env, LEAN_PATH=os.pathsep.join(
                [tmp, str(out), str(optional), str(window), env_path.strip()]))
            joined = ["AlpogeIntegerPrimeBand", "CheckAlpogePrimeWindowMass",
                      "CheckAlpogeIntegerBaseline", "CheckAlpogeMinedWindows"]
            for name in joined:
                subprocess.run([lean, "--trust=0", "-DwarningAsError=true", f"--root={ROOT / 'scripts'}",
                                "-o", out / f"{name}.olean", ROOT / "scripts" / f"{name}.lean"],
                               env=combined, cwd=ROOT, check=True)
            subprocess.run([Path(lean).with_name("leanchecker"), "-v", *joined],
                           env=combined, cwd=ROOT, check=True)


if __name__ == "__main__":
    main()
