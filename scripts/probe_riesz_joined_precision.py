#!/usr/bin/env python3
"""Optional precision audit of the joined Riesz model, not a prime-sum bound.

Compare 113-bit and 100-decimal-digit Euler recurrences AND direct inverse
convolutions at the same exact intended parameters. There is no FFT, float
conversion, radial quadrature or count truncation in the helper. Grid error
remains uncertified. This deliberately does not certify earlier integrated
model values, still less transport them to ordinary primes.

Needs g++, libquadmath and the Boost headers; keep outside ordinary CI.
"""
import argparse
import concurrent.futures
from decimal import Decimal, localcontext
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "scripts/riesz_joined_precision.cpp"


def binary(precision):
    source_hash = hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    compiler = subprocess.check_output(["g++", "--version"], text=True).splitlines()[0]
    key = hashlib.sha256((source_hash + compiler + str(precision)).encode()).hexdigest()[:16]
    path = ROOT / ".lake/riesz-joined-precision" / f"probe-{key}"
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        command = ["g++", "-O3", "-std=c++17", str(SOURCE), "-o", str(path)]
        if precision == 34:
            command.extend(["-DUSE_QUAD", "-lquadmath"])
        subprocess.run(command, check=True)
    return path, compiler, source_hash


def evaluate(executable, n, grid, share):
    start = time.monotonic()
    output = subprocess.check_output(
        [str(executable), str(n), str(grid), share], text=True).split()
    if len(output) != 5:
        raise ValueError(f"Unexpected helper output: {output}")
    return {
        "value": output[3],
        "absolute_convolution_mass": output[4],
        "seconds": time.monotonic() - start,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--orders", nargs="+", type=int, default=[262144, 1048576])
    parser.add_argument("--grids", nargs="+", type=int, default=[512, 2048])
    parser.add_argument("--shares", nargs="+", default=["0.01", "0.04"])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if min(args.orders + args.grids) <= 0:
        parser.error("orders and grids must be positive")
    if any(not Decimal(0) < Decimal(r) < Decimal("0.45") for r in args.shares):
        parser.error("shares must lie strictly between 0 and 0.45")
    b34, compiler, source_hash = binary(34)
    b100, _, _ = binary(100)

    def run(case):
        n, grid, share = case
        low = evaluate(b34, n, grid, share)
        high = evaluate(b100, n, grid, share)
        with localcontext() as ctx:
            ctx.prec = 100
            error = abs(Decimal(low["value"]) - Decimal(high["value"]))
            relative = error / abs(Decimal(high["value"])) if Decimal(high["value"]) else None
        row = {"N": n, "cutoff_grid": grid, "least_share": share,
               "precision_113_bits": low, "precision_100_decimal": high,
               "absolute_difference": str(error),
               "relative_difference": str(relative) if relative is not None else None}
        print(f"N={n} grid={grid} r={share}: relative discrepancy {relative}", flush=True)
        return row

    cases = [(n, g, r) for n in args.orders for g in args.grids for r in args.shares]
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
        rows = list(executor.map(run, cases))
    result = {
        "scope": "Synthetic all-count fixed-point lattice response; precision comparison only",
        "proof_status": "Not certified; no retained prime-sum bound or asymptotic conclusion",
        "parameters": {"u": "10001/20000", "owner_share": "11/20",
                       "T": "(N+1)/u", "L": "2*(-N*log(u)-log(N+1))",
                       "modes": ["0", "1/40000 + (3/500)i", "1/40000 - (3/500)i"],
                       "multiplicities": [1, 3, 3]},
        "kept": ["both empty coefficient atoms", "every count on this grid",
                 "all Riesz subset signs", "full conjugate phase",
                 "direct signed convolution in each precision"],
        "not_included": ["radial or share integration", "factorial beta-face weights",
                         "actual ordinary-prime measure", "literal count masks 3..55/3..13",
                         "physical prime endpoints", "certified rounding or grid errors"],
        "length_note": "Asymptotic moving length; the exact integer-floor length is not evaluated",
        "compiler": compiler,
        "source_sha256": source_hash,
        "probe_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "rows": rows,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
