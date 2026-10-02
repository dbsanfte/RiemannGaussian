#!/usr/bin/env python3
"""Optional semiprime modular-signal investigation; never a build or CI job.

For N=p*q with distinct primes and gcd(a,N)=1, Euler's theorem gives
a^(N+1) = a^(p+q) (mod N). This exact encoding is classical. This probe
decodes it inside a PUBLIC factor-ratio bound, using sparse residue masks
and adaptive baby-step/giant-step searches. It is not a new asymptotic
factoring result and makes no comparison claim against tuned QS or NFS.

The decoder receives only N, its ratio promise and public settings.
Reference primes appear only in sample generation and post-run validation.
gmpy2 is optional for decoding. SymPy is needed for generated experiments.
Benchmarks run sequentially and include per-input wheel construction.
"""

import argparse
from dataclasses import asdict, dataclass
import hashlib
import json
import math
from pathlib import Path
import platform
import random
import shutil
import statistics
import subprocess
import sys
import time

try:
    import gmpy2
except ImportError:
    gmpy2 = None


SMALL_PRIMES = (2, 3, 5, 7, 11, 13, 17)
VARIANTS = ("plain", "wheel", "adaptive", "prime-power")


@dataclass
class FactorResult:
    factor: int | None
    reason: str
    wheel: int = 1
    residues: int = 1
    width: int = 0
    baby_entries: int = 0
    giant_steps: int = 0
    stages: int = 0
    candidates_checked: int = 0


def factor_sum_residues(n, modulus):
    """All t+n/t mod modulus with t a unit; no factor of n is queried."""
    if modulus == 1:
        return [0]
    if math.gcd(n, modulus) != 1:
        raise ValueError("The residue modulus must be coprime to N")
    return sorted({
        (t + (n % modulus) * pow(t, -1, modulus)) % modulus
        for t in range(1, modulus) if math.gcd(t, modulus) == 1
    })


def join_residues(n, moduli):
    """CRT join of permitted residues, without scanning the full wheel."""
    residues, wheel = [0], 1
    for modulus in moduli:
        allowed = factor_sum_residues(n, modulus)
        inverse = pow(wheel, -1, modulus)
        residues = [
            r + wheel * ((s - r) * inverse % modulus)
            for r in residues for s in allowed
        ]
        wheel *= modulus
    return wheel, sorted(residues)


def fixed_wheel_moduli(bits):
    """Frozen first-stage policy used before the prime-power experiment."""
    if bits <= 20:
        return [8]
    if bits <= 28:
        return [8, 3]
    if bits <= 36:
        return [8, 3, 5]
    if bits <= 52:
        return [8, 3, 5, 7]
    if bits <= 68:
        return [8, 3, 5, 7, 11]
    if bits <= 82:
        return [8, 3, 5, 7, 11, 13]
    return [8, 3, 5, 7, 11, 13, 17]


def power_wheel_moduli(n):
    """Frozen input-only policy; prime-power lifts help stationary residues."""
    bits = n.bit_length()
    moduli = [16 if n % 4 == 1 else 8]
    if bits <= 36:
        return moduli + [3, 5]
    if bits <= 52:
        return moduli + [3, 5, 7]
    if bits <= 68:
        return moduli + [9 if n % 3 == 1 else 3, 5, 7, 11]
    moduli += [
        9 if n % 3 == 1 else 3,
        25 if n % 5 in (1, 4) else 5,
        7, 11,
    ]
    if bits <= 82:
        if math.prod(moduli) * 13 <= 500_000:
            moduli.append(13)
    else:
        moduli.append(13)
        if math.prod(moduli) * 17 <= 10_000_000:
            moduli.append(17)
    return moduli


def decode_mask(n, wheel, sum_residues, ratio_ceiling=2,
                start_divisor=64, use_gmp=True, max_entries=2_000_000):
    """Exact finite decoder under the promised q/p <= ratio_ceiling.

    Every stride is a multiple of wheel, so permitted baby residues stay
    permitted in every giant block. Duplicate modular values retain ALL
    exponents; a collision alone is never accepted as a factor.

    A low multiplicative order can create many collision candidates, so
    the usual O(N^(1/4)) search-size heuristic is not an unconditional
    runtime theorem for this implementation.
    """
    lower = math.isqrt(4 * n)
    lower += lower * lower < 4 * n
    upper = math.isqrt((ratio_ceiling + 1) ** 2 * n // ratio_ceiling)
    width = upper - lower
    residues = sorted((s - lower) % wheel for s in sum_residues)
    count = len(residues)
    result = FactorResult(None, "interval-exhausted", wheel, count, width)
    if width < 0 or not count:
        return result

    gaps = [residues[i + 1] - residues[i] for i in range(count - 1)]
    gaps.append(wheel + residues[0] - residues[-1])
    use_gmp = use_gmp and gmpy2 is not None
    scalar = gmpy2.mpz if use_gmp else int
    modulus = scalar(n)
    jumps = {gap: scalar(pow(2, gap, n)) for gap in set(gaps)}
    raw = math.isqrt(
        (max(1, width // start_divisor) * wheel + count - 1) // count
    ) + 1
    stride = wheel * ((raw + wheel - 1) // wheel)
    table = {}
    exponent, gap_index = residues[0], 0
    value = scalar(pow(2, exponent, n))
    previous = -1

    while True:
        result.stages += 1
        while exponent < stride and exponent <= width:
            if result.baby_entries >= max_entries:
                result.reason = "explicit-table-cap"
                return result
            old = table.get(value)
            if old is None:
                table[value] = exponent
            elif isinstance(old, int):
                table[value] = [old, exponent]
            else:
                old.append(exponent)
            result.baby_entries += 1
            value = value * jumps[gaps[gap_index]] % modulus
            exponent += gaps[gap_index]
            gap_index = (gap_index + 1) % count

        end = min(width, max(previous + 1, stride * stride * count // wheel))
        first_block = (previous + 1) // stride
        target = scalar(pow(2, n + 1 - lower - first_block * stride, n))
        step = scalar(pow(2, -stride, n))
        for block in range(first_block, end // stride + 1):
            result.giant_steps += 1
            hits = table.get(target)
            if hits is not None:
                for remainder in [hits] if isinstance(hits, int) else hits:
                    offset = block * stride + remainder
                    if not previous < offset <= end:
                        continue
                    result.candidates_checked += 1
                    total = lower + offset
                    discriminant = total * total - 4 * n
                    if discriminant < 0:
                        continue
                    root = math.isqrt(discriminant)
                    if root * root != discriminant or (total - root) % 2:
                        continue
                    factor = (total - root) // 2
                    if 1 < factor < n and n % factor == 0:
                        result.factor = factor
                        result.reason = "exact-division"
                        return result
            target = target * step % modulus
        if end == width:
            return result
        previous, stride = end, 2 * stride


def factor_semiprime(n, ratio_ceiling=2, variant="prime-power",
                     use_gmp=True, max_entries=2_000_000):
    """Return a checked factor, or explicit exhaustion/resource-cap status.

    The public promise is an integer semiprime with q/p <= ratio_ceiling.
    The promise is not established by this routine. A returned proper
    divisor is checked exactly even if the caller supplied a false promise.
    """
    if n < 4 or ratio_ceiling < 1:
        raise ValueError("Require N >= 4 and an integer ratio ceiling >= 1")
    if variant not in VARIANTS:
        raise ValueError(f"Unknown variant: {variant}")
    for prime in SMALL_PRIMES:
        if n % prime == 0 and prime < n:
            return FactorResult(prime, "known-small-prime")
    root = math.isqrt(n)
    if root * root == n:
        return FactorResult(root, "perfect-square")

    if variant == "plain":
        moduli = []
    elif variant == "prime-power":
        moduli = power_wheel_moduli(n)
    elif variant == "adaptive":
        moduli = fixed_wheel_moduli(n.bit_length())
    else:
        moduli = fixed_wheel_moduli(min(n.bit_length(), 68))
    wheel, residues = join_residues(n, moduli)
    start_divisor = 64 if variant in ("adaptive", "prime-power") else 1
    return decode_mask(n, wheel, residues, ratio_ceiling, start_divisor,
                       use_gmp, max_entries)


def generated_samples(bits, count, seed):
    """Same-length primes; products have bits-1 or bits input bits.

    Prime generation and labels are outside all decoder timing regions.
    Labels are passed only to post-run validators.
    """
    from sympy import nextprime

    if bits < 16 or bits % 2:
        raise ValueError("Generated benchmark sizes must be even and >= 16")
    rng = random.Random(seed)
    half = bits // 2
    low, high = 1 << (half - 1), 1 << half
    padding = min(1000, max(4, (high - low) // 8))
    samples = []
    while len(samples) < count:
        p = int(nextprime(rng.randrange(low, high - padding)))
        q = int(nextprime(rng.randrange(low, high - padding)))
        if p == q or max(p, q) >= high:
            continue
        samples.append((p * q, min(p, q), max(p, q)))
    return samples


def validate():
    from sympy import primerange

    small = list(map(int, primerange(13, 251)))
    checked = 0
    for index, p in enumerate(small):
        for q in small[index:]:
            if q > 2 * p:
                continue
            n = p * q
            result = factor_semiprime(n)
            assert result.factor in (p, q) and n % result.factor == 0
            if p != q:
                assert pow(2, n + 1, n) == pow(2, p + q, n)
            checked += 1

    mask_checks = 0
    for n in (2021, 3337, 3397, 3901):
        for moduli in ([8, 3, 5], [16, 9, 25], [8, 27, 49], [16, 9, 5, 7]):
            wheel, residues = join_residues(n, moduli)
            assert residues == factor_sum_residues(n, wheel)
            mask_checks += 1

    # ord_2047(2)=11: the table contains genuine duplicate modular values.
    aliases = decode_mask(2047, 1, [0], 1000, 1)
    assert aliases.factor == 23 and aliases.candidates_checked >= 2
    caps = decode_mask(2047, 1, [0], 1000, 1, max_entries=1)
    assert caps.factor is None and caps.reason == "explicit-table-cap"
    return {
        "smallExactFactorChecks": checked,
        "independentCRTMaskChecks": mask_checks,
        "lowOrderAliasRegression": asdict(aliases),
        "explicitTableCapRegression": True,
    }


def native_batch(executable, numbers, timeout):
    """One native invocation per complete batch, including startup/capture."""
    started = time.perf_counter_ns()
    run = subprocess.run(
        [executable, *map(str, numbers)], capture_output=True, text=True,
        timeout=timeout, check=True,
    )
    elapsed = (time.perf_counter_ns() - started) / 1e6
    lines = run.stdout.splitlines()
    if len(lines) != len(numbers):
        raise ValueError("Native baseline returned the wrong number of lines")
    for n, line in zip(numbers, lines):
        left, right = line.split(":")
        factors = list(map(int, right.split()))
        if int(left) != n or len(factors) != 2 or math.prod(factors) != n:
            raise ValueError(f"Native baseline failed an exact check for {n}")
    return elapsed


def benchmark(args):
    if len(args.bits) != len(args.counts):
        raise ValueError("--bits and --counts must have the same length")
    executable = shutil.which(args.baseline)
    if executable is None:
        raise ValueError(f"Native baseline not available: {args.baseline}")
    version = subprocess.run(
        [executable, "--version"], capture_output=True, text=True, check=True,
    ).stdout.splitlines()[0]
    report = {
        "schemaVersion": 1,
        "sideInvestigation": True,
        "ordinaryBuildOrCIIntegration": False,
        "newFactoringComplexityProved": False,
        "scriptSha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "python": platform.python_version(),
        "platform": platform.platform(),
        "gmpy2": gmpy2.version() if gmpy2 else None,
        "nativeBaseline": {"executable": executable, "version": version},
        "seedBase": args.seed_base,
        "repeats": args.repeats,
        "publicFactorRatioCeiling": 2,
        "validation": validate(),
        "protocol": [
            "Fresh same-length prime pairs; actual product bits are reported.",
            "Imports and sample generation excluded; per-input masks included.",
            "Methods run sequentially in deterministically shuffled order.",
            "Native time includes one process startup per batch.",
            "Reference factors never enter the decoder.",
            "All returned factors checked exactly after the timing region.",
            "Reported statistic is median batch-average time per input.",
            "No comparison against tuned quadratic-sieve or NFS software.",
        ],
        "sizes": [],
    }
    for bits, count in zip(args.bits, args.counts):
        samples = generated_samples(bits, count, args.seed_base + bits)
        numbers = [row[0] for row in samples]
        batches = {name: [] for name in ("adaptive", "prime-power", "native")}
        details = {}
        for repeat in range(args.repeats):
            order = list(batches)
            random.Random(args.seed_base + 10 + bits + repeat).shuffle(order)
            for method in order:
                if method == "native":
                    elapsed = native_batch(executable, numbers, args.timeout)
                else:
                    started = time.perf_counter_ns()
                    results = [
                        factor_semiprime(n, variant=method,
                                         max_entries=args.max_entries)
                        for n in numbers
                    ]
                    elapsed = (time.perf_counter_ns() - started) / 1e6
                    for (n, p, q), result in zip(samples, results):
                        if result.factor not in (p, q) or n % result.factor:
                            raise ValueError(
                                f"{method} failed for {n}: {asdict(result)}"
                            )
                    details[method] = results
                batches[method].append(elapsed / count)
        row = {
            "nominalBits": bits,
            "actualBits": sorted({n.bit_length() for n in numbers}),
            "count": count,
            "batchMsPerInput": batches,
            "medianBatchMsPerInput": {
                method: statistics.median(times)
                for method, times in batches.items()
            },
            "cases": [
                {
                    "N": str(n), "referencePrimes": [str(p), str(q)],
                    "primePowerDecoder": {
                        **asdict(details["prime-power"][index]),
                        "factor": str(details["prime-power"][index].factor),
                    },
                }
                for index, (n, p, q) in enumerate(samples)
            ],
        }
        report["sizes"].append(row)
        print(json.dumps({key: value for key, value in row.items()
                          if key != "cases"}), flush=True)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    factor = commands.add_parser("factor", help="decode one promised semiprime")
    factor.add_argument("N", type=int)
    factor.add_argument("--ratio-ceiling", type=int, default=2)
    factor.add_argument("--variant", choices=VARIANTS, default="prime-power")
    factor.add_argument("--no-gmp", action="store_true")
    factor.add_argument("--max-entries", type=int, default=2_000_000)
    commands.add_parser("validate", help="run small exact and mask regressions")
    bench = commands.add_parser("benchmark", help="explicit optional benchmark")
    bench.add_argument("--bits", nargs="+", type=int, default=[64, 80, 88, 96])
    bench.add_argument("--counts", nargs="+", type=int, default=[48, 32, 20, 8])
    bench.add_argument("--seed-base", type=int, default=2026100900)
    bench.add_argument("--repeats", type=int, default=3)
    bench.add_argument("--baseline", default="factor")
    bench.add_argument("--timeout", type=float, default=45)
    bench.add_argument("--max-entries", type=int, default=2_000_000)
    bench.add_argument("--output", type=Path)
    args = parser.parse_args()
    try:
        if args.command == "factor":
            result = factor_semiprime(
                args.N, args.ratio_ceiling, args.variant, not args.no_gmp,
                args.max_entries,
            )
            print(json.dumps({
                "N": str(args.N), **asdict(result),
                "factor": str(result.factor) if result.factor else None,
                "cofactor": str(args.N // result.factor) if result.factor else None,
                "publicFactorRatioCeiling": args.ratio_ceiling,
            }))
            return 0 if result.factor else 1
        if args.command == "validate":
            print(json.dumps(validate(), indent=2))
            return 0
        if args.repeats < 1 or any(count < 1 for count in args.counts):
            raise ValueError("Counts and repeats must be positive")
        report = benchmark(args)
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(
                json.dumps(report, indent=2, allow_nan=False) + "\n",
                encoding="utf-8",
            )
        return 0
    except (ValueError, subprocess.TimeoutExpired,
            subprocess.CalledProcessError) as error:
        print(str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
