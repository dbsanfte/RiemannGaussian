#!/usr/bin/env python3
"""Optional signed Suzuki probe. Floating evidence, not a certificate.

Retain every literal von Mangoldt prime power and the full work/entropy
ledger. Stream prefixes so the probe can extend its range without storing
an array of every potential. Continuous positive-density controls are
explicitly separate from the ordinary integer prime data.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.optimize import brentq


def constants():
    with mp.workdps(60):
        c = (mp.digamma(mp.mpf(1) / 4) - mp.log(mp.pi)) / 2
        b = mp.zeta(2, mp.mpf(1) / 4) / 4 - 8
        return np.longdouble(str(c)), np.longdouble(str(b))


def literal_prefixes(limit, chunk_size, query_cutoffs=()):
    sieve = np.ones(limit + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    primes = np.flatnonzero(sieve)
    del sieve
    powers = []
    for p0 in primes[: np.searchsorted(primes, math.isqrt(limit), side="right")]:
        p = int(p0)
        q = p * p
        while q <= limit:
            powers.append((q, math.log(p)))
            q *= p
    powers.sort()
    power_ns = np.array([p[0] for p in powers], dtype=np.int64)
    power_lams = np.array([p[1] for p in powers], dtype=np.longdouble)
    c, b = constants()
    mass0 = moment0 = np.longdouble(0)
    selected = []
    dyadic = []
    checksum = hashlib.sha256()
    max_moment_cancellation = np.longdouble(0)
    query_cutoffs = np.array(sorted(set(query_cutoffs)), dtype=np.int64)
    query_values = {}
    for lo in range(1, limit + 1, chunk_size):
        hi = min(limit + 1, lo + chunk_size)
        x = np.arange(lo, hi, dtype=np.longdouble)
        logs = np.log(x)
        roots = np.sqrt(x)
        lam = np.zeros(hi - lo, dtype=np.longdouble)
        ps = primes[np.searchsorted(primes, lo) : np.searchsorted(primes, hi)]
        lam[ps - lo] = np.log(ps.astype(np.longdouble))
        il, ir = np.searchsorted(power_ns, [lo, hi])
        lam[power_ns[il:ir] - lo] = power_lams[il:ir]
        checksum.update(np.asarray(lam, dtype="<f8").tobytes())
        weights = lam / roots
        mass = mass0 + np.cumsum(weights, dtype=np.longdouble)
        moment = moment0 + np.cumsum(weights * logs, dtype=np.longdouble)
        corrected = mass - c
        potential = moment - 2 * corrected * (np.log(corrected / 2) - 1) + b
        actual_error = logs * mass - moment - 4 * roots
        q = corrected / (2 * roots)
        entropy = 4 * roots * (q * np.log(q) - q + 1)
        identity = -actual_error + c * logs + b - entropy
        max_moment_cancellation = max(
            max_moment_cancellation, np.max(np.abs(potential - identity))
        )
        balanced = (2 * roots <= corrected) & (corrected <= 2 * np.sqrt(x + 1))
        if lo == 1:
            balanced[0] = False
        for i in np.flatnonzero(balanced):
            selected.append((int(x[i]), mass[i], moment[i], potential[i], actual_error[i]))
        queries = query_cutoffs[np.searchsorted(query_cutoffs, lo) :
                                np.searchsorted(query_cutoffs, hi)]
        for n in queries:
            i = n - lo
            query_values[str(int(n))] = {"mass": float(mass[i]), "moment": float(moment[i])}
        for k in range(max(1, (lo - 1).bit_length()), hi.bit_length()):
            n = 1 << k
            if lo <= n < hi:
                i = n - lo
                dyadic.append({"X": n, "potential": float(potential[i]),
                               "logAverageError": float(actual_error[i]),
                               "correctedMass": float(corrected[i])})
        mass0, moment0 = mass[-1], moment[-1]
    data = np.array(selected, dtype=np.longdouble)
    return data, dyadic, {
        "vonMangoldtSHA256Float64": checksum.hexdigest(),
        "ordinaryPrimeCount": int(len(primes)),
        "properPrimePowerCount": int(len(powers)),
        "actualEndpointIdentityMaximumFloatingResidual": float(max_moment_cancellation),
        "precision": "numpy.longdouble prefix accumulation; no outward rounding",
        "requestedPrefixValues": query_values,
    }


def drawdown(values):
    return float(np.max(np.maximum.accumulate(values) - values))


def literal_report(data, dyadic, limit):
    c, _ = constants()
    xs, masses, moments, potentials, errors = data.T
    rows = []
    for exponent in range(7, limit.bit_length()):
        lo, hi = 1 << (exponent - 1), 1 << exponent
        indices = np.flatnonzero((xs >= lo) & (xs <= hi))
        if len(indices) < 2:
            rows.append({"X": hi, "balancedCutoffs": len(indices)})
            continue
        il, ir = indices[:-1], indices[1:]
        starts, ends = xs[il], xs[ir]
        gaps = ends - starts
        m = masses[il] - c
        a = masses[ir] - masses[il]
        work = moments[ir] - moments[il] - 2 * np.log(m / 2) * a
        credit = 2 * ((m + a) * np.log1p(a / m) - a)
        joined = work - credit
        change = potentials[ir] - potentials[il]
        separated = 2 * a**2 / m
        negative = np.maximum(-joined, 0)
        positive = np.maximum(joined, 0)
        classifications = []
        for alpha in (0.5, 0.625, 0.75, 0.875):
            active = gaps > starts**alpha
            classifications.append({
                "alpha": alpha,
                "longBlocks": int(active.sum()),
                "longBlockNegativeVariation": float(negative[active].sum()),
                "longBlockSignedTotal": float(joined[active].sum()),
                "longBlockSeparatedMajorant": float(separated[active].sum()),
            })
        worst = np.argsort(joined)[:5]
        rows.append({
            "X": hi,
            "balancedCutoffs": len(indices),
            "minimumPotential": float(potentials[indices].min()),
            "maximumPotential": float(potentials[indices].max()),
            "maximumLogAverageError": float(errors[indices].max()),
            "maximumDrawdown": drawdown(potentials[indices]),
            "cumulativeDrawdownFromFirstBalancedCutoff": drawdown(potentials[: indices[-1] + 1]),
            "maximumBalancedGap": int(gaps.max()),
            "maximumGapPower": float(np.max(np.log(gaps) / np.log(starts))),
            "negativeVariation": float(negative.sum()),
            "positiveVariation": float(positive.sum()),
            "netJoinedChange": float(joined.sum()),
            "centeredWorkTotal": float(work.sum()),
            "entropyTotal": float(credit.sum()),
            "separatedMajorantTotal": float(separated.sum()),
            "jointLedgerMaximumFloatingResidual": float(np.max(np.abs(joined - change))),
            "longBlockClasses": classifications,
            "largestNegativeBlocks": [{
                "start": int(starts[i]), "end": int(ends[i]),
                "logLength": float(np.log(ends[i] / starts[i])),
                "work": float(work[i]), "entropy": float(credit[i]),
                "joinedChange": float(joined[i]),
                "massRelativeErrorAtStart": float((m[i] - 2 * np.sqrt(starts[i])) / m[i]),
            } for i in worst],
        })
    return {"rows": rows, "dyadicCutoffs": dyadic, "totalBalancedCutoffs": len(xs),
            "globalMinimumPotential": float(potentials.min()),
            "globalMaximumDrawdown": drawdown(potentials)}


def continuous_control(beta, gamma, m=1, span=160):
    """A positive literal-density control with a known persistent zero mode.

    density=1 below exp(B); thereafter 1-2m*x^(beta-1)*cos(gamma*log x).
    B=log(2m)/(1-beta), so density>=0 throughout. We solve balance in the
    log variable without ever materializing exp(B). This is NOT primes.
    """
    c, b = map(float, constants())
    B = math.log(2 * m) / (1 - beta)
    alpha = beta - 0.5
    h = complex(alpha, gamma)
    period = 2 * math.pi / gamma

    def scaled_mass_error(v):
        t = B + v
        # (M(exp(t))-c-2exp(t/2))/exp(alpha*t).
        baseline = (-2 - c) * math.exp(-alpha * t)
        mode = np.exp(1j * gamma * t)
        head = np.exp(-alpha * v + 1j * gamma * B)
        return baseline - 2 * m * ((mode - head) / h).real

    def scaled_potential(v):
        t = B + v
        baseline = ((2 + c) * t + 4 + b) * math.exp(-alpha * t)
        mode = np.exp(1j * gamma * t)
        head = np.exp(-alpha * v + 1j * gamma * B)
        # At an exact balanced root q=1, hence no endpoint entropy term.
        return baseline + 2 * m * ((mode - head * (1 + h * v)) / h**2).real

    grid = np.arange(1.0, span + period / 8, period / 8)
    roots = []
    for vl, vr in zip(grid[:-1], grid[1:]):
        if scaled_mass_error(vl) * scaled_mass_error(vr) < 0:
            v = brentq(scaled_mass_error, vl, vr, xtol=1e-12)
            t = B + v
            # Second derivative of the signed signal has sign cos(gamma*t).
            if math.cos(gamma * t) > 0:
                value = scaled_potential(v)
                roots.append({"logCutoff": t, "logCutoffMinusB": v,
                              "sourceNormalizedPotential": value,
                              "logAbsolutePotential": math.log(abs(value)) + alpha * t})
    if len(roots) < 3:
        raise AssertionError("control did not produce enough balanced minima")
    tail = [r for r in roots if r["logCutoffMinusB"] >= span / 2]
    fit = np.polyfit([r["logCutoff"] for r in tail],
                     [r["logAbsolutePotential"] for r in tail], 1)
    return {
        "kind": "continuous positive-density control; not ordinary integer primes",
        "beta": beta, "height": gamma, "multiplicity": m,
        "densityStartsAtLogX": B, "densityNonnegativeByConstruction": True,
        "predictedGrowthExponent": alpha, "observedTailGrowthExponent": float(fit[0]),
        "balancedMinima": len(roots), "firstMinimum": roots[0], "lastMinimum": roots[-1],
        "negativeSourceNormalizedTailMinimum": min(r["sourceNormalizedPotential"] for r in tail),
        "negativeSourceNormalizedTailMaximum": max(r["sourceNormalizedPotential"] for r in tail),
        "passesMassBalance": True,
        "passesExactJointWorkEntropyAccounting": True,
        "passesNonnegativeDensity": True,
        "hasSubpolynomialBalancedFloor": False,
        "reason": "balanced minima grow negatively like X^(beta-1/2)",
    }


def kernel_cases(limit):
    cases = []
    largest = min(9.0, math.log(limit - 1) / 2)
    for L in sorted(set([v for v in (2.0, 4.0, 6.0, 8.0) if v <= largest] + [largest])):
        regular = np.linspace(-L, L, 65)
        regular = regular[np.abs(regular) > 1e-12]  # the origin is an exact zero row
        eta = math.pi / (2 * 60)
        cluster = np.array([L - j * eta for j in range(4)])
        cases.extend([("regular", L, regular),
                      ("height60_cluster", L, np.r_[-cluster, cluster])])
    return cases


def kernel_query_cutoffs(cases):
    values = {1}
    for _, _, nodes in cases:
        times = np.r_[np.abs(nodes), np.abs(nodes[:, None] - nodes[None, :]).ravel()]
        values.update(math.floor(math.exp(float(t))) for t in times)
    return values


def kernel_report(cases, prefixes):
    """Arithmetic time kernel, not the automatically positive Hilbert Gram.

    The off-axis quartet is a synthetic divisor control, not a modification
    claimed to preserve the ordinary-prime Euler product or xi completion.
    """
    c, b = map(float, constants())
    parts = {}

    def psi(t):
        if t < 1e-12:
            return 0.0
        n = math.floor(math.exp(t))
        prefix = prefixes[str(n)]
        q = math.exp(-2 * t)
        with mp.workdps(30):
            lerch = float(mp.lerchphi(q, 2, mp.mpf(1) / 4))
        arch = 4 * math.exp(t / 2) + c * t + b + math.exp(-t / 2) * (4 - lerch / 4)
        prime = t * prefix["mass"] - prefix["moment"]
        parts[t] = {"arch": arch, "prime": prime}
        return arch - prime

    rows = []
    for kind, L, nodes in cases:
        times = np.abs(nodes)
        diffs = np.abs(nodes[:, None] - nodes[None, :])
        unique = sorted(set(map(float, times)) | set(map(float, diffs.ravel())))
        cache = {t: psi(t) for t in unique}
        parts[0.0] = {"arch": 0.0, "prime": 0.0}
        diagonal = np.array([cache[float(t)] for t in times])
        differences = np.array([[cache[float(t)] for t in row] for row in diffs])
        K = diagonal[:, None] + diagonal[None, :] - differences
        K = (K + K.T) / 2
        arch_diag = np.array([parts[float(t)]["arch"] for t in times])
        arch_diff = np.array([[parts[float(t)]["arch"] for t in row] for row in diffs])
        arch_K = arch_diag[:, None] + arch_diag[None, :] - arch_diff
        prime_diag = np.array([parts[float(t)]["prime"] for t in times])
        prime_diff = np.array([[parts[float(t)]["prime"] for t in row] for row in diffs])
        prime_K = prime_diag[:, None] + prime_diag[None, :] - prime_diff
        eigenvalues = np.linalg.eigvalsh(K)
        controls = []
        for alpha in (0.4, 0.49995):
            mode = complex(60, alpha)

            def toy(t):
                return (4 * (1 - np.cos(mode * t)) / mode**2).real

            toy_diag = toy(times)
            toy_diffs = toy(diffs)
            toy_K = toy_diag[:, None] + toy_diag[None, :] - toy_diffs
            detection = None
            for amplitude in np.geomspace(1e-6, 10, 141):
                mixed = K + amplitude * toy_K
                vals, vecs = np.linalg.eigh(mixed)
                point_values = np.array(list(cache.values())) + amplitude * toy(np.array(unique))
                if vals[0] < -1e-9 and point_values.min() >= -1e-12:
                    v = vecs[:, 0]
                    ds = np.diag(mixed)
                    pair_min = (ds[:, None] + ds[None, :] - np.sqrt(
                        (ds[:, None] - ds[None, :])**2 + 4 * mixed**2)) / 2
                    pair_min[np.tril_indices(len(nodes))] = np.inf
                    i, j = np.unravel_index(np.argmin(pair_min), pair_min.shape)
                    detection = {
                        "amplitude": float(amplitude), "minimumEigenvalue": float(vals[0]),
                        "minimumScalarAtAllSampledArguments": float(point_values.min()),
                        "minimumScalarAtNonzeroSampledArguments": float(
                            point_values[np.array(unique) > 1e-12].min()),
                        "minimumTwoNodePrincipalEigenvalue": float(pair_min[i, j]),
                        "worstTwoNodeTimes": [float(nodes[i]), float(nodes[j])],
                        "negativeDespiteEveryTwoNodePrincipalMatrixNonnegative":
                            bool(pair_min[i, j] >= -1e-12),
                        "arithmeticArchimedeanQuadratic": float(v @ arch_K @ v),
                        "arithmeticSignedPrimeQuadratic": float(-v @ prime_K @ v),
                        "arithmeticJoinedQuadratic": float(v @ K @ v),
                        "syntheticModeQuadratic": float(amplitude * (v @ toy_K @ v)),
                        "directSignedQuadratic": float(v @ mixed @ v),
                        "witnessNodes": nodes.tolist(), "witnessWeights": v.tolist(),
                    }
                    break
            controls.append({"kind": "synthetic off-axis quartet added to arithmetic kernel",
                             "height": 60, "horizontalOffset": alpha,
                             "detectedDespiteSampledScalarNonnegativity": detection})
        unit_controls = []
        for gamma in (200, 400, 600, 800, 1000, 1200, 1600):
            mode = complex(gamma, 0.49995)
            toy_values = (4 * (1 - np.cos(mode * np.array(unique))) / mode**2).real
            toy_diag = (4 * (1 - np.cos(mode * times)) / mode**2).real
            toy_diff = (4 * (1 - np.cos(mode * diffs)) / mode**2).real
            mixed = K + toy_diag[:, None] + toy_diag[None, :] - toy_diff
            vals, vecs = np.linalg.eigh(mixed)
            ds = np.diag(mixed)
            pair_min = (ds[:, None] + ds[None, :] - np.sqrt(
                (ds[:, None] - ds[None, :])**2 + 4 * mixed**2)) / 2
            pair_min[np.tril_indices(len(nodes))] = np.inf
            scalar_min = float((np.array(list(cache.values())) + toy_values).min())
            if vals[0] < -1e-9 and scalar_min >= -1e-12 and pair_min.min() >= -1e-12:
                v = vecs[:, 0]
                unit_controls.append({
                    "kind": "synthetic quartet with unit multiplicity; not an actual zeta zero",
                    "height": gamma, "horizontalOffset": 0.49995, "amplitude": 1,
                    "minimumScalarAtNonzeroSampledArguments": float(
                        (np.array(list(cache.values())) + toy_values)[np.array(unique) > 1e-12].min()),
                    "minimumTwoNodePrincipalEigenvalue": float(pair_min.min()),
                    "minimumEigenvalue": float(vals[0]),
                    "arithmeticArchimedeanQuadratic": float(v @ arch_K @ v),
                    "arithmeticSignedPrimeQuadratic": float(-v @ prime_K @ v),
                    "arithmeticJoinedQuadratic": float(v @ K @ v),
                    "directSignedQuadratic": float(v @ mixed @ v),
                    "witnessNodes": nodes.tolist(), "witnessWeights": v.tolist(),
                })
        rows.append({"nodeFamily": kind, "halfWindow": L, "dimension": len(nodes),
                     "maximumPrimeCutoff": math.floor(math.exp(2 * L)),
                     "minimumArithmeticEigenvalue": float(eigenvalues[0]),
                     "minimumArithmeticScalarAtSampledArguments": min(cache.values()),
                     "controls": controls, "unitMultiplicityControlsPassingAllPairTests": unit_controls})
    return {"kernel": "Psi(t)+Psi(s)-Psi(t-s), full arithmetic completion",
            "automaticHilbertGramUsed": False, "rows": rows,
            "fullOperatorPositivityProved": False, "finiteEigenvaluesCertified": False}


def self_checks():
    data, _, _ = literal_prefixes(8192, 257)
    data_other, _, _ = literal_prefixes(8192, 2048)
    if not np.array_equal(data[:, 0], data_other[:, 0]):
        raise AssertionError("stream chunk size changed balance classification")
    if np.max(np.abs(data[:, 1:] - data_other[:, 1:])) > 1e-11:
        raise AssertionError("stream prefix bookkeeping is unstable")
    _, _, small = literal_prefixes(128, 31, (2, 4, 8, 9, 12, 27, 64, 128))

    def direct_lam(n):
        for p in range(2, n + 1):
            if n % p == 0:
                a = n
                while a % p == 0:
                    a //= p
                return math.log(p) if a == 1 else 0.0
        return 0.0

    for n, row in small["requestedPrefixValues"].items():
        expected_mass = math.fsum(direct_lam(k) / math.sqrt(k) for k in range(2, int(n) + 1))
        expected_moment = math.fsum(direct_lam(k) * math.log(k) / math.sqrt(k)
                                  for k in range(2, int(n) + 1))
        if abs(row["mass"] - expected_mass) > 1e-13 or abs(row["moment"] - expected_moment) > 1e-12:
            raise AssertionError("literal prime-power query disagrees with direct factorization")
    control = continuous_control(0.9, 60, span=100)
    if abs(control["observedTailGrowthExponent"] - 0.4) > 1e-7:
        raise AssertionError("off-critical control failed its predicted growth")
    return {"chunkSizeReplay": True, "controlGrowthReplay": True,
            "finiteVonMangoldtIncludesProperPowers": True, "directFactorizationQueryReplay": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=1 << 24)
    parser.add_argument("--chunk-size", type=int, default=1 << 19)
    parser.add_argument("--output", type=Path,
                        default=Path(".lake/suzuki-joint-excursions/probe.json"))
    args = parser.parse_args()
    if args.limit < 128 or args.limit & (args.limit - 1) or args.chunk_size < 1:
        parser.error("limit must be a power of two >=128; chunk size positive")
    checks = self_checks()
    cases = kernel_cases(args.limit)
    data, dyadic, provenance = literal_prefixes(args.limit, args.chunk_size,
                                               kernel_query_cutoffs(cases))
    report = {
        "scope": "optional floating research probe; no certificate or all-height estimate",
        "maximumLiteralCutoff": args.limit,
        "fullPrimePowersRetained": True,
        "joinedBeforeNormOrSignSplit": True,
        "provenance": provenance, "selfChecks": checks,
        "literal": literal_report(data, dyadic, args.limit),
        "controls": [continuous_control(0.9, 60), continuous_control(0.99995, 60)],
        "crossScaleArithmeticKernel": kernel_report(cases, provenance["requestedPrefixValues"]),
        "independentArithmeticFloorProved": False,
        "newZeroFreeRegionProved": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"report": str(args.output), "checks": checks,
                      "lastLiteralRows": report["literal"]["rows"][-2:],
                      "controls": report["controls"]}, indent=2))


if __name__ == "__main__":
    main()
