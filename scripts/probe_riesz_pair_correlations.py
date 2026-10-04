#!/usr/bin/env python3
"""Optional pair-level discovery on the unpaid exact factorial-prefix sum.

Actual proven-prime cache only. Preserve the factorial weight, moving length,
complete-period mask and phase. Structural features use gcds, residues,
quadratic reciprocity and explicit partial factor profiles of p+-q. No
individual-prime feature is mistaken for a genuine pair interaction.

Permutation ranks are exploratory diagnostics, not arithmetic bounds or
calibrated population p-values. Leg phases are permuted within marginal
log-position quartiles; Cartesian pair incidences are never independent
samples. Equal box weighting is a discovery convention, not an estimate of
the global carrier. Nothing runs in ordinary build/CI.
"""

import argparse
from collections import Counter
import hashlib
import json
import math
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
import numpy as np
from flint import arb, ctx

import probe_riesz_pair_prefix as prefix
import probe_riesz_pair_structure as pair


MODULI = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
TRIAL_PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31)
REGRESSION_HEIGHTS = ('54', '65', '100', '142')
DISCOVERY_HEIGHTS = ('10^10000', '10^12000')
VALIDATION_HEIGHTS = ('10^20000', '10^24000')


def parse_height(label):
    m = re.fullmatch(r'10\^([0-9]+)', label)
    value = 10**int(m[1]) if m else int(label)
    assert value >= 54
    return value


def integer_height_phase(primes, y):
    """Rigorous ball argument reduction before sin/cos, even at 10^24000.

    Automatic Arb trig evaluation can return [-1,1] at extreme arguments.
    The uniquely certified integer multiple of 2*pi is subtracted with the
    FULL working precision; the phase is never frozen or computed in float.
    """
    period = 2*arb.pi()
    values = []
    radius = 0.
    for p in primes:
        v = -y*arb(p).log()
        quotient = (v/period).floor().unique_fmpz()
        assert quotient is not None
        angle = v-period*quotient
        assert angle >= 0 and angle < period
        re, im = angle.cos(), angle.sin()
        radius = max(radius, float(re.rad()), float(im.rad()))
        values.append(complex(float(re.mid()), float(im.mid())))
    upper = math.nextafter(radius, math.inf)
    assert upper < 1e-100
    return np.array(values), upper


def formula_value(node, L):
    tag, *args = node
    if tag == 'natural':
        return arb(args[0])
    if tag == 'variable':
        return L
    a = formula_value(args[0], L)
    if tag == 'log':
        return a.log()
    if tag == 'exp':
        return a.exp()
    b = formula_value(args[1], L)
    if tag == 'add':
        return a+b
    if tag == 'sub':
        return a-b
    if tag == 'mul':
        return a*b
    if tag == 'div':
        return a/b
    if tag == 'power':
        return a**b
    if tag == 'maximum':
        return a if a > b else b if b > a else a.union(b)
    if tag == 'minimum':
        return a if a < b else b if b < a else a.union(b)
    raise ValueError(tag)


def height_coverage(labels):
    formulas = json.loads(Path('docs/zero-free-regions/formulas.json').read_text())
    result = []
    for label in labels:
        ctx.prec = 256
        L = arb(parse_height(label)).log()
        widths = {name: formula_value(expr, L) for name, expr in formulas['curves'].items()}
        result.append(dict(height=label, logHeight=float(L.mid()),
            widths={name: dict(mid=float(v.mid()), interval=str(v)) for name, v in widths.items()},
            allDisplayedWidthsBelowTargetBetaGap=all(v < arb(1)/20000 for v in widths.values()),
            targetBeta='99995/100000', proofOfAnyNewZeroFreeRegion=False))
    for record in result:
        if record['height'] in DISCOVERY_HEIGHTS+VALIDATION_HEIGHTS:
            assert record['allDisplayedWidthsBelowTargetBetaGap']
    return result


def valuation(n, p):
    k = 0
    while n % p == 0:
        n //= p
        k += 1
    return k


def symbol(a, p):
    v = pow(a % p, (p-1)//2, p)
    assert v in (1, p-1)
    return 1 if v == 1 else -1


def pair_features(p, q):
    assert p > q > 2
    gap, total = p-q, p+q
    # This would be a spurious discovery feature: it is identically two.
    assert math.gcd(gap, total) == 2
    direct, reverse = symbol(q, p), symbol(p, q)
    reciprocity = -1 if p % 4 == q % 4 == 3 else 1
    assert direct*reverse == reciprocity
    f = dict(legendre_small_in_large=direct, legendre_large_in_small=reverse,
             reciprocity_product=reciprocity,
             euclidean_remainder_fraction=(p % q)/q)
    for sp, sq, name in ((-1, -1, 'minus_minus'), (1, 1, 'plus_plus'),
                         (-1, 1, 'minus_plus'), (1, -1, 'plus_minus')):
        g = math.gcd(p+sp, q+sq)
        f['gcd_'+name+'_log'] = math.log(g)
        f['gcd_'+name+'_v2'] = valuation(g, 2)
        f['gcd_'+name+'_v3'] = valuation(g, 3)
        f['gcd_'+name+'_v5'] = valuation(g, 5)
        f['gcd_'+name+'_beyond_two'] = int(g > 2)
    for m in MODULI:
        f['same_residue_mod_'+str(m)] = int((p-q) % m == 0)
        f['opposite_residue_mod_'+str(m)] = int((p+q) % m == 0)
    for n, name in ((gap, 'gap'), (total, 'sum')):
        residual = n
        smooth_log = 0.
        known_divisor_log = 0.
        for r in TRIAL_PRIMES:
            v = valuation(n, r)
            residual //= r**v
            smooth_log += v*math.log(r)
            known_divisor_log += math.log(v+1)
            f[name+'_v'+str(r)] = v
        assert residual*math.prod(r**f[name+'_v'+str(r)] for r in TRIAL_PRIMES) == n
        f[name+'_known_log_part'] = smooth_log
        f[name+'_known_divisor_log'] = known_divisor_log
        # No unfactored residual is declared prime or squarefree.
    return f


def project_geometry(f, weights, cells):
    """Remove BOTH marginals and coarse total log in one weighted projection.

    Sequential demeaning could reintroduce marginal structure. Verify the
    normal equations, including all dependent columns, instead.
    """
    rows, cols, count = f.shape
    i, j = np.indices((rows, cols))
    _, c = np.unique(cells.ravel(), return_inverse=True)
    design = np.concatenate([np.eye(rows)[i.ravel()], np.eye(cols)[j.ravel()],
                             np.eye(int(c.max())+1)[c]], axis=1)
    w = np.abs(weights).ravel()
    w /= w.sum()
    flat = f.reshape(-1, count)
    sw = np.sqrt(w)
    beta, *_ = np.linalg.lstsq(sw[:, None]*design, sw[:, None]*flat, rcond=None)
    residual = flat-design@beta
    error = float(np.max(np.abs(design.T@(w[:, None]*residual))))
    assert error < 1e-10, error
    return residual.reshape(f.shape), error


def prepare(cache):
    samples = json.loads(cache.read_text())
    boxes = []
    seen_features = None
    reciprocity_counts = Counter()
    for row in samples['rows']:
        N = row['N']
        ctx.prec = max(1200, math.ceil(2*N/math.log(2))+256)
        assert row['left']['provedByFLINT'] and row['right']['provedByFLINT']
        p = [int(v) for v in row['left']['primes']]
        q = [int(v) for v in row['right']['primes']]
        assert min(p) > max(q) > N**16
        xl, zl = [arb(v).log() for v in p], [arb(v).log() for v in q]
        x = np.array([float(v.mid()) for v in xl])[:, None]
        z = np.array([float(v.mid()) for v in zl])[None, :]
        lo, hi = arb(1971)*N/1000+1, arb(2029)*N/1000-1
        assert all(a+b > lo and a+b <= hi for a in xl for b in zl)
        c = pair.coefficient(N, np.array(p, dtype=object)[:, None],
                             np.array(q, dtype=object)[None, :], x, z)
        assert np.all(c['central'])
        Q, _ = prefix.comparison(N, pair.parameters(N)['L'], x, z)
        d = Q-c['selberg']
        ref = 2*N+2
        weights = (d/N)*np.exp(N*np.log1p((c['T']-ref)/ref)-1.5*(c['T']-ref))
        structures = [[pair_features(a, b) for b in q] for a in p]
        names = list(structures[0][0])
        assert seen_features in (None, names)
        seen_features = names
        f = np.array([[[a[n] for n in names] for a in r] for r in structures])
        for r in structures:
            for a in r:
                reciprocity_counts[(a['legendre_small_in_large'], a['legendre_large_in_small'])] += 1
        boxes.append(dict(row=row, p=p, q=q, x=x, z=z, xl=xl, zl=zl, T=c['T'], weights=weights,
                          base=f, structures=structures))
    # Standardisation and random features depend on arithmetic only.
    pooled = np.concatenate([b['base'].reshape(-1, len(seen_features)) for b in boxes])
    means, sd = pooled.mean(axis=0), pooled.std(axis=0)
    keep = sd > 1e-12
    names = [n for n, k in zip(seen_features, keep) if k]
    means, sd = means[keep], sd[keep]
    rng = np.random.default_rng(943716)
    projections = rng.normal(size=(len(names), 96))/math.sqrt(len(names))
    offsets = rng.uniform(0, 2*math.pi, size=96)
    # Unknown nonlinear structures, with fixed phase-free projections.
    all_names = names+[f'arithmetic_rff_{i:03}' for i in range(96)]
    for b in boxes:
        base = (b['base'][..., keep]-means)/sd
        nonlinear = np.cos(base@projections+offsets)
        f = np.concatenate([base, nonlinear], axis=2)
        cells = np.floor((b['T']-2*b['row']['N'])*16).astype(int)
        b['features'], b['projection_error'] = project_geometry(f, b['weights'], cells)
    return boxes, all_names, reciprocity_counts


def stratified_permutations(values, log_values, rng, count):
    groups = np.array_split(np.argsort(log_values), 4)
    out = np.repeat(values[None, :], count, axis=0)
    for i in range(count):
        for g in groups:
            out[i, g] = values[rng.permutation(g)]
    return out


def audit(boxes, names, seed, label, permutations):
    y = parse_height(label)
    use = [b for b in boxes if b['row']['seed'] == seed]
    observed = np.zeros(len(names), dtype=complex)
    null = np.zeros((permutations, len(names)), dtype=complex)
    variance = np.zeros(len(names))
    records = []
    entropy = int(hashlib.sha256(label.encode()).hexdigest()[:16], 16)
    rng = np.random.default_rng(seed+entropy+101)
    for b in use:
        N = b['row']['N']
        # Exact integer height, including 10^24000: no binary64 conversion.
        ctx.prec = max(1200, math.ceil(2*N/math.log(2))+256, y.bit_length()+1024)
        pl, pr = integer_height_phase(b['p'], y), integer_height_phase(b['q'], y)
        # Existing interiorLabels_subset_completePeriods applies at EVERY
        # height >=54. Avoid computing an astronomically large period index.
        mask = np.ones(b['T'].shape, dtype=bool)
        if label in REGRESSION_HEIGHTS:
            _, direct_mask = pair.complete_periods(N, b['T'], y)
            assert np.array_equal(mask, direct_mask)
        w = np.where(mask, b['weights'], 0.)
        denominator = float(np.abs(w).sum())
        assert denominator > 0
        w = w/denominator
        f = b['features']
        atoms = pl[0][:, None]*pr[0][None, :]
        observed += np.einsum('ij,ijf->f', w*atoms, f)/len(use)
        variance += np.einsum('ij,ijf->f', np.abs(w), f*f)/len(use)
        pp = stratified_permutations(pl[0], b['x'][:, 0], rng, permutations)
        qq = stratified_permutations(pr[0], b['z'][0], rng, permutations)
        phase_grid = pp[:, :, None]*qq[:, None, :]
        null += (phase_grid.reshape(permutations, -1)@
                 (w[:, :, None]*f).reshape(-1, len(names)))/len(use)
        records.append(dict(box=b['row']['box'], N=N,
            actualRetainedPairIncidences=int(mask.sum()),
            signedSampleCompression=pair.encode(complex((w*atoms).sum())),
            coefficientOverNRange=[float((b['weights']/np.exp(
                N*np.log1p((b['T']-(2*N+2))/(2*N+2))-1.5*(b['T']-(2*N+2)))).min()),
                                   float((b['weights']/np.exp(
                N*np.log1p((b['T']-(2*N+2))/(2*N+2))-1.5*(b['T']-(2*N+2)))).max())],
            phaseBallRadiusUpper=max(pl[1], pr[1]),
            binary64PhaseMidpointRoundingIncludedInBall=False,
            geometryProjectionNormalEquationError=b['projection_error'],
            phasePrecisionBits=ctx.prec,
            completePeriodSupportVerifiedViaStrictInterior=True,
            rawPrimeCountingWeightEstimated=False))
    valid = variance > 1e-20
    scale = np.sqrt(np.maximum(variance, 1e-20))
    effect = np.abs(observed)/scale
    effect[~valid] = 0
    null_effect = np.abs(null)/scale[None, :]
    null_effect[:, ~valid] = 0
    maxima = null_effect.max(axis=1)
    adjusted = (1+np.sum(maxima[:, None] >= effect[None, :], axis=0))/(permutations+1)
    raw = (1+np.sum(null_effect >= effect[None, :], axis=0))/(permutations+1)
    ranking = np.argsort(effect)[::-1]
    scores = [dict(feature=names[i], standardizedEffect=float(effect[i]),
        signedCorrelation=pair.encode(complex(observed[i]/scale[i])),
        rawPermutationRank=float(raw[i]), maxStatisticPermutationRank=float(adjusted[i]))
        for i in ranking]
    return dict(seed=seed, height=label, testedFeatures=int(valid.sum()),
        maxStatisticFlagsAt005=[s for s in scores if s['maxStatisticPermutationRank'] <= .05],
        topFeatures=scores[:12], allScores=scores, boxDiagnostics=records,
        permutationRanksAreExploratory=True, legDependencePreserved=True,
        nullPreservesActualCharacter=False)


def run(cache, permutations):
    boxes, names, reciprocity = prepare(cache)
    seeds = sorted(set(b['row']['seed'] for b in boxes))
    heights = REGRESSION_HEIGHTS+DISCOVERY_HEIGHTS+VALIDATION_HEIGHTS
    coverage = height_coverage(heights)
    results = []
    for seed in seeds:
        for label in heights:
            print(json.dumps(dict(stage='phase scan', seed=seed, height=label)), flush=True)
            results.append(audit(boxes, names, seed, label, permutations))
    replications = []
    for y in heights:
        matching = [r for r in results if r['height'] == y]
        flags = [{s['feature'] for s in r['maxStatisticFlagsAt005']} for r in matching]
        common = set.intersection(*flags)
        for name in sorted(common):
            scores = [next(s for s in r['allScores'] if s['feature'] == name) for r in matching]
            replications.append(dict(height=y, feature=name, seeds=seeds,
                signedCorrelations=[s['signedCorrelation'] for s in scores]))
    return dict(classification='Pair-specific arithmetic structure scan of unpaid exact prefix; discovery only',
        sources=[prefix.digest(p) for p in ('scripts/probe_riesz_pair_correlations.py',
            'scripts/probe_riesz_pair_prefix.py','scripts/probe_riesz_pair_structure.py',
            'RiemannGaussian/ZetaRieszPairPrefixPayment.lean',
            'docs/zero-free-regions/formulas.json',cache)],
        coverage=dict(actualPairIncidences=sum(b['T'].size for b in boxes),
            distinctActualPrimes=len({int(p) for b in boxes for side in ('left','right')
                                     for p in b['row'][side]['primes']}),
            sampleOrders=sorted(set(b['row']['N'] for b in boxes)),seeds=seeds,
            regressionHeights=REGRESSION_HEIGHTS, discoveryHeights=DISCOVERY_HEIGHTS,
            heldOutHeights=VALIDATION_HEIGHTS,
            countTwoOnly=True, polynomialSmallCofactorsSkipped=True,
            wholePopulationEnumerated=False, sharedPrimePairsNotIndependent=True,
            featureNames=names, baseStructuralFeatures=len(names)-96,
            genericNonlinearArithmeticFeatures=96, factorTrialLimit=31,
            factorialKernelFrozen=False, fullProductPhaseRetained=True),
        exactFiniteChecks=dict(gcdOfGapAndSumIdenticallyTwo=True,
            quadraticReciprocityVerified=True,
            reciprocalSymbolPopulation=[dict(smallInLarge=a,largeInSmall=b,count=count)
                for (a,b),count in sorted(reciprocity.items())],
            unfactoredResidualPrimalityAsserted=False),
        zeroFreeCoverage=coverage,
        conventions=dict(allDiscoveryFeaturesBuiltWithoutPhase=True,
            weightedJointMarginalAndTotalLogProjection=True,
            totalLogCoarseCellWidth='1/16', marginalPermutationQuartiles=4,
            permutations=permutations, perBoxSignedWeightL1Normalization=True,
            boxesEquallyWeightedNotGlobalCarrier=True,
            permutationRanksNotPopulationPValues=True,
            maxStatisticAdjustmentAcrossAllFeatures=True),
        results=results,sameHeightSeedReplications=replications,
        independentSignedMainBound=False,floor=False,zeroExclusion=False,RH=False)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--cache', type=Path, default=Path('.lake/riesz-pair-structure/scan.primes.json'))
    ap.add_argument('--output', type=Path, default=Path('.lake/riesz-pair-correlations/scan.json'))
    ap.add_argument('--permutations', type=int, default=255)
    args = ap.parse_args()
    assert args.permutations >= 63
    result = run(args.cache, args.permutations)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(output=str(args.output),
        pairIncidences=result['coverage']['actualPairIncidences'],
        testedFeatures=len(result['coverage']['featureNames']),
        flags=sum(len(r['maxStatisticFlagsAt005']) for r in result['results']),
        sameHeightReplications=result['sameHeightSeedReplications'],floor=False)))


if __name__ == '__main__':
    main()
