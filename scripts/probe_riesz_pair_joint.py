#!/usr/bin/env python3
"""Five optional joined tests of the unpaid literal factorial-prefix sum.

Actual proven primes, exact moving length and full product phase. The suite
joins coefficient signs before reporting responses and retains correlated
prime marginals. Its equal-box/L1 normalization is a discovery convention,
NOT an estimate or bound for the complete arithmetic carrier. No floor
credit is inferred from finite SVDs, matching costs or empirical ranks.
"""

import argparse
from collections import defaultdict
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
from flint import arb, ctx, fmpz
from scipy.stats import binom

import probe_riesz_pair_correlations as correlations
import probe_riesz_pair_prefix as prefix
import probe_riesz_pair_structure as pair


HEIGHTS = ('100', '142', '10^10000', '10^20000')


def reduced_phase(argument):
    period = 2*arb.pi()
    integer = (argument/period).floor().unique_fmpz()
    assert integer is not None
    angle = argument-period*integer
    assert 0 <= angle < period
    real, imag = angle.cos(), angle.sin()
    radius = math.nextafter(max(float(real.rad()), float(imag.rad())), math.inf)
    assert 0 < radius < 1e-100
    return complex(float(real.mid()), float(imag.mid())), radius


def exact_period_mask(box, height):
    """Literal complete-period mask; never use huge float period indices."""
    width = 2*arb.pi()/height
    N = box['N']
    lower, upper = arb(1971)*N/1000, arb(2029)*N/1000
    mask = np.zeros(box['T'].shape, dtype=bool)
    # The stored geometry balls were computed before the astronomical
    # height was known. Recompute logs at the FULL current precision.
    xl = [arb(p).log() for p in box['p']]
    zl = [arb(q).log() for q in box['q']]
    for i, x in enumerate(xl):
        for j, z in enumerate(zl):
            index = ((x+z)/width).floor().unique_fmpz()
            assert index is not None
            left, right = index*width, (index+1)*width
            # Comparisons must be decisive, not silently classified false.
            assert left >= lower or left < lower
            assert right <= upper or right > upper
            mask[i, j] = left >= lower and right <= upper
    return mask & box['coefficient']['central']


def prepare_row(row, identifier, kind):
    N = row['N']
    ctx.prec = max(1200, math.ceil(2*N/math.log(2))+256)
    p = [int(v) for v in row['left']['primes']]
    q = [int(v) for v in row['right']['primes']]
    # Older dense balanced cache stores the larger leg on the right.
    if min(q) > max(p):
        p, q = q, p
    assert min(p) > max(q) > N**16
    assert row['left']['provedByFLINT'] and row['right']['provedByFLINT']
    xl, zl = [arb(p).log() for p in p], [arb(q).log() for q in q]
    x = np.array([float(v.mid()) for v in xl])[:, None]
    z = np.array([float(v.mid()) for v in zl])[None, :]
    c = pair.coefficient(N, np.array(p, dtype=object)[:, None],
                         np.array(q, dtype=object)[None, :], x, z)
    Q, _ = prefix.comparison(N, pair.parameters(N)['L'], x, z)
    # Off the original radial flag, prefixCoefficient subtracts the exact
    # completed coefficient. Those labels are also checked by period mask.
    L, T = pair.parameters(N)['L'], c['T']
    riesz = L-np.maximum(L-x, 0)-np.maximum(L-z, 0)+np.maximum(L-T, 0)
    completed = -T*riesz/L
    Q = Q-np.where(c['central'], 0., completed)
    coefficient = Q-c['selberg']
    ref = 2*N+2
    weights = coefficient/N*np.exp(N*np.log1p((T-ref)/ref)-1.5*(T-ref))
    strict = all(a+b > arb(1971)*N/1000+1 and
                 a+b <= arb(2029)*N/1000-1 for a in xl for b in zl)
    products = np.array([[a*b for b in q] for a in p], dtype=object)
    return dict(id=identifier, kind=kind, N=N, seed=row['seed'], row=row,
        p=p, q=q, xl=xl, zl=zl, x=x, z=z, T=T, coefficient=c,
        prefixDefectCoefficient=coefficient, weights=weights, ref=ref,
        products=products, strictInterior=strict,
        meanShare=float(np.mean(z/T)))


def prepare(old, new, balanced):
    source = json.loads(old.read_text())
    fresh = json.loads(new.read_text())
    assert fresh['complete'] and len(fresh['rows']) == len(fresh['plan'])
    # Verify frozen producer/helper pins, without repeating its long run.
    for key, path in (('generator', 'scripts/sample_riesz_pair_joint.py'),
                      ('sampler', 'scripts/probe_riesz_balanced_prime_sampling.py'),
                      ('shares', 'scripts/probe_riesz_pair_structure.py')):
        assert prefix.digest(path)['sha256'] == fresh['sourceSha256'][key]
    dense = json.loads(balanced.read_text())
    boxes = []
    for row in source['rows']:
        boxes.append(prepare_row(row, f"old-{row['N']}-{row['seed']}-{row['box']}", 'bulk'))
    for row in fresh['rows']:
        boxes.append(prepare_row(row, row['id'], row['kind']))
    for row in dense['rows']:
        boxes.append(prepare_row(row, f"dense-{row['N']}-{row['seed']}", 'dense_balanced'))
    assert len({b['id'] for b in boxes}) == len(boxes)
    return boxes


def decomposition(w):
    U, sigma, V = np.linalg.svd(w, full_matrices=False)
    reconstructed = (U*sigma)@V
    assert np.max(np.abs(reconstructed-w)) < 1e-11*max(1., np.abs(w).max())
    return U, sigma, V


def response_curve(box, w, pl, qr, delta):
    """Exact finite SVD coupling, with only the common radial rotation removed.

    Each leg's phase remains inside its weighted finite prime sum. No
    complete-leg limit is substituted through any mask.
    """
    U, sigma, V = decomposition(w)
    # The two centres sum to the SAME reference for every box of this order.
    xp = box['row']['left']['logLower']+1
    if min(map(int, box['row']['right']['primes'])) > max(map(int, box['row']['left']['primes'])):
        xp = box['row']['right']['logLower']+1
    zq = box['ref']-xp
    left = (np.exp(-1j*delta[:, None]*(box['x'][:, 0]-xp))*pl[None, :])@U
    right = (np.exp(-1j*delta[:, None]*(box['z'][0]-zq))*qr[None, :])@V.T
    modes = left*right*sigma[None, :]
    curve = modes.sum(axis=1)
    for k in sorted({0, len(delta)//4, len(delta)//2, len(delta)-1}):
        direct = np.sum(w*pl[:, None]*qr[None, :]*
                        np.exp(-1j*delta[k]*(box['T']-box['ref'])))
        assert abs(curve[k]-direct) < 2e-11
    total_energy = float(np.dot(sigma, sigma))
    leading = sigma[0]*U[:, 0, None]*V[None, 0, :]
    summary = dict(rankOneSquaredEnergyFraction=float(sigma[0]**2/total_energy) if total_energy else 0.,
        rankOneRemainderL1=float(np.abs(w-leading).sum()),
        maximumEvaluatedSignedRemainder=float(np.abs(curve-modes[:, 0]).max()),
        leadingPrimeFactorsAtBase=[pair.encode(complex(left[len(delta)//2, 0])),
                                   pair.encode(complex(right[len(delta)//2, 0]))],
        leadingCouplingAtBase=pair.encode(complex(modes[len(delta)//2, 0])),
        evaluatedModeCount=len(sigma), exactFiniteReplay=True,
        completePrimeLegConvergenceUsed=False, globalCarrierBound=False)
    return curve, modes[:, 0], summary


def coherence(positive, negative):
    denominator = math.sqrt(float(np.vdot(positive, positive).real)*
                            float(np.vdot(negative, negative).real))
    return float(np.vdot(negative, positive).real)/denominator if denominator else None


def coherence_reference(marginals, delta, positive, negative, permutations):
    """Shared-leg permutations: reference ranks, NOT population p-values."""
    # Downsample only the smooth demodulated profiles; the carrier itself
    # and full discovery grid remain unchanged.
    indices = np.linspace(0, len(delta)-1, min(257, len(delta)), dtype=int)
    grid = delta[indices]
    P = np.zeros((permutations, len(grid)), dtype=complex)
    Q = np.zeros_like(P)
    label_hash = int(hashlib.sha256(str(marginals[0][0]['N']).encode()).hexdigest()[:8], 16)
    rng = np.random.default_rng(marginals[0][0]['seed']+label_hash+81731)
    for box, w, pl, qr in marginals:
        pp = correlations.stratified_permutations(pl, box['x'][:, 0], rng, permutations)
        qq = correlations.stratified_permutations(qr, box['z'][0], rng, permutations)
        xp = box['row']['left']['logLower']+1
        zq = box['ref']-xp
        left = np.exp(-1j*grid[:, None]*(box['x'][:, 0]-xp))[None, :, :]*pp[:, None, :]
        right = np.exp(-1j*grid[:, None]*(box['z'][0]-zq))[None, :, :]*qq[:, None, :]
        P += np.sum((left@np.maximum(w, 0))*right, axis=2)
        Q += np.sum((left@np.minimum(w, 0))*right, axis=2)
    denominators = np.sqrt(np.sum(np.abs(P)**2, axis=1)*np.sum(np.abs(Q)**2, axis=1))
    assert np.all(denominators > 0)
    values = np.sum(np.real(P*np.conj(Q)), axis=1)/denominators
    observed = coherence(positive[indices], negative[indices])
    rank = (1+int(np.sum(values <= observed)))/(permutations+1)
    return dict(observedReferenceGridCoherence=observed, negativeCoherenceReferenceRank=rank,
        referenceRange=[float(values.min()), float(values.max())],
        referenceMedian=float(np.median(values)), permutations=permutations,
        referenceGridPoints=len(indices), legDependencePreserved=True,
        marginalLogQuartilesPreserved=True, literalCharacterNotPreserved=True,
        diagnosticRankNotCalibratedPopulationPValue=True)


def profile(use, label, delta, permutations=0):
    y = correlations.parse_height(label)
    positive = np.zeros(len(delta), dtype=complex)
    negative = np.zeros(len(delta), dtype=complex)
    leading = np.zeros(len(delta), dtype=complex)
    blocks, marginals = [], []
    shifted_replay_error = 0.
    for b in use:
        assert b['strictInterior']
        ctx.prec = max(1200, y.bit_length()+1024,
                       math.ceil(2*b['N']/math.log(2))+256)
        pl, erp = correlations.integer_height_phase(b['p'], y)
        qr, erq = correlations.integer_height_phase(b['q'], y)
        for offset in (float(delta[0]), float(delta[-1])):
            exact = reduced_phase(-(arb(y)+arb(offset))*arb(b['p'][0]*b['q'][0]).log())[0]
            via_identity = pl[0]*qr[0]*np.exp(-1j*offset*b['T'][0, 0])
            shifted_replay_error = max(shifted_replay_error, abs(exact-via_identity))
            assert abs(exact-via_identity) < 2e-11
        w = b['weights']/np.abs(b['weights']).sum()/len(use)
        all_response, main, summary = response_curve(b, w, pl, qr, delta)
        plus, _, _ = response_curve(b, np.maximum(w, 0), pl, qr, delta)
        minus, _, _ = response_curve(b, np.minimum(w, 0), pl, qr, delta)
        assert np.max(np.abs(all_response-plus-minus)) < 2e-11
        positive += plus
        negative += minus
        leading += main
        blocks.append(dict(box=b['id'], phaseBallRadiusUpper=max(erp, erq), **summary))
        marginals.append((b, w, pl, qr))
    joined = positive+negative
    separate = np.abs(positive)+np.abs(negative)
    cancellation = np.divide(separate-np.abs(joined), separate,
                             out=np.zeros_like(separate), where=separate > 1e-14)
    cross = np.real(positive*np.conj(negative))
    zero = len(delta)//2
    re_original = np.real(joined*np.exp(-1j*delta*use[0]['ref']))
    kmax = int(np.argmax(re_original))
    summary = dict(N=use[0]['N'], seed=use[0]['seed'], height=label,
        boxes=len(use), pairIncidences=sum(b['T'].size for b in use),
        signedAtBase=pair.encode(complex(joined[zero])),
        positiveCoefficientSignedAtBase=pair.encode(complex(positive[zero])),
        negativeCoefficientSignedAtBase=pair.encode(complex(negative[zero])),
        integratedBandCoherence=coherence(positive, negative),
        fractionOfGridWithOpposingBandCrossTerm=float(np.mean(cross < 0)),
        cancellationRatioQuantiles=np.quantile(cancellation, [.05, .5, .95]).tolist(),
        bestCancellationOffset=float(delta[int(np.argmax(cancellation))]),
        worstReinforcementOffset=float(delta[int(np.argmax(cross))]),
        maximumSampledReal=float(re_original[kmax]), maximumRealOffset=float(delta[kmax]),
        sampledFrequencyMaximumNotUniformHeightBound=True,
        rawRadialCarrierMayAliasOnOffsetGrid=True,
        bandCoherenceUsesOnlyCommonDemodulatedEnvelope=True,
        leadingCouplingAtBase=pair.encode(complex(leading[zero])),
        joinedRemainingModesAtBase=pair.encode(complex(joined[zero]-leading[zero])),
        finiteRankOneRemainderL1Budget=sum(r['rankOneRemainderL1'] for r in blocks),
        maximumEvaluatedRemainingModes=float(np.abs(joined-leading).max()),
        directShiftedHeightAtomReplayMaxError=shifted_replay_error,
        offsetPhaseBinary64LogAndTrigRoundingNotIncludedInArbRadius=True,
        blocks=blocks, noPopulationScaleEstimated=True, cofinalFloorCredit=0)
    curves = dict(offsets=delta.tolist(), positiveReal=positive.real.tolist(),
        positiveImag=positive.imag.tolist(), negativeReal=negative.real.tolist(),
        negativeImag=negative.imag.tolist(), joinedReal=re_original.tolist(),
        joinedEnvelopeReal=joined.real.tolist(), joinedEnvelopeImag=joined.imag.tolist(),
        leadingEnvelopeReal=leading.real.tolist(), leadingEnvelopeImag=leading.imag.tolist(),
        joinedModulus=np.abs(joined).tolist(), cancellationRatio=cancellation.tolist())
    if permutations:
        summary['bandCoherenceReference'] = coherence_reference(
            marginals, delta, positive, negative, permutations)
    return summary, curves, marginals


def quantile_edges(positive, negative, weights):
    """Matched common mass plus explicit unequal-mass remainder.

    The distributions are NOT silently normalized to erase the remainder.
    Each keeps its original sampled mass; only common mass is coupled.
    """
    P, Q = float(weights[positive].sum()), float(-weights[negative].sum())
    if not P or not Q:
        return [], np.ones(len(weights)), P, Q
    common = min(P, Q)
    wp, wn = weights[positive]*common/P, -weights[negative]*common/Q
    fractions = np.ones(len(weights))
    fractions[positive] -= common/P
    fractions[negative] -= common/Q
    i = j = 0
    a, b = wp[0], wn[0]
    edges = []
    while i < len(positive) and j < len(negative):
        mass = min(a, b)
        edges.append((int(positive[i]), int(negative[j]), float(mass)))
        a -= mass
        b -= mass
        if a <= 1e-15:
            i += 1
            if i < len(positive):
                a = wp[i]
        if b <= 1e-15:
            j += 1
            if j < len(negative):
                b = wn[j]
    assert abs(sum(e[2] for e in edges)-common) < 2e-11
    return edges, fractions, P, Q


def transport(marginals, label):
    products = np.concatenate([b['products'].ravel() for b, *_ in marginals])
    weights = np.concatenate([w.ravel() for _, w, *_ in marginals])
    phase = np.concatenate([(pl[:, None]*qr[None, :]).ravel() for _, _, pl, qr in marginals])
    order = sorted(range(len(products)), key=lambda i: products[i])
    pos = np.array([i for i in order if weights[i] > 0], dtype=int)
    neg = np.array([i for i in order if weights[i] < 0], dtype=int)
    edges, fractions, P, Q = quantile_edges(pos, neg, weights)
    matched = sum(m*(phase[i]-phase[j]) for i, j, m in edges)
    unmatched = np.sum(weights*fractions*phase)
    whole = np.sum(weights*phase)
    assert abs(matched+unmatched-whole) < 2e-11
    y = correlations.parse_height(label)
    ctx.prec = max(1200, y.bit_length()+1024,
                   math.ceil(2*marginals[0][0]['N']/math.log(2))+256)
    cost = 0.
    shared = 0.
    log_gaps = []
    for i, j, m in edges:
        a, b = int(products[i]), int(products[j])
        small, large = min(a, b), max(a, b)
        gap = (arb(large-small)/small).log1p()
        assert gap > 0
        log_gaps.append(float(gap.mid()))
        cap = y*gap
        upper = 2. if cap >= 2 else math.nextafter(float(cap.upper()), math.inf)
        cost += m*upper
        if math.gcd(a, b) > 1:
            shared += m
    circular = []
    angles = np.angle(phase)
    for cut in np.linspace(-math.pi, math.pi, 16, endpoint=False):
        circular_order = np.argsort(np.mod(angles-cut, 2*math.pi))
        cp = np.array([i for i in circular_order if weights[i] > 0], dtype=int)
        cn = np.array([i for i in circular_order if weights[i] < 0], dtype=int)
        es, fs, _, _ = quantile_edges(cp, cn, weights)
        charge = sum(m*(phase[i]-phase[j]) for i, j, m in es)
        rest = np.sum(weights*fs*phase)
        assert abs(charge+rest-whole) < 2e-11
        circular.append(dict(cut=float(cut), observedChordCost=float(sum(
            m*abs(phase[i]-phase[j]) for i, j, m in es)),
            signedMatched=pair.encode(complex(charge))))
    best = min(circular, key=lambda a: a['observedChordCost'])
    common = min(P, Q)
    return dict(N=marginals[0][0]['N'], seed=marginals[0][0]['seed'], height=label,
        positiveSampledMass=P, negativeSampledMass=Q,
        matchedMass=common, unmatchedAbsoluteMass=abs(P-Q),
        sortedLogMatchingEdges=len(edges), signedMatched=pair.encode(complex(matched)),
        signedUnmatched=pair.encode(complex(unmatched)),
        reconstructionError=abs(matched+unmatched-whole),
        geometricPhaseDifferenceCost=cost, maximumTrivialMatchingCost=2*common,
        logGapQuantiles=np.quantile(log_gaps, [.05, .5, .95]).tolist() if log_gaps else [],
        matchingMassSharingActualPrime=shared,
        phaseCircleMatching=best, phaseCircleMatchingIsOutcomeDependent=True,
        productSortingUsesExactIntegers=True, logGapUsesBallRatioLog=True,
        samplingConventionsNotGlobalArithmeticMeasure=True, cofinalFloorCredit=0)


def boundary(box, label):
    y = correlations.parse_height(label)
    ctx.prec = max(1200, y.bit_length()+1024,
                   math.ceil(2*box['N']/math.log(2))+256)
    keep = exact_period_mask(box, arb(y))
    pl, erp = correlations.integer_height_phase(box['p'], y)
    qr, erq = correlations.integer_height_phase(box['q'], y)
    phase = pl[:, None]*qr[None, :]
    w = np.where(keep, box['weights'], 0.)
    denominator = float(np.abs(w).sum())
    if denominator:
        w /= denominator
    c = box['coefficient']
    v = c['share']
    M, K = box['N']+1, 13*box['N']//32
    F = binom.cdf(K, M, v)
    derivative = -M*binom.pmf(K, M-1, v)
    error = ((c['joined']-box['prefixDefectCoefficient']+c['selberg'])/box['N'])[keep]
    return dict(box=box['id'], kind=box['kind'], N=box['N'], seed=box['seed'], height=label,
        sampledPairIncidences=int(keep.size), retainedCompletePeriodLabels=int(keep.sum()),
        outsideOriginalRadialFlag=int((~c['central']).sum()),
        centralButPartialPeriod=int((c['central'] & ~keep).sum()),
        originalOwnerRegimeCounts={str(k): int((c['regime']==k).sum()) for k in np.unique(c['regime'])},
        meanShareRange=[float(v.min()), float(v.max())],
        factorialTransition=K/M, labelsEachSideOfTransition=[int((v < K/M).sum()), int((v >= K/M).sum())],
        exactPrefixRange=[float(F.min()), float(F.max())],
        prefixDerivativeRange=[float(derivative.min()), float(derivative.max())],
        joinedMaskErrorCoefficientOverNRange=[float(error.min()), float(error.max())] if error.size else [],
        retainedSigned=pair.encode(complex(np.sum(w*phase))),
        phaseBallRadiusUpper=max(erp, erq), floatingPeriodIndexUsed=False,
        boundaryMaskCompleted=False, formalLargeOrderThresholdMet=False, cofinalFloorCredit=0)


def phase_calibration(boxes, labels):
    max_prime = max(p for b in boxes for side in ('p', 'q') for p in b[side])
    max_label = max(int(n) for b in boxes for n in b['products'].ravel())
    ctx.prec = 256
    result = []
    for label in labels:
        y = correlations.parse_height(label)
        # log(1+1/n)>=1/(n+1): a conservative unit-integer phase step.
        prime_lower = arb(y).log()-arb(max_prime+1).log()-(2*arb.pi()).log()
        label_lower = arb(y).log()-arb(max_label+1).log()-(2*arb.pi()).log()
        result.append(dict(height=label,
            logMinimumPrimeIntegerStepTurnsLower=float(prime_lower.lower()),
            logMinimumProductIntegerStepTurnsLower=float(label_lower.lower()),
            everyPrimeIntegerNeighbourCrossesFullPhasePeriod=bool(prime_lower > 0),
            everyProductIntegerNeighbourCrossesFullPhasePeriod=bool(label_lower > 0),
            finiteOrdersNotAssumedAsymptoticForThisHeight=True))
    return result


def render(result, path):
    """Standalone numerical viewer; no README, Pages or CI integration."""
    payload = json.dumps(result, allow_nan=False).replace('</', '<\\/')
    html = '''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Joined signed pair discovery</title><style>
*{box-sizing:border-box}body{font:15px system-ui;background:#101925;color:#eaf0f8;max-width:1200px;margin:24px auto;padding:0 16px}
a{color:#9bcafa}h1{font-size:1.7rem}.scope{border:1px solid #91a5bf;padding:14px;border-radius:8px}
select,button{font:inherit;padding:7px;margin:4px;background:#26354a;color:inherit;border:1px solid #768aa4;border-radius:4px}
nav{display:flex;flex-wrap:wrap}button.active{border-color:#ffb68e}canvas{width:100%;height:auto;background:#162334;border-radius:8px}
pre{white-space:pre-wrap;overflow-wrap:anywhere;max-width:100%}.table{overflow-x:auto}table{border-collapse:collapse;width:100%;font-size:13px}
td,th{border-bottom:1px solid #42516a;padding:7px;text-align:left}#tip{min-height:35px;color:#bdcede}
</style><h1>Joined signed pair discovery</h1>
<p class="scope"><b>Finite actual-prime samples. No proved floor.</b> Exact moving length and factorial prefixes; full complex phase.
Equal sampled L1 mass per box is a discovery convention, not a global carrier estimate. None of these charts is in units of the 0.0798 floor target.</p>
<nav id="tabs"></nav><p><label>Height <select id="height"></select></label>
<label>Order <select id="order"></select></label><label>Seed <select id="seed"></select></label></p>
<p id="explanation"></p><canvas id="plot" width="1080" height="400"></canvas><p id="tip">Hover over the profile to inspect a sampled frequency offset.</p>
<div class="table" id="table"></div><pre id="details"></pre><script>
const R=PAYLOAD,H=document.querySelector('#height'),O=document.querySelector('#order'),S=document.querySelector('#seed'),C=document.querySelector('#plot'),X=C.getContext('2d');
const tabs=['Signed bands','Coupled moments','Order stability','Nearby products','Transition boundaries'];let current=0,selected=null;
document.querySelector('#tabs').innerHTML=tabs.map((t,i)=>`<button data-tab="${i}">${t}</button>`).join('');
document.querySelectorAll('[data-tab]').forEach(b=>b.onclick=()=>{current=+b.dataset.tab;draw()});
function opts(el,values){el.innerHTML=values.map(v=>`<option>${v}</option>`).join('')}
opts(H,R.coverage.heights);opts(O,[256,640]);opts(S,[731,732]);H.onchange=O.onchange=S.onchange=draw;
function fmt(v){return v===null?'—':typeof v==='number'?v.toPrecision(5):String(v)}
function rows(data,fields){document.querySelector('#table').innerHTML='<table><thead><tr>'+fields.map(f=>`<th>${f[0]}</th>`).join('')+'</tr></thead><tbody>'+data.map(d=>'<tr>'+fields.map(f=>`<td>${fmt(f[1](d))}</td>`).join('')+'</tr>').join('')+'</tbody></table>'}
function plot(data,lines){X.clearRect(0,0,C.width,C.height);let limit=Math.max(1e-12,...lines.flatMap(l=>l.values.map(Math.abs))),left=58,right=1050,mid=205,scale=145/limit;
X.strokeStyle='#758aa5';X.beginPath();X.moveTo(left,mid);X.lineTo(right,mid);X.stroke();X.fillStyle='#bdcede';X.fillText(fmt(-limit),8,mid+148);X.fillText(fmt(limit),8,mid-148);
lines.forEach((line,j)=>{X.strokeStyle=line.colour;X.beginPath();line.values.forEach((v,i)=>{let x=left+(right-left)*i/(line.values.length-1),y=mid-v*scale;i?X.lineTo(x,y):X.moveTo(x,y)});X.stroke();X.fillStyle=line.colour;X.fillText(line.name,65+j*290,25)});
X.fillStyle='#bdcede';X.fillText('offset '+data.offsets[0],left,380);X.fillText('offset '+data.offsets.at(-1),right-95,380);selected=data}
function draw(){document.querySelectorAll('[data-tab]').forEach(b=>b.classList.toggle('active',+b.dataset.tab===current));selected=null;C.style.display=current<2?'block':'none';
let profile=R.signedBandProfiles.find(r=>r.N==O.value&&r.seed==S.value&&r.height==H.value),data=R.curves[`${O.value}-${S.value}-${H.value}`];
document.querySelector('#table').innerHTML='';document.querySelector('#details').textContent='';
if(current===0){document.querySelector('#explanation').textContent='Complex band sums joined before estimating. The plot removes the same known radial rotation from all three curves; it preserves their relative phase and cancellation. Sampled maxima are not uniform-height bounds.';
plot(data,[{name:'Positive coefficient band (real)',values:data.positiveReal,colour:'#ffac84'},{name:'Negative coefficient band (real)',values:data.negativeReal,colour:'#7cbef2'},{name:'Joined envelope (real)',values:data.joinedEnvelopeReal,colour:'#b4df91'}]);
document.querySelector('#details').textContent=JSON.stringify({coherence:profile.integratedBandCoherence,reference:profile.bandCoherenceReference,cancellationQuantiles:profile.cancellationRatioQuantiles,calibration:R.orderHeightCalibration.find(r=>r.height==H.value)},null,2)}
else if(current===1){document.querySelector('#explanation').textContent='Finite weighted prime marginals are multiplied with their complex correlation retained. Every SVD mode remains in the exact reconstruction. A small sample remainder is not a global prime-phase bound.';
plot(data,[{name:'Leading coupled moment (real)',values:data.leadingEnvelopeReal,colour:'#ffac84'},{name:'All remaining modes (real)',values:data.joinedEnvelopeReal.map((v,i)=>v-data.leadingEnvelopeReal[i]),colour:'#7cbef2'},{name:'Exact joined envelope (real)',values:data.joinedEnvelopeReal,colour:'#b4df91'}]);
rows(profile.blocks,[['Box',r=>r.box],['Leading squared energy',r=>r.rankOneSquaredEnergyFraction],['Sampled L1 remainder',r=>r.rankOneRemainderL1],['Largest evaluated signed remainder',r=>r.maximumEvaluatedSignedRemainder]])}
else if(current===2){document.querySelector('#explanation').textContent='Same fixed height across native orders 256, 640 and 1536. Two seeds and differing sample sizes remain visible. Three finite orders do not establish cofinal decay.';
rows(R.orderStability.filter(r=>r.height==H.value),[['Order',r=>r.N],['Seed',r=>r.seed],['Sample family',r=>r.kind],['Smaller log share',r=>r.meanShare],['Signed real',r=>r.signedAtBase.re],['Signed imaginary',r=>r.signedAtBase.im],['Sample L1 remainder',r=>r.finiteRankOneRemainderL1Budget]])}
else if(current===3){document.querySelector('#explanation').textContent='Exact product sorting with the unequal-mass remainder retained. Phase-circle matching uses the observed outcome and is not an independent arithmetic transport theorem.';
rows(R.nearbyProductMatching.filter(r=>r.height==H.value),[['Order',r=>r.N],['Seed',r=>r.seed],['Common mass',r=>r.matchedMass],['Unmatched mass',r=>r.unmatchedAbsoluteMass],['Geometric phase cost',r=>r.geometricPhaseDifferenceCost],['Trivial cap',r=>r.maximumTrivialMatchingCost],['Observed circular chord cost',r=>r.phaseCircleMatching.observedChordCost]])}
else{document.querySelector('#explanation').textContent='Targeted factorial, owner and radial boundaries. Literal complete-period membership is evaluated with full-precision ball arithmetic; filtered labels are not silently filled.';
rows(R.exactTransitionBoundaries.filter(r=>r.height==H.value),[['Boundary',r=>r.kind],['Seed',r=>r.seed],['Sample pairs',r=>r.sampledPairIncidences],['Retained complete-period labels',r=>r.retainedCompletePeriodLabels],['Outside original radial flag',r=>r.outsideOriginalRadialFlag],['Partial periods',r=>r.centralButPartialPeriod],['Signed real',r=>r.retainedSigned.re]])}
document.querySelector('#tip').textContent='Scope: optional discovery, zero cofinal floor credit.'}
C.onmousemove=e=>{if(!selected)return;let rect=C.getBoundingClientRect(),x=(e.clientX-rect.left)*C.width/rect.width,k=Math.max(0,Math.min(selected.offsets.length-1,Math.round((x-58)/992*(selected.offsets.length-1))));document.querySelector('#tip').textContent=`offset ${selected.offsets[k]} | joined envelope ${fmt(selected.joinedEnvelopeReal[k])} + i ${fmt(selected.joinedEnvelopeImag[k])} | cancellation ratio ${fmt(selected.cancellationRatio[k])}`};draw();
</script></html>'''
    path.write_text(html.replace('PAYLOAD', payload))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--old', type=Path, default=Path('.lake/riesz-pair-structure/scan.primes.json'))
    ap.add_argument('--new', type=Path, default=Path('.lake/riesz-pair-joint/new-primes.json'))
    ap.add_argument('--balanced', type=Path, default=Path('.lake/riesz-balanced-prime-sampling/result.primes.json'))
    ap.add_argument('--output', type=Path, default=Path('.lake/riesz-pair-joint/scan.json'))
    ap.add_argument('--span', type=int, default=16)
    ap.add_argument('--steps-per-unit', type=int, default=64)
    ap.add_argument('--permutations', type=int, default=255)
    args = ap.parse_args()
    assert args.span > 0 and args.span <= 32 and args.steps_per_unit >= 16
    assert args.steps_per_unit & (args.steps_per_unit-1) == 0
    assert args.permutations >= 63
    boxes = prepare(args.old, args.new, args.balanced)
    delta = np.arange(-args.span*args.steps_per_unit, args.span*args.steps_per_unit+1)/args.steps_per_unit
    grouped = defaultdict(list)
    for b in boxes:
        if b['kind'] == 'bulk':
            grouped[(b['N'], b['seed'])].append(b)
    profiles, matching, curves, boundaries, order_cases = [], [], {}, [], []
    for label in HEIGHTS:
        for key, use in sorted(grouped.items()):
            print(json.dumps(dict(stage='joined phase profile', height=label, N=key[0], seed=key[1])), flush=True)
            summary, data, marginals = profile(use, label, delta, args.permutations)
            profiles.append(summary)
            curves[f'{key[0]}-{key[1]}-{label}'] = data
            matching.append(transport(marginals, label))
        for b in boxes:
            if b['kind'] not in ('bulk', 'native_order', 'dense_balanced'):
                boundaries.append(boundary(b, label))
            elif b['kind'] in ('native_order', 'dense_balanced') or (
                    b['kind']=='bulk' and b['meanShare'] > .49):
                summary, _, _ = profile([b], label, np.array([0.]))
                summary.update(kind=b['kind'], box=b['id'], meanShare=b['meanShare'])
                order_cases.append(summary)
    replications = []
    family_size = len({r['N'] for r in profiles})*len(HEIGHTS)
    for N in sorted({r['N'] for r in profiles}):
        for label in HEIGHTS:
            r = [a for a in profiles if a['N']==N and a['height']==label]
            replications.append(dict(N=N, height=label,
                bandCoherenceBySeed={str(a['seed']): a['integratedBandCoherence'] for a in r},
                bothSeedsOpposingOnAverage=all(a['integratedBandCoherence'] < 0 for a in r),
                maximumSeedReferenceRank=max(a['bandCoherenceReference']['negativeCoherenceReferenceRank'] for a in r),
                familyAdjustedReplicationDiagnostic=min(1., family_size*max(
                    a['bandCoherenceReference']['negativeCoherenceReferenceRank'] for a in r)),
                familySize=family_size, diagnosticNotPopulationPValue=True))
    result = dict(classification='Five joined actual-prime discovery scans; no independent floor',
        sources=[prefix.digest(p) for p in ('scripts/probe_riesz_pair_joint.py',
            'scripts/sample_riesz_pair_joint.py','scripts/probe_riesz_pair_correlations.py',
            'scripts/probe_riesz_pair_prefix.py','scripts/probe_riesz_pair_structure.py',
            'RiemannGaussian/ZetaRieszPairPrefixPayment.lean', args.old, args.new, args.balanced)],
        coverage=dict(actualDistinctPrimes=len({p for b in boxes for side in ('p','q') for p in b[side]}),
            actualSampledPairIncidences=sum(b['T'].size for b in boxes),
            broadBandSampledPairIncidences=sum(b['T'].size for b in boxes if b['kind']=='bulk'),
            orders=sorted({b['N'] for b in boxes}), boxes=len(boxes), heights=HEIGHTS,
            phaseOffsets=len(delta), phaseOffsetRange=[-args.span,args.span],
            dyadicPhaseOffsetStep=f'1/{args.steps_per_unit}',
            factorialKernelAndMovingLengthRetained=True, polynomialSmallCofactorsSkipped=True,
            noPrimeDensityApproximation=True, noPopulationCompletion=True),
        conventions=dict(equalBoxSampledL1Normalization=True, sharedPrimePairsNotIndependent=True,
            frequencyProfilesAreFiniteNotUniformHeightBounds=True,
            periodMaskCertifiedInBallArithmeticAtBoundaries=True,
            phaseOffsetsAppliedBeforeJoiningWithExactIdentity=True,
            phaseCircleMatchingOutcomeDependent=True,
            rawRadialCarrierGridNotAUniformFrequencyExtremum=True,
            formalLargeOrderThresholdNotReached=True),
        heightCoverage=correlations.height_coverage(HEIGHTS),
        orderHeightCalibration=phase_calibration(boxes, HEIGHTS),
        signedBandProfiles=profiles, primeMomentCouplings=profiles,
        orderStability=order_cases, nearbyProductMatching=matching,
        exactTransitionBoundaries=boundaries, seedSignComparisons=replications,
        curves=curves, independentSignedMainBound=False, floor=False, zeroExclusion=False,
        cofinalFloorCredit=0, RH=False)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    render(result, args.output.with_suffix('.html'))
    print(json.dumps(dict(output=str(args.output), profiles=len(profiles), boundaries=len(boundaries),
        orders=result['coverage']['orders'], allFiveScansExecuted=True, floor=False)))


if __name__ == '__main__':
    main()
