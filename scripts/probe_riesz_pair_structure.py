#!/usr/bin/env python3
"""Unpaid signed-pair structure detector using actual primes.

The older detector scans many-prime subset hinges. This adapter evaluates the
CURRENT literalPairDefect, retaining zero joined coefficients, the damped
length, both owner corrections, the exact factorial allocation and phase.
Small-order scans enumerate every distinct pair in the complete-period
support. Larger-order scans use disjoint boxes of proven-prime rejection
samples. Their Cartesian products are NOT independent observations.

Discovery/validation heights and seeds are separate. Phase permutations are
null diagnostics, never replacement carriers. No PNT density, selected-zero
model, cofinal estimate or saving against 399/5000 is inferred. Optional;
nothing here is imported by Lean or run by ordinary CI.
"""

import argparse
from collections import defaultdict
from functools import lru_cache
import hashlib
import json
import math
from pathlib import Path
import sys

sys.dont_write_bytecode = True
import numpy as np
from scipy.stats import binom
from flint import arb, ctx, fmpz

from probe_riesz_balanced_prime_sampling import (
    sample_primes, stopped_count, phase,
)
from probe_riesz_fixed_count_period import unpaid_orders


U_NUM, U_DEN = 10001, 20000
U = U_NUM / U_DEN
SHARES = (.20, .255, .30, .36, .40, .43, .475, .495)
SOURCE_PATHS = [
    'scripts/probe_riesz_pair_structure.py',
    'scripts/probe_riesz_fixed_count_period.py',
    'scripts/probe_riesz_balanced_prime_sampling.py',
    'RiemannGaussian/ZetaRieszLowCountSignedBoundary.lean',
    'RiemannGaussian/ZetaRieszLowCountSelbergAudit.lean',
    'RiemannGaussian/ZetaRieszSignedSelbergPayment.lean',
    'RiemannGaussian/ZetaRieszPolynomialPairPayment.lean',
]


def encode(value):
    return {'re': float(value.real), 'im': float(value.imag)}


def exp_floor(value):
    integer = value.exp().floor().unique_fmpz()
    if integer is None:
        raise ArithmeticError('Unresolved exponential endpoint')
    return int(integer)


@lru_cache(maxsize=None)
def parameters(N):
    D = U_DEN**N // ((N+1)*U_NUM**N)
    physical = (D+2)**2
    return dict(N=N, D=D, physical=physical,
        L=float(arb(physical).log().mid()),
        centralLow=exp_floor(arb(1971)*N/1000),
        centralHigh=exp_floor(arb(2029)*N/1000),
        ownerLow=exp_floor(arb(51)*N/50)+1,
        ownerHigh=exp_floor(arb(5)*N/4))


def allocation(N, share):
    orders = unpaid_orders(N)
    if not len(orders):
        return np.zeros_like(share)
    if np.all(np.diff(orders) == 1):
        mass = binom.cdf(int(orders[-1]), N+1, share)
        mass -= binom.cdf(int(orders[0])-1, N+1, share)
    else:
        mass = sum(binom.pmf(int(k), N+1, share) for k in orders)
    if np.any(mass < -2e-14) or np.any(mass > 1+2e-14):
        raise ArithmeticError('Factorial allocation outside [0,1]')
    return np.clip(mass, 0., 1.)


def coefficient(N, p, q, x, z):
    """Literal coefficient for central distinct ordinary-prime pairs.

    Callers check primality and distinctness. Integer comparisons retain the
    physical, sieve and support cutoffs. x,z are numerical logs, NOT new log
    geometries. On the contracted window the incidence interval is automatic.
    """
    par = parameters(N)
    p, q = np.broadcast_arrays(p, q)
    x, z = np.broadcast_arrays(x, z)
    swap = p < q
    larger, smaller = np.where(swap, q, p), np.where(swap, p, q)
    lp, lq = np.where(swap, z, x), np.where(swap, x, z)
    T = lp+lq
    label = p*q
    central = (par['centralLow'] < label) & (label <= par['centralHigh']) & (p != q)
    L = par['L']
    R = L-np.maximum(L-lp, 0)-np.maximum(L-lq, 0)+np.maximum(L-T, 0)
    original = -T*R/L
    correction_mask = (par['ownerLow'] <= larger) & (larger <= par['physical'])
    head_mask = ((par['ownerLow'] <= larger) & (larger <= par['ownerHigh']) &
                 (N*N < larger) & (larger < par['physical']) & (N**3 < smaller))
    correction = np.where(correction_mask, T*(L-lp)/L, 0.)
    allocated = allocation(N, lq/T)
    head = np.where(head_mask, T*(L-lp)/L*(1-allocated), 0.)
    joined = original+head-correction
    selberg = -2*lp*lq/T
    defect = joined-selberg
    regime = correction_mask.astype(int)+2*head_mask.astype(int)
    return dict(T=T, share=lq/T, joined=joined, selberg=selberg, defect=defect,
                allocated=allocated, regime=regime, central=central,
                smaller=smaller, larger=larger)


def complete_periods(N, T, y):
    width = 2*math.pi/abs(y)
    index = np.floor(T/width).astype(np.int64)
    left = index*width
    return index, (1.971*N <= left) & (left+width <= 2.029*N)


def grouped(data, y, phase_values=None):
    """Join the signed coefficients BEFORE computing one-sided diagnostics."""
    T, N = data['T'], data['N']
    index, keep = complete_periods(N, T, y)
    keep &= data.get('central', np.ones(T.shape, dtype=bool))
    phase_values = np.exp(-1j*y*T) if phase_values is None else phase_values
    values = data['amplitude']*phase_values
    values = values[keep]
    periods, ip = np.unique(index[keep], return_inverse=True)
    bins = np.minimum(31, (64*data['share'][keep]).astype(int))
    matrix = np.zeros((len(periods), 32), dtype=complex)
    np.add.at(matrix, (ip, bins), values)
    period_values = matrix.sum(axis=1)
    share_values = matrix.sum(axis=0)
    total = values.sum()
    assert abs(matrix.sum()-total) < 1e-11*max(1., float(np.abs(values).sum()))
    coefficient_positive = data['defect'][keep] > 0
    positive = values[coefficient_positive].sum()
    negative = values[~coefficient_positive].sum()
    gross = float(np.abs(values).sum())
    atom_price = float(np.maximum(values.real, 0).sum())
    period_price = float(np.maximum(period_values.real, 0).sum())
    share_price = float(np.maximum(share_values.real, 0).sum())
    total_price = max(float(total.real), 0.)
    assert min(atom_price-period_price, atom_price-share_price,
               period_price-total_price, share_price-total_price) > -1e-10*max(1., gross)
    sign_matrix = np.zeros((len(periods), 2), dtype=complex)
    np.add.at(sign_matrix, (ip, coefficient_positive.astype(int)), values)
    sign_price = float(np.maximum(sign_matrix.real, 0).sum())
    valid_bins = np.flatnonzero(np.any(matrix != 0, axis=0))
    pairs = []
    for a_pos, a in enumerate(valid_bins):
        for b in valid_bins[a_pos+1:]:
            xa, xb = matrix[:, a].real, matrix[:, b].real
            separate = float(np.maximum(xa, 0).sum()+np.maximum(xb, 0).sum())
            saving = separate-float(np.maximum(xa+xb, 0).sum())
            if saving > 0:
                corr = (float(np.corrcoef(xa, xb)[0, 1])
                        if len(xa) >= 3 and np.std(xa) and np.std(xb) else None)
                pairs.append(dict(bins=[int(a), int(b)], finitePriceSaving=saving,
                                  fraction=saving/separate if separate else 0., correlation=corr))
    pairs.sort(key=lambda v: v['finitePriceSaving'], reverse=True)
    return dict(N=N, height=y, labels=int(keep.sum()), periods=len(periods),
        signed=encode(total), positiveCoefficientSigned=encode(positive),
        negativeCoefficientSigned=encode(negative), absoluteMass=gross,
        oneSidedPrices=dict(atom=atom_price, period=period_price, share=share_price,
                            coefficientSignThenPeriod=sign_price, wholeFiniteSum=total_price),
        jointSignPeriodSaving=sign_price-period_price,
        jointAcrossPeriodsSaving=period_price-total_price,
        shareBins=[encode(v) for v in share_values], topShareOppositions=pairs[:12],
        phaseSupportNumericallyEvaluated=True, cofinalSavingCertified=False,
        originalZeroJoinedLabelsRetained=int(np.count_nonzero(data['joined'][keep] == 0)))


def exhaustive(N):
    par = parameters(N)
    high = par['centralHigh']
    if high > 20_000_000:
        raise ValueError('Explicit cap: exhaustive contracted upper endpoint <=20 million')
    sieve = np.ones(high//2+1, dtype=bool)
    sieve[:2] = False
    for p in range(2, math.isqrt(len(sieve)-1)+1):
        if sieve[p]:
            sieve[p*p::p] = False
    primes = np.flatnonzero(sieve)
    chunks = defaultdict(list)
    for q in primes[:np.searchsorted(primes, math.isqrt(high), side='right')]:
        left = max(int(q)+1, par['centralLow']//int(q)+1)
        right = high//int(q)
        p = primes[np.searchsorted(primes, left):np.searchsorted(primes, right, side='right')]
        if not len(p):
            continue
        x, z = np.log(p.astype(float)), np.full(len(p), math.log(int(q)))
        c = coefficient(N, p, np.full(len(p), q), x, z)
        assert np.all(c['central'])
        for key in ('T', 'share', 'joined', 'defect', 'allocated', 'regime'):
            chunks[key].append(c[key])
    data = {key: np.concatenate(value) for key, value in chunks.items()}
    T = data['T']
    data.update(N=N, amplitude=data['defect']*np.exp((N+1)*math.log(U)-1.5*T+
                N*np.log(T)-math.lgamma(N+1)))
    return data


def direct_regressions():
    checks = 0
    # Independent integer-divisor response and literal finite factorial sum.
    for N in (3, 6, 8, 64, 256):
        par = parameters(N)
        for p, q in ((7, 3), (503, 223), (7919, 1009)):
            c = coefficient(N, np.array([p]), np.array([q]),
                            np.array([math.log(p)]), np.array([math.log(q)]))
            R = math.fsum(sign*max(par['L']-math.log(d), 0.)
                         for d, sign in ((1, 1), (p, -1), (q, -1), (p*q, 1)))
            T, x, z = math.log(p*q), math.log(p), math.log(q)
            alloc = math.fsum(math.comb(N+1, int(k))*(z/T)**int(k)*
                             (1-z/T)**(N+1-int(k)) for k in unpaid_orders(N))
            corr = T*(par['L']-x)/par['L'] if par['ownerLow'] <= p <= par['physical'] else 0.
            head = (T*(par['L']-x)/par['L']*(1-alloc)
                    if par['ownerLow'] <= p <= par['ownerHigh'] and N*N < p < par['physical']
                    and N**3 < q else 0.)
            joined = -T*R/par['L']+head-corr
            assert abs(joined-c['joined'][0]) < 1e-11
            assert abs(alloc-c['allocated'][0]) < 1e-12
            assert abs(c['defect'][0]-(joined+2*x*z/T)) < 1e-11
            checks += 1
    # A zero coefficient must not be a support filter for its defect.
    toy = dict(N=256, T=np.array([512., 512.01]), share=np.array([.45, .45]),
               joined=np.zeros(2), defect=np.ones(2), amplitude=np.ones(2))
    assert grouped(toy, 54)['labels'] == 2
    assert grouped(toy, 54)['originalZeroJoinedLabelsRetained'] == 2
    coverage = []
    # Independent factor-by-factor enumeration, not another product iterator.
    for N in (3, 4, 5):
        data, par = exhaustive(N), parameters(N)
        actual = set(np.rint(np.exp(data['T'])).astype(int).tolist())
        oracle = set()
        for n in range(par['centralLow']+1, par['centralHigh']+1):
            for q in range(2, math.isqrt(n)+1):
                if n % q == 0:
                    p = n//q
                    if p != q and all(q % a for a in range(2, math.isqrt(q)+1)) and \
                            all(p % a for a in range(2, math.isqrt(p)+1)):
                        oracle.add(n)
                    break
        assert actual == oracle
        coverage.append(dict(N=N, labels=len(actual), independentCoverageEquality=True))
    return dict(independentDivisorFactorialComparisons=checks,
                zeroJoinedNonzeroDefectGuard=True, exhaustiveCoverageOracles=coverage)


def sample_boxes(args, sample_path):
    if sample_path.exists():
        samples = json.loads(sample_path.read_text())
        if samples['orders'] != args.sample_orders or samples['seeds'] != args.seeds:
            raise ValueError('Sample cache has different orders/seeds')
        if samples['size'] != args.size or samples['shares'] != list(SHARES):
            raise ValueError('Sample cache has different size/share geometry')
    else:
        samples = dict(orders=args.sample_orders, seeds=args.seeds, size=args.size,
                       shares=list(SHARES), rows=[])
    existing = {(row['N'], row['seed'], row['box']) for row in samples['rows']}
    if len(existing) != len(samples['rows']):
        raise ValueError('Duplicate cached box records')
    for N in args.sample_orders:
        for seed in args.seeds:
            for box, share in enumerate(SHARES):
                if (N, seed, box) in existing:
                    continue
                lo_q = round(2*N*share)
                lo_p = 2*N-lo_q
                if lo_q <= 16*math.log(N) or lo_q+1 >= lo_p:
                    raise ValueError('Box must be above N^16 with strictly ordered primes')
                left = sample_primes(lo_p, args.size, seed+10000*N+1000*box)
                right = sample_primes(lo_q, args.size, seed+10000*N+1000*box+500)
                samples['rows'].append(dict(N=N, seed=seed, box=box, share=share,
                                            left=left, right=right))
                sample_path.write_text(json.dumps(samples, indent=2)+'\n')
    return samples


@lru_cache(maxsize=None)
def prepared_sample(N, pp, qq, reference):
    assert all(fmpz(p).is_prime() for p in pp+qq)
    assert all(q > N**16 for q in qq)
    lp, lq = [arb(p).log() for p in pp], [arb(q).log() for q in qq]
    x, z = np.array([float(v.mid()) for v in lp]), np.array([float(v.mid()) for v in lq])
    c = coefficient(N, np.array(pp, dtype=object)[:, None], np.array(qq, dtype=object)[None, :],
                    x[:, None], z[None, :])
    assert np.all(c['central'])
    T = c['T']
    weights = c['defect']/N*np.exp(N*np.log1p((T-reference)/reference)-1.5*(T-reference))
    return c, weights, lp, lq


def sample_arrays(row, y):
    N = row['N']
    pp = tuple(int(p) for p in row['left']['primes'])
    qq = tuple(int(q) for q in row['right']['primes'])
    reference = row['left']['logLower']+row['right']['logLower']+1
    c, weights, lp, lq = prepared_sample(N, pp, qq, reference)
    pl, er1 = phase(lp, arb(y))
    qr, er2 = phase(lq, arb(y))
    phases = pl[:, None]*qr[None, :]
    return c, weights, pl, qr, phases, max(er1, er2), reference


def sampled_case(row, y, permutations):
    N = row['N']
    c, weights, pl, qr, phases, phase_error, reference = sample_arrays(row, y)
    data = dict(N=N, **{key: c[key].reshape(-1) for key in ('T', 'share', 'joined', 'defect', 'central')},
                amplitude=weights.reshape(-1))
    g = grouped(data, y, phases.reshape(-1))
    denominator = float(np.abs(weights).sum())
    left, singular, right = np.linalg.svd(weights, full_matrices=False)
    rank1_energy = float(singular[0]**2/np.sum(singular**2)) if np.sum(singular**2) else 0.
    mode_values = singular*(left.T@pl)*(right@qr)/denominator
    assert abs(mode_values.sum()-np.sum(weights*phases)/denominator) < 1e-12
    rank_one = singular[0]*left[:, 0, None]*right[None, 0, :]
    rng = np.random.default_rng(row['seed']+1000*row['box']+int(y))
    null = [float(np.real(np.sum(weights*pl[rng.permutation(len(pl)), None]*
                                 qr[None, rng.permutation(len(qr))]))/denominator)
            for _ in range(permutations)]
    observed = float(np.real(np.sum(weights*phases))/denominator)
    quantile = (1+sum(abs(value) >= abs(observed) for value in null))/(len(null)+1)
    # Independent prime MARGINALS are resampled; never resample Cartesian pairs.
    boot = []
    for _ in range(255):
        i = rng.integers(0, len(pl), len(pl))
        j = rng.integers(0, len(qr), len(qr))
        ix = np.ix_(i, j)
        boot.append(float(np.real(np.sum((weights*phases)[ix]))/np.abs(weights[ix]).sum()))
    counts = [stopped_count(row[side]) for side in ('left', 'right')]
    log_scale = ((N+1)*math.log(U)+math.log(N)-1.5*reference+N*math.log(reference)-
                 math.lgamma(N+1)+sum(v['logPrimeCountEstimate'] for v in counts))
    population = (math.exp(log_scale)*np.mean(weights*phases)
                  if -700 < log_scale < 700 else None)
    return dict(N=N, seed=row['seed'], box=row['box'], targetShare=row['share'], height=y,
        actualLogBoxes=[row[side]['logLower'] for side in ('left', 'right')],
        marginalSampleSizes=[len(pl), len(qr)], relativeSignedReal=observed,
        relativeSigned=encode(np.sum(weights*phases)/denominator),
        coefficientOverNRange=[float(c['defect'].min()/N), float(c['defect'].max()/N)],
        coefficientSigns=sorted(set(np.sign(c['defect']).reshape(-1).astype(int).tolist())),
        literalRegimes=sorted(set(c['regime'].reshape(-1).tolist())),
        allocationRange=[float(c['allocated'].min()), float(c['allocated'].max())],
        coefficientMatrixRankOneEnergy=rank1_energy,
        finiteSignedCompression=dict(leadingMode=encode(mode_values[0]),
            remainingModes=encode(mode_values[1:].sum()),
            leadingPrimeMarginalFactors=[encode(left[:, 0]@pl), encode(right[0]@qr)],
            rankOneWeightRemainderL1Ratio=float(np.abs(weights-rank_one).sum()/denominator),
            exactFiniteMaskKept=True, completePrimeLegLimitTransferred=False,
            evaluatedModes=len(mode_values), floatingReplayDifference=float(abs(mode_values.sum()-
                np.sum(weights*phases)/denominator))),
        phasePermutationNull=dict(twoSidedRank=quantile,
             range=[min(null), max(null)], permutationCount=permutations,
             preservesActualCarrier=False, samplesAreNotIndependentPairs=True),
        empiricalTwoMarginalBootstrap95=np.quantile(boot, [.025, .975]).tolist(),
        primePhaseMagnitudes=[float(abs(pl.mean())), float(abs(qr.mean()))],
        phaseArbRadiusUpper=phase_error, finiteSampleSignedGrouping=g,
        stoppedCountDiagnostics=counts,
        finiteBoxPopulationEstimate=encode(population) if population is not None else None,
        wholeCarrierEstimated=False, sourceScaleSavingCredited=0)


def sampled_joint(rows, y):
    """One SIGNED, period-aligned ledger on the union of disjoint sample boxes.

    Counts are estimated by stopped rejection sampling. This is a partial
    population diagnostic with empirical uncertainty, never a literal sum
    over the unsampled population or a bound for the entire carrier.
    """
    N, seed = rows[0]['N'], rows[0]['seed']
    pieces, phases, blocks = defaultdict(list), [], []
    boxes = []
    for row in rows:
        assert row['N'] == N and row['seed'] == seed
        c, weights, _, _, phase_values, _, reference = sample_arrays(row, y)
        box = (row['right']['logLower'], row['left']['logLower'])
        assert box not in boxes
        boxes.append(box)
        counts = [stopped_count(row[side]) for side in ('left', 'right')]
        log_scale = ((N+1)*math.log(U)+math.log(N)-1.5*reference+
            N*math.log(reference)-math.lgamma(N+1)+
            sum(v['logPrimeCountEstimate'] for v in counts))
        scaled = math.exp(log_scale)*weights
        for key in ('T', 'share', 'joined', 'defect', 'central'):
            pieces[key].append(c[key].reshape(-1))
        pieces['amplitude'].append((scaled/scaled.size).reshape(-1))
        phases.append(phase_values.reshape(-1))
        blocks.append((scaled*phase_values, counts))
    data = {key: np.concatenate(values) for key, values in pieces.items()}
    data['N'] = N
    result = grouped(data, y, np.concatenate(phases))
    rng = np.random.default_rng(seed+int(y))
    boot = []
    for _ in range(255):
        total = 0j
        for atoms, counts in blocks:
            i = rng.integers(0, atoms.shape[0], atoms.shape[0])
            j = rng.integers(0, atoms.shape[1], atoms.shape[1])
            ratio = 1.
            for count in counts:
                accepted = count['acceptedPrimeCount']
                trials = accepted+rng.negative_binomial(accepted,
                            count['stoppedSamplingSuccessRateEstimate'])
                ratio *= (count['totalOddTrials']-1)/(trials-1)
            total += ratio*np.mean(atoms[np.ix_(i, j)])
        boot.append(float(total.real))
    result.update(seed=seed, disjointLogBoxes=boxes,
        sourceScaledPartialPopulationEstimated=True,
        sourceScaledWholeCarrierEstimated=False, primeCountsCertified=False,
        empiricalTwoMarginalStoppedCountBootstrap95=np.quantile(boot, [.025, .975]).tolist(),
        noActualCarrierPhaseReplaced=True, noPopulationFloorCertified=True)
    return result


def render(report, path):
    # Self-contained interactive map; numerical coverage remains visible.
    payload = json.dumps(report, allow_nan=False).replace('</', '<\\/')
    html = '''<!doctype html><html><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Retained signed prime-pair detector</title><style>body{font:16px system-ui;max-width:1100px;margin:30px auto;padding:0 20px;background:#101721;color:#e8edf3}button,select{padding:8px;margin:5px}canvas{width:100%;height:auto}pre{white-space:pre-wrap;overflow-wrap:anywhere}a{color:#86c8ff}.scope{border:1px solid #8799ac;padding:15px}#tip{min-height:70px}</style>
<h1>Retained signed prime-pair detector</h1><p class="scope">Actual primes. Exact integer support and original coefficients; floating weights. Small orders are exhaustively enumerated. Larger orders are sampled disjoint boxes, NOT whole-carrier estimates. No cofinal floor credit.</p>
<label>View <select id="view"><option value="joint">Joined sampled boxes</option><option value="sample">Sampled actual-prime boxes</option><option value="exact">Exhaustive small-order sums</option></select></label><label>Height <select id="height"></select></label><label>Order <select id="order"></select></label>
<canvas id="plot" width="1040" height="430"></canvas><p id="tip">Hover over a bar for its actual coefficient range and scope.</p><pre id="info"></pre>
<script>const R=PAYLOAD;const V=document.querySelector('#view'),H=document.querySelector('#height'),O=document.querySelector('#order'),C=document.querySelector('#plot'),X=C.getContext('2d');let bars=[];function options(el,vals){el.innerHTML=vals.map(v=>`<option>${v}</option>`).join('')}function reset(){let rs=V.value==='sample'?R.sampled:R.exhaustive;options(H,[...new Set(rs.map(r=>r.height))]);options(O,[...new Set(rs.map(r=>r.N))]);draw()}function draw(){let rs=(V.value==='sample'?R.sampled:R.exhaustive).filter(r=>r.height==H.value&&r.N==O.value);X.clearRect(0,0,C.width,C.height);bars=[];let vs=V.value==='sample'?rs.map(r=>r.relativeSignedReal):rs.flatMap(r=>r.shareBins.map(z=>z.re));let lim=Math.max(...vs.map(Math.abs),1e-12),w=900/Math.max(vs.length,1);X.strokeStyle='#798c9f';X.beginPath();X.moveTo(60,215);X.lineTo(1000,215);X.stroke();vs.forEach((v,i)=>{let h=170*Math.abs(v)/lim,x=65+i*w,y=v>=0?215-h:215;X.fillStyle=v>=0?'#ed9a79':'#66b5d7';X.fillRect(x,y,w*.8,h);bars.push({x,y,w:w*.8,h,record:V.value==='sample'?rs[i]:{bin:i%32,seed:rs[Math.floor(i/32)].seed??null,order:O.value,height:H.value,signedReal:v,coverage:V.value==='joint'?'Estimated partial packet':'Exhaustive early-order population'}})});document.querySelector('#info').textContent=JSON.stringify({summary:R.summary,selectedRows:rs.map(r=>V.value==='sample'?{seed:r.seed,share:r.targetShare,coefficientSigns:r.coefficientSigns,permutationRank:r.phasePermutationNull.twoSidedRank}: {signed:r.signed,labels:r.labels,oneSidedPrices:r.oneSidedPrices})},null,2)}C.onmousemove=e=>{let rect=C.getBoundingClientRect(),x=(e.clientX-rect.left)*C.width/rect.width,y=(e.clientY-rect.top)*C.height/rect.height;let b=bars.find(b=>x>=b.x&&x<=b.x+b.w&&y>=b.y&&y<=b.y+Math.max(b.h,4));document.querySelector('#tip').textContent=b?JSON.stringify(b.record,null,2):'Hover over a bar.'};V.onchange=reset;H.onchange=draw;O.onchange=draw;reset();</script></html>'''
    # Extend the older detector's interactive inspection to this literal pair
    # adapter, keeping population estimates distinct from exhaustive sums.
    html = html.replace("V.value==='sample'?R.sampled:R.exhaustive",
        "V.value==='sample'?R.sampled:(V.value==='joint'?R.sampledJoint:R.exhaustive)")
    html = html.replace("X.strokeStyle='#798c9f'", "X.fillStyle='#e8edf3';X.fillText(" +
        "V.value==='sample'?'Relative sampled signed values':(V.value==='joint'?" +
        "'Partial population estimates by share bin; both seeds shown':'Exhaustive small-order share sums')," +
        "60,25);X.strokeStyle='#798c9f'")
    path.write_text(html.replace('PAYLOAD', payload))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--self-test', action='store_true')
    parser.add_argument('--orders', type=int, nargs='*', default=[6, 7, 8])
    parser.add_argument('--sample-orders', type=int, nargs='*', default=[256])
    parser.add_argument('--size', type=int, default=24)
    parser.add_argument('--seeds', type=int, nargs='+', default=[731, 732])
    parser.add_argument('--heights', type=float, nargs='+', default=[54., 65., 100., 142.])
    parser.add_argument('--permutations', type=int, default=127)
    parser.add_argument('--output', type=Path, default=Path('.lake/riesz-pair-structure/scan.json'))
    args = parser.parse_args()
    if min(args.heights) < 54 or any(not math.isfinite(y) for y in args.heights):
        parser.error('Use finite diagnostic heights >=54')
    if args.size < 8 or args.permutations < 31:
        parser.error('At least 8 marginal primes and 31 permutations required')
    ctx.prec = max(1024, math.ceil((max(args.sample_orders, default=256)*2+100)/math.log(2))+256)
    regressions = direct_regressions()
    if args.self_test:
        print(json.dumps(regressions))
        return
    args.output.parent.mkdir(parents=True, exist_ok=True)
    report = dict(schemaVersion=2, regressions=regressions, exhaustive=[], sampled=[], sampledJoint=[],
        classification='Actual-prime numerical discovery; no arithmetic floor',
        sourceScaledWholeCarrierCertified=False, cofinalInference=False,
        sourceScaleSavingCredited=0, selectedZeroOrdinatesUsed=False,
        target='Re literalPairDefect <=399/5000+o(1)',
        discoveryHeights=args.heights[:2], validationHeights=args.heights[2:])
    for N in args.orders:
        data = exhaustive(N)
        print(json.dumps(dict(event='exhaustive', N=N, allCentralPairs=len(data['T']))), flush=True)
        for y in args.heights:
            g = grouped(data, y)
            g.update(exhaustiveCentralIntegerPairPopulation=True,
                     primalityByDeterministicSieve=True, preAsymptoticOrder=True,
                     nativeEventualPaymentsUsed=False, allOrdersBeforePolynomialSmallPayment=True)
            report['exhaustive'].append(g)
    sample_path = args.output.with_suffix('.primes.json')
    samples = sample_boxes(args, sample_path) if args.sample_orders else dict(rows=[])
    for row in samples['rows']:
        for y in args.heights:
            result = sampled_case(row, y, args.permutations)
            report['sampled'].append(result)
        print(json.dumps(dict(event='sampled', N=row['N'], seed=row['seed'], box=row['box'])), flush=True)
    for N in args.sample_orders:
        for seed in args.seeds:
            rows = [row for row in samples['rows'] if row['N'] == N and row['seed'] == seed]
            for y in args.heights:
                report['sampledJoint'].append(sampled_joint(rows, y))
    candidates = []
    for N in args.sample_orders:
        for box, share in enumerate(SHARES):
            rows = [r for r in report['sampled'] if r['N'] == N and r['box'] == box]
            interesting = [r for r in rows if r['phasePermutationNull']['twoSidedRank'] < .05]
            # Matching SHARE alone at two different heights is not replication.
            replicated = [y for y in args.heights if all(any(r['seed'] == seed and
                           r['height'] == y for r in interesting) for seed in args.seeds)]
            repeated = bool(replicated)
            validation = any(y in args.heights[2:] for y in replicated)
            candidates.append(dict(N=N, share=share,
                discoveryOrValidationExtremeRows=len(interesting),
                sameHeightSeedReplications=replicated,
                seenOnEverySeed=repeated, seenAtValidationHeight=validation,
                uncorrectedMultipleTesting=True, mechanismCertified=False))
    report['summary'] = dict(sampleBoxes=len(samples['rows']),
        sampledPhaseCases=len(report['sampled']), exhaustiveCases=len(report['exhaustive']),
        repeatedPhaseWeightCandidates=[r for r in candidates if r['seenOnEverySeed'] and r['seenAtValidationHeight']],
        coefficientRegimeCandidates=candidates, oneSidedFloorOpen=True,
        empiricalMarginalIntervalsContainingZero=sum(r['empiricalTwoMarginalBootstrap95'][0] <= 0 <=
            r['empiricalTwoMarginalBootstrap95'][1] for r in report['sampled']),
        empiricalJointPacketIntervalsContainingZero=sum(r['empiricalTwoMarginalStoppedCountBootstrap95'][0] <=
            0 <= r['empiricalTwoMarginalStoppedCountBootstrap95'][1] for r in report['sampledJoint']),
        permutationReferencesAreNotProbabilityCertificates=True,
        maximumRelativeSignedCompressionRemainder=max((abs(complex(
            r['finiteSignedCompression']['remainingModes']['re'],
            r['finiteSignedCompression']['remainingModes']['im']))
            for r in report['sampled']), default=0.),
        compressionRemainderLargerThanSignedValueCases=sum(abs(complex(
            r['finiteSignedCompression']['remainingModes']['re'],
            r['finiteSignedCompression']['remainingModes']['im'])) >= abs(complex(
            r['relativeSigned']['re'],r['relativeSigned']['im'])) for r in report['sampled']),
        experimentalScope='Finite discovery/validation only; repeated flags are not statistical certificates')
    report['sources'] = []
    for path in SOURCE_PATHS:
        data = Path(path).read_bytes()
        report['sources'].append(dict(path=path, sha256=hashlib.sha256(data).hexdigest()))
    if sample_path.exists():
        report['sampleFile'] = dict(path=str(sample_path), sha256=hashlib.sha256(sample_path.read_bytes()).hexdigest())
    args.output.write_text(json.dumps(report, indent=2, allow_nan=False)+'\n')
    render(report, args.output.with_suffix('.html'))
    print(json.dumps(report['summary'], indent=2), flush=True)


if __name__ == '__main__':
    main()
