#!/usr/bin/env python3
"""Optional weighted signed-cutoff investigation, never an RH certificate.

Two deliberately separate experiments:
* A log-simplex/ordinary-prime-density MODEL, with literal moving length,
  factorial probabilities, all marked incidences, and unmodified phase.
  There is NO arithmetic transport theorem and the omitted counts are unpaid.
* Certified prime products from randomized log targets. These are actual
  integers, but the Proth construction is NOT a population sample.

The target weight is lowerThreshold minus shortOverflow: counts <14 keep
both least-order endpoints, counts >=14 keep the lower endpoint. No two
independent allowances replace that signed difference.
"""
import argparse
import hashlib
import itertools
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np
from scipy.special import gammaln
from scipy.stats import binom, qmc

from probe_riesz_label_anatomy import check_certificate, length, proth_near_log
from probe_riesz_joint_masked import rectangle_values

U = 10001/20000
HEIGHTS = (0, 54, 60, 100)
PROFILE_SLOTS = np.linspace(0, 1, 17)


def shapes(N, count, power, seed):
    """Uniform simplex proposal, not a sample from the prime population."""
    points = qmc.Sobol(count, scramble=True, seed=seed).random_base2(power)
    T = N*(1.95+.08*points[:, 0])
    p = .5+.1*points[:, 1]
    lo = np.maximum(.005, 2*np.log(N)/T)
    hi = np.minimum(.06, (1-p)/(count-1))
    width = np.maximum(hi-lo, 0)
    r = lo+width*points[:, 2]
    m = count-2
    cuts = np.sort(points[:, 3:], axis=1)
    gaps = np.diff(np.column_stack((np.zeros(len(p)), cuts, np.ones(len(p)))), axis=1)
    free = np.maximum(1-p-(m+1)*r, 0)
    middle = r[:, None]+free[:, None]*gaps
    xs = np.column_stack((p, middle, r))
    # Jacobian and the unordered-middle symmetry factor are separate.
    volume = .08*N*.1*width*free**(m-1)/math.factorial(m-1)/math.factorial(m)
    return T, xs, volume


def marked_weights(N, xs, count):
    """Literal multinomial marginals, with every distinct marked prime."""
    j = np.arange((21*N+39)//40, 23*N//40+1)
    hlow, hhigh = max(0, (N+99)//100-1), N//25-1
    least = xs[:, -1, None]
    weight = np.zeros(len(xs))
    owner = None
    for index in range(xs.shape[1]-1):
        p = xs[:, index, None]
        remaining = N+1-j
        cond = least/(1-p)
        lower = binom.sf(hlow-1, remaining, cond)
        if count < 14:
            # Preserve lower-minus-overflow as one signed boundary weight.
            lower -= binom.sf(hhigh, remaining, cond)
        v = np.sum(binom.pmf(j, N+1, p)*lower, axis=1)
        if index == 0:
            owner = v.copy()
        weight += v
    return weight, owner


def profiles(xs, lam):
    """All middle-divisor signs; exact finite formulas in floating point.

    J = integral_(d-r)^d M(t)dt in normalized logarithms. Also measure
    integral |M|, after summing signs, and the earlier termwise allowance.
    """
    size = len(xs)
    values = np.zeros(size)
    variation = np.zeros(size)
    termwise = np.zeros(size)
    slot = np.zeros((size, len(PROFILE_SLOTS)))
    plateau = np.zeros(size, dtype=bool)
    identities = []
    for first in range(0, size, 128):
        x = xs[first:first+128]
        d = lam[first:first+128]-x[:, 0]
        r = x[:, -1]
        middle = x[:, 1:-1]
        sums = np.zeros((len(x), 1))
        signs = np.ones(1)
        for q in middle.T:
            sums = np.concatenate((sums, sums+q[:, None]), axis=1)
            signs = np.concatenate((signs, -signs))
        clipped = np.minimum(r[:, None], np.maximum(d[:, None]-sums, 0))
        val = np.sum(clipped*signs, axis=1)
        term = np.sum(clipped, axis=1)
        order = np.argsort(sums, axis=1)
        ordered = np.take_along_axis(sums, order, axis=1)
        balance = np.cumsum(signs[order], axis=1)
        right = np.column_stack((ordered[:, 1:], np.full(len(x), np.inf)))
        lengths = np.maximum(0, np.minimum(right, d[:, None])-
                             np.maximum(ordered, (d-r)[:, None]))
        integral = np.sum(lengths*balance, axis=1)
        identities.append(np.max(np.abs(integral-val)))
        sl = slice(first, first+len(x))
        values[sl] = val
        termwise[sl] = term
        variation[sl] = np.sum(lengths*np.abs(balance), axis=1)
        for i, v in enumerate(PROFILE_SLOTS):
            slot[sl, i] = np.sum(signs*(sums <= (d-r+v*r)[:, None]), axis=1)
        plateau[sl] = (r <= d) & np.all(middle >= d[:, None], axis=1)
        assert np.max(np.abs(val[plateau[sl]]-r[plateau[sl]]), initial=0) < 1e-12
    assert max(identities) < 2e-10
    return values, variation, termwise, slot, plateau, max(identities)


def encode(z):
    return [float(np.real(z)), float(np.imag(z))]


def model_row(N, count, power, seed):
    T, xs, volume = shapes(N, count, power, seed)
    L = float(length(N))
    lam = L/T
    W, owner = marked_weights(N, xs, count)
    J, var, term, profile, plateau, identity_error = profiles(xs, lam)
    valid = (volume > 0) & np.all(xs*T[:, None] < L, axis=1)
    radial = np.exp((N+1)*np.log(U)+N*np.log(T)-T/2-gammaln(N+1))
    base = volume*radial*W/(lam*np.prod(xs, axis=1))*valid
    signed = base*J
    model_phases = {str(y): encode(np.mean(signed*np.exp(-1j*y*T))) for y in HEIGHTS}
    # Probe whether cancellation remains when an absolute value is taken
    # only after the complete count/signed profile, not at each divisor.
    row = dict(N=N, count=count, seed=seed, samples=len(T),
        identity_error=identity_error,
        signed=float(np.mean(signed)), absolute_after_label=float(np.mean(base*np.abs(J))),
        absolute_after_profile=float(np.mean(base*var)),
        termwise_divisor_allowance=float(np.mean(base*term)),
        plateau_signed=float(np.mean(signed*plateau)),
        positive_mass=float(np.mean(np.maximum(signed, 0))),
        negative_mass=float(np.mean(np.maximum(-signed, 0))),
        zero_profile_fraction=float(np.mean(np.abs(J)<1e-13)),
        plateau_fraction=float(np.mean(plateau & valid)),
        nonowner_fraction=float(np.sum(base*np.abs(J)*np.divide(W-owner,W,
            out=np.zeros_like(W),where=W>0))/max(np.sum(base*np.abs(J)),1e-300)),
        weighted_profile=np.mean(base[:, None]*xs[:, -1, None]*profile, axis=0).tolist(),
        phases=model_phases)
    # A deterministic worst positive and negative example in this proposal.
    row['shape_extrema'] = [dict(log_shares=xs[i].tolist(), T=float(T[i]),
                                coefficient_per_log=float(J[i]/lam[i]),
                                plateau=bool(plateau[i]))
                            for i in (int(np.argmax(J)), int(np.argmin(J)))]
    if count == 5:
        small_pair = xs[:, -1]+np.min(xs[:, 1:-1],axis=1) <= lam-xs[:, 0]
        assert np.max(J[small_pair],initial=0) < 1e-12
        row['small_pair_negative_mass'] = float(np.mean(base*np.maximum(-J,0)*small_pair))
        row['small_pair_sign_violation'] = float(np.max(J[small_pair],initial=0))
    return row


def certified_near_log(target, excluded):
    """Exact Proth certificate, advancing past already used primes."""
    while True:
        try:
            p, cert = proth_near_log(target)
        except RuntimeError:
            m = int(mp.ceil(target/(2*mp.log(2))))+1
            k = int(mp.ceil(mp.exp(target)/2**m))
            k += 1-k%2
            while True:
                assert 0 < k < 2**m
                p = k*2**m+1
                witness = next((a for a in [2,3,5,7,11,13,17,19,23,29,31]
                                if pow(a,(p-1)//2,p)==p-1), None)
                if witness is not None:
                    cert = dict(k=str(k),m=m,witness=witness)
                    break
                k += 2
        if p not in excluded:
            return p, cert
        target = mp.log(p+1)


def certified_row(N, count, seed):
    T0, xs0, volume = shapes(N, count, 2, seed)
    candidates = np.flatnonzero(volume > 0)
    if not len(candidates):
        return None
    index = int(candidates[0])
    primes, certificates = [], []
    for x in xs0[index]:
        target = mp.mpf(str(T0[index]))*mp.mpf(str(x))
        p, cert = certified_near_log(target, primes)
        check_certificate(p, cert)
        primes.append(p)
        certificates.append(cert)
    pairs = sorted(zip(primes, certificates), reverse=True)
    primes = [p for p, _ in pairs]
    assert len(set(primes)) == count
    logs = [mp.log(p) for p in primes]
    T, L = mp.fsum(logs), length(N)
    physical = 20000**N//(10001**N*(N+1))+2
    assert mp.mpf('1.95')*N < T <= mp.mpf('2.03')*N
    assert all(N*N<p<physical*physical for p in primes)
    assert mp.mpf('.5') < logs[0]/T < mp.mpf('.6')
    assert mp.mpf('.005') < logs[-1]/T < mp.mpf('.06')
    d, h = L-logs[0], logs[-1]
    clipped = mp.mpf(0)
    for bits in itertools.product((0,1), repeat=count-2):
        subtotal = mp.fsum(x for bit,x in zip(bits,logs[1:-1]) if bit)
        clipped += (-1)**sum(bits)*min(h,max(mp.mpf(0),d-subtotal))
    shares = np.array([[float(x/T) for x in logs]])
    J, var, term, profile, plateau, _ = profiles(shares, np.array([float(L/T)]))
    error = abs(float(clipped/T)-J[0])
    assert error < 1e-10
    W, owner = marked_weights(N,shares,count)
    if count<14:
        separate = sum(float(rectangle_values(N,np.array([x]),shares[:,-1])[0])
                       for x in shares[0,:-1])
        assert abs(separate-W[0]) < 1e-11
    coefficient = T*clipped/L
    log_kernel = (N+1)*mp.log(mp.mpf(10001)/20000)+N*mp.log(T)-mp.loggamma(N+1)-mp.mpf('1.5')*T
    return dict(N=N,count=count,seed=seed,integer=str(math.prod(primes)),
        primes=[str(p) for p in primes],certificates=[c for _,c in pairs],
        log_shares=shares[0].tolist(),total_log=mp.nstr(T,45),
        coefficient_per_log=mp.nstr(clipped/L,45),
        profile_integral_per_log=mp.nstr(clipped/T,45),
        profile_float_error=error,termwise_per_log=float(term[0]),
        profile_variation_per_log=float(var[0]),plateau=bool(plateau[0]),
        marked_weight=float(W[0]),largest_mark_weight=float(owner[0]),
        source_log_kernel=mp.nstr(log_kernel,45),
        weighted_real_coefficient=mp.nstr(coefficient*mp.mpf(str(W[0])),45),
        phases={str(y):encode(complex(mp.exp(-mp.j*y*T))) for y in HEIGHTS})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--orders', type=int, nargs='+', default=[256,512,1024])
    parser.add_argument('--power', type=int, default=11)
    parser.add_argument('--max-count', type=int, default=14)
    parser.add_argument('--seeds', type=int, default=2)
    parser.add_argument('--certificate-cases', type=int, default=1)
    parser.add_argument('--resume', action='store_true', help='Resume interrupted diagnostics; record both producer hashes')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert 3 <= args.max_count <= 18, 'Subset enumeration probe, not an all-count tail bound'
    mp.mp.dps=600
    result = dict(scope='Diagnostic only: no arithmetic population estimate, packet bound or zero exclusion',
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        target='lowerThresholdPacket(counts 3..55) - shortOverflowPacket(counts 3..13)',
        model='ordinary-prime density, NOT zero modes and NOT a proved prime-sum approximation',
        omitted_count_tail=f'{args.max_count+1}..55 UNBOUNDED in this experiment',
        model_support='Explicit core, physical, squarefree/distinct continuum variables, owner/least interior and count tests; not an evaluation of the full Lean Finset',
        sample_bias='Certified Proth primes at randomized log targets, not uniform prime products',
        profile_slots=PROFILE_SLOTS.tolist(),rows=[],summaries=[],certified=[])
    if args.resume and args.output.exists():
        previous = json.loads(args.output.read_text())
        assert previous['target']==result['target'] and previous['profile_slots']==result['profile_slots']
        assert previous['omitted_count_tail']==result['omitted_count_tail']
        assert all(row['samples']==2**args.power for row in previous['rows'])
        for key in ('rows','summaries','certified'):
            result[key]=previous[key]
        result['producer_history']=previous.get('producer_history',[])+[previous['script_sha256']]
        result['resumption_note']='Earlier model and certified rows retained; model formulas unchanged. Certificate search now advances past duplicates.'
    def save():
        args.output.write_text(json.dumps(result,indent=2)+'\n')
    for N in args.orders:
        for seed in range(args.seeds):
            if any(s['N']==N and s['seed']==seed for s in result['summaries']):
                continue
            rows=[]
            for count in range(3,args.max_count+1):
                row=model_row(N,count,args.power,20260926+100*seed+count)
                rows.append(row)
            result['rows'].extend(rows)
            summary=dict(N=N,seed=seed,
                **{key:sum(row[key] for row in rows) for key in
                   ['signed','absolute_after_label','absolute_after_profile','termwise_divisor_allowance','plateau_signed']},
                phases={str(y):np.sum([row['phases'][str(y)] for row in rows],axis=0).tolist() for y in HEIGHTS},
                weighted_profile=np.sum([row['weighted_profile'] for row in rows],axis=0).tolist())
            result['summaries'].append(summary)
            print(json.dumps(summary),flush=True)
            save()
    for N in [n for n in args.orders if n<=512]:
        for count in range(3,min(args.max_count,14)+1):
            for index in range(args.certificate_cases):
                if any(r['N']==N and r['count']==count and r['seed']==9173+100*index+count
                       for r in result['certified']):
                    continue
                row=certified_row(N,count,9173+100*index+count)
                if row is not None:
                    result['certified'].append(row)
                    print(json.dumps({'certified':len(result['certified']), 'N':N,'count':count,
                        'coefficient_per_log':row['coefficient_per_log'],'plateau':row['plateau']}),flush=True)
                    save()
    # Enrich a resumed report with this sign criterion without recomputing
    # unrelated high-dimensional count diagnostics or altering their totals.
    for i,row in enumerate(result['rows']):
        if row['count']==5 and 'small_pair_negative_mass' not in row:
            new = model_row(row['N'],5,int(math.log2(row['samples'])),row['seed'])
            assert abs(new['signed']-row['signed'])<1e-14
            result['rows'][i]=new
    for row in result['certified']:
        if row['count']==5:
            logs=[mp.log(int(p)) for p in row['primes']]
            gap=length(row['N'])-logs[0]-logs[-1]-logs[-2]
            row['small_pair_cutoff_gap']=mp.nstr(gap,45)
            row['small_pair_below_cutoff']=bool(gap>=0)
            if gap>=0:
                assert mp.mpf(row['coefficient_per_log'])<=mp.mpf('1e-100')
    save()


if __name__=='__main__':
    main()
