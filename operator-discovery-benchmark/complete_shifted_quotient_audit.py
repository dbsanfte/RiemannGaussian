"""Finish only the six unfinished cases under a recorded7% audit extension.

Independent Euler-subset expansion of the three-factor word.  This is an
audit algorithm change, not a new candidate, score, scale, or study attempt.
"""
from concurrent.futures import ProcessPoolExecutor, as_completed
from fractions import Fraction as Q
from math import comb, isqrt
from pathlib import Path
import argparse
import json
import resource
import time
from flint import arb, ctx

import check_shifted_quotient_candidates as C
import run_shifted_quotient_discovery as R
from shifted_quotient_candidates import Meter

PROGRAM = {'shifts': ['1/6', '1/3', '1/2']}
ADDITIONAL = 56000000
FILES = ['complete_shifted_quotient_audit.py', 'test_complete_shifted_quotient_audit.py',
         'shifted_completion_development.json']


def table(H, meter):
    meter.charge(H+1)
    spf = [0]*(H+1)
    for p in range(2, isqrt(H)+1):
        if not spf[p]:
            meter.charge((H-p*p)//p+1)
            for n in range(p*p, H+1, p):
                if not spf[n]: spf[n] = p
    return spf


def reconstruct(source, H, scales, meter):
    """Product of (Q*zeta_shift-1) by inclusion-exclusion, including overlaps."""
    if source not in C.SOURCES or type(H) is not int or not 1 <= H <= 262143:
        raise ValueError('bounded declared complete source')
    if any(type(x) is not int or x < 1 or 2*x-1 > H for x in scales):
        raise ValueError('complete blocks')
    spf = table(H, meter)
    values = [[arb(0)]*(H+1) for _ in range(8)]
    for mask in range(1, 8): values[mask][1] = arb(1)
    meter.live(18*(H+1)+4096)
    for p in range(2, H+1):
        meter.charge()
        if spf[p]: continue
        power = p; indices = []
        while power <= H:
            indices.append(power); power *= p; meter.charge(2)
        K = len(indices)
        meter.charge(66)
        root = arb(p)**(-arb(1)/6)
        weights = [root, root*root, root*root*root]
        sign = -1 if source == 'mu' or p <= 13 else 1
        for mask in range(1, 8):
            degree = mask.bit_count()
            if source == 'one':
                local = [arb(comb(degree+e-1, e)) for e in range(K+1)]
            else:
                local = [arb(sign**e*comb(degree,e) if e <= degree else 0) for e in range(K+1)]
            meter.charge(3*(K+1))
            for j, weight in enumerate(weights):
                if mask & (1 << j):
                    meter.charge(2*K)
                    for e in range(1, K+1): local[e] += weight*local[e-1]
            for index, value in zip(indices, local[1:]): values[mask][index] = value
            meter.charge(K)
    for n in range(2, H+1):
        p = spf[n] or n
        rest = n
        while rest % p == 0:
            rest //= p; meter.charge(2)
        if rest > 1:
            part = n//rest
            meter.charge(14)
            for mask in range(1, 8): values[mask][n] = values[mask][part]*values[mask][rest]
    rows = C.normalizer(PROGRAM, meter)
    total, absolute = arb(0), arb(0)
    sums = {x: [arb(0), arb(0)] for x in scales}
    for n in range(1, H+1):
        coefficient = arb(0)
        if n > 1:
            for mask in range(1, 8):
                coefficient += (-1 if (3-mask.bit_count()) % 2 else 1)*values[mask][n]
            coefficient *= 36
        total += coefficient; absolute += abs(coefficient)
        meter.charge(18)
        active = [x for x in scales if x <= n < 2*x]
        if not active: continue
        # Every exponent is an integer multiple of1/6. One certified root
        # retains all three exact monomials, rather than three transcendentals.
        root = arb(n)**(arb(1)/6)
        powers = [arb(1), root]
        for j in range(2, 6): powers.append(powers[-1]*root)
        main, envelope = arb(0), arb(0)
        for row, exponent in zip(rows, (5, 4, 3)):
            main += row['coefficient']*powers[exponent]
            envelope += abs(row['coefficient'])*powers[exponent]
        signed, path = total-main, absolute+envelope
        meter.charge(82)
        for x in active:
            sums[x][0] += signed**2
            sums[x][1] += path**2
            meter.charge(4)
    return [dict(X=x, energy=sums[x][0]/(x*x), absolute_energy=sums[x][1]/(x*x)) for x in scales]


def baselines(H, scales, meter):
    """All three matched baselines by exact local binomial polynomials."""
    spf = table(H, meter)
    sums = {k: {x: [0, 0] for x in scales} for k in (1, 2, 3)}
    prefix, absolute = [0]*4, [0]*4
    for n in range(2, H+1):
        residue = n
        coefficients = [0, 1, 1, 1]
        while residue > 1:
            p = spf[residue] or residue
            e = 0
            while residue % p == 0:
                residue //= p; e += 1; meter.charge(2)
            for j in (1, 2, 3):
                coefficients[j] *= (-1)**e*comb(j, e) if e <= j else 0
            meter.charge(9)
        a, b, c = coefficients[1:]
        row = [0, a, b-2*a, c-3*b+3*a]
        meter.charge(6)
        for k in (1, 2, 3):
            prefix[k] += row[k]; absolute[k] += abs(row[k]); meter.charge(3)
            for x in scales:
                if x <= n < 2*x:
                    sums[k][x][0] += prefix[k]**2
                    sums[k][x][1] += absolute[k]**2
                    meter.charge(4)
    return {str(k): [dict(X=x, energy=arb(sums[k][x][0])/(x*x),
                         absolute_energy=arb(sums[k][x][1])/(x*x)) for x in scales] for k in (1, 2, 3)}


def pending(directory):
    report = R.read(directory/'report.json')
    if report['status'] != 'INCOMPLETE' or report['total_operations'] != 800000000:
        raise ValueError('exact original exhausted audit retained')
    expected = [{'stage': 'discovery', 'id': i, 'cases': 8} for i in range(25)]
    for source in C.SOURCES:
        audit = R.read(directory/('audit_'+source+'.json'))
        extra = ([dict(stage='discovery_baseline', degree=k, cases=8) for k in (1, 2, 3)] if source == 'mu' else [])
        extra += [dict(stage='final', id=i, cases=2) for i in (1, 10)]
        if (audit['status'] != 'incomplete' or audit['errors'] != ['study operation cap']
                or audit['checked'] != expected+extra):
            raise ValueError('exact unfinished cases only; no completed numerical repeats')
        final = R.read(directory/('final_'+source+'.json'))
        candidate = next(r for r in final['rows'] if r['id'] == 15)
        if candidate['program'] != PROGRAM or [r['X'] for r in candidate['cases']] != R.FINAL:
            raise ValueError('fixed existing selected candidate and final blocks')
    return report


def worker(directory, source, cap, deadline):
    ctx.prec = 192
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, hard))
    meter = Meter(cap); meter.deadline = deadline
    checked = []
    try:
        final = R.read(directory/('final_'+source+'.json'))
        row = next(r for r in final['rows'] if r['id'] == 15)
        R.compare_rows(row['cases'], reconstruct(source, 131071, R.FINAL, meter))
        checked.append(dict(stage='final', id=15, cases=2))
        if source == 'mu':
            actual = baselines(131071, R.FINAL, meter)
            for degree in (1, 2, 3):
                R.compare_rows(final['baselines'][str(degree)], actual[str(degree)])
                checked.append(dict(stage='final_baseline', degree=degree, cases=2))
        status, error = 'verified', None
    except (ValueError, ArithmeticError, OverflowError, TimeoutError, MemoryError) as failure:
        status, error = 'incomplete', str(failure) or type(failure).__name__
    return dict(source=source, status=status, error=error, checked=checked, counts=meter.counts(),
                peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)


def run(directory):
    directory = Path(directory).resolve()
    R.verify_source(directory)
    old = pending(directory)
    development = R.read(R.ROOT/'shifted_completion_development.json')
    if development['runs'][-1]['returncode'] != 0:
        raise ValueError('passed cumulative completion calibration')
    extra = development['operations']+100000
    if extra >= ADDITIONAL:
        raise OverflowError('extension includes all preparatory work')
    R.write(directory/'audit_work_extension.json', dict(original_limit=800000000,
             additional_limit=ADDITIONAL, extended_limit=856000000, percent=7,
             scope='only final id15 for3sources and3mu baselines; no search or selection changes',
             reason='original divisor-row audit exhausted its cap; use exact Euler-subset identity and shared sixth roots',
             authorization='earlier user allowance for a small work-limit extension around7percent',
             previous_spent_work_retained=True, completed_numeric_cases_repeated=False,
             development=development, metadata_reserve=100000, source_files=FILES, hashes=False))
    snapshot = directory/'completion_source_snapshot'; snapshot.mkdir()
    for name in FILES: (snapshot/name).write_bytes((R.ROOT/name).read_bytes())
    deadline = R.read(directory/'started.json')['monotonic']+R.SECONDS
    remaining = ADDITIONAL-extra
    # The actual-mu worker also verifies all three baselines.
    caps = {'mu': remaining*40//100, 'one': remaining*30//100,
            'partial_prime_13': remaining-remaining*40//100-remaining*30//100}
    records = []
    with ProcessPoolExecutor(max_workers=3) as pool:
        futures = [pool.submit(worker, directory, source, caps[source], deadline) for source in C.SOURCES]
        for future in as_completed(futures):
            row = future.result(); records.append(row); extra += row['counts']['operations']
            R.write(directory/('completion_'+row['source']+'.json'), row)
            print(json.dumps(row), flush=True)
    R.verify_source(directory)
    for name in FILES:
        if (snapshot/name).read_bytes() != (R.ROOT/name).read_bytes():
            raise ValueError('completion source bytes changed')
    verified = all(r['status'] == 'verified' for r in records) and extra <= ADDITIONAL
    R.write(directory/'independent_completion.json', dict(
        status='FINITE_INTERVAL_EVALUATIONS_VERIFIED_WITH_WORK_EXTENSION' if verified else 'INCOMPLETE',
        total_operations=old['total_operations']+extra, extension_operations=extra,
        extended_limit=856000000, previous_checked_blocks=old['checked_blocks'],
        newly_checked_blocks=sum(r['cases'] for a in records for r in a['checked']),
        records=records, **R.P.FLAGS))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('directory')
    run(parser.parse_args().directory)
