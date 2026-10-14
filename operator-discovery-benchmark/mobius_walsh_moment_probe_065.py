"""Exact post-study moment diagnostics, never a uniform or universal proof.

Inspect the already admitted beta-one construction. Dyadic row intervals
are fixed before observation; no exponents, weights or partitions are fitted.
"""
from fractions import Fraction as Q
from math import isqrt
import json
import resource
import time

from prime_transfer_algebra_058 import Meter


def root_upper(value):
    """Smallest multiple of 1/4096 whose square dominates value."""
    if value < 0:
        raise ValueError('nonnegative moment product')
    target = value.numerator * 4096**2
    k = isqrt(target // value.denominator)
    if k*k*value.denominator < target:
        k += 1
    return Q(k, 4096)


def intervals(H):
    if type(H) is not int or H < 1:
        raise ValueError('positive row horizon')
    J = 1
    while J <= H:
        yield J, min(2*J-1, H)
        J *= 2


def character_sign(index, radius, conditioned, cache, meter):
    if type(index) is not int or not 1 <= index <= max(radius, 1)**4:
        raise ValueError('degree-four character index within radius')
    if index in cache:
        return cache[index]
    n, sign, p = index, 1, 2
    while p*p <= n:
        meter.charge(16)
        if n % p == 0:
            n //= p
            if n % p == 0 or p > radius or p in conditioned:
                raise ValueError('squarefree unconditioned character')
            sign = -sign
        p += 1 if p == 2 else 2
    if n > 1:
        if n > radius or n in conditioned:
            raise ValueError('remaining prime within radius')
        sign = -sign
    cache[index] = sign
    return sign


def moment(rows):
    W = sum((row['w'] for row in rows), Q(0))
    A = sum((row['A'] for row in rows), Q(0))
    result = {'weight_mass': str(W), 'coefficient_mass': str(A)}
    for label, key in (('actual', 'minus'), ('all_free_plus', 'plus')):
        E = sum((row[key]**2/row['w'] for row in rows if row['w']), Q(0))
        V = sum((abs(row[key]) for row in rows), Q(0))
        upper = root_upper(W*E)
        if V > upper:
            raise ValueError('exact weighted Cauchy check')
        result.update({label+'_energy': str(E), label+'_variation': str(V),
                       label+'_cauchy_product': str(W*E),
                       label+'_cauchy_upper': str(upper)})
    return result


def analyze_endpoint(parent, certificate, H, radius, conditioned, meter):
    if parent['ratio'] != certificate['ratio']:
        raise ValueError('same endpoint')
    rows, weights = parent['rows'], list(map(Q, certificate['weights']))
    if len(rows) != H or len(weights) != H:
        raise ValueError('complete row horizon')
    cache, values = {1: 1}, []
    for j, (row, w) in enumerate(zip(rows, weights), 1):
        if row['j'] != j:
            raise ValueError('ordered complete rows')
        A, minus, plus = Q(0), Q(0), Q(0)
        for term in row['terms']:
            a = Q(term['coefficient'])
            minus += a*character_sign(term['index'], radius, conditioned, cache, meter)
            plus += a
            A += abs(a)
            meter.charge(32)
        if (A == 0 and w != 0) or (A > 0 and not A <= w < Q(17, 16)*A):
            raise ValueError('beta-one precision-four weight scope')
        values.append({'j': j, 'A': A, 'w': w, 'minus': minus, 'plus': plus})
    global_moment = moment(values)
    if global_moment['weight_mass'] != certificate['weight_mass']:
        raise ValueError('same total weight')
    if global_moment['coefficient_mass'] != parent['l1']:
        raise ValueError('same parent coefficient mass')
    E_minus, E_plus = Q(0), Q(0)
    for term in certificate['energy_terms']:
        a = Q(term['coefficient'])
        E_minus += a*character_sign(term['index'], radius, conditioned, cache, meter)
        E_plus += a
        meter.charge(32)
    if [str(E_minus), str(E_plus)] != [global_moment['actual_energy'], global_moment['all_free_plus_energy']]:
        raise ValueError('row-square and Walsh evaluations disagree')
    if min(E_minus, E_plus) < 0 or max(E_minus, E_plus) > Q(certificate['energy_upper']):
        raise ValueError('saved universal upper must cover both assignments')
    blocks = []
    for start, stop in intervals(H):
        blocks.append({'start': start, 'stop': stop, **moment(values[start-1:stop])})
    for name in ('weight_mass', 'coefficient_mass', 'actual_energy', 'actual_variation',
                 'all_free_plus_energy', 'all_free_plus_variation'):
        if sum((Q(b[name]) for b in blocks), Q(0)) != Q(global_moment[name]):
            raise ValueError('complete additive partition')
    partition = {label+'_partition_cauchy_upper': str(sum((Q(b[label+'_cauchy_upper']) for b in blocks), Q(0)))
                 for label in ('actual', 'all_free_plus')}
    return {'ratio': parent['ratio'], 'global': global_moment, 'blocks': blocks,
            **partition, 'row_square_equals_walsh_evaluation': True,
            'rows': [{k: str(v) if isinstance(v, Q) else v for k, v in row.items()} for row in values]}


def main():
    from run_mobius_walsh_energy_065 import OUT as PARENT, ROOT, FILES as PARENT_FILES
    from run_fractional_prime_kernel_051 import write, check_receipt
    output = PARENT/'moment_diagnostic_001'
    if output.exists():
        raise FileExistsError('preserve every diagnostic attempt')
    started = time.monotonic()
    files = ['mobius_walsh_moment_probe_065.py', 'test_mobius_walsh_moment_probe_065.py',
             'mobius_walsh_moment_probe_065_development.json', 'mobius_walsh_moment_probe_protocol_065.txt',
             'MOBIUS_WALSH_UNIFORM_PREFACTOR_REVIEW_065.txt']
    frozen = {name: (ROOT/name).read_bytes() for name in files}
    receipt = json.loads(frozen['mobius_walsh_moment_probe_065_development.json'])
    development = check_receipt(receipt)
    for name in PARENT_FILES:
        if (ROOT/name).read_bytes() != (PARENT/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve frozen065 source '+name)
    parent_report = json.loads((PARENT/'report.json').read_text())
    if parent_report['exact_energy_certificates_independently_verified'] != 324 or parent_report['RH_proved']:
        raise ValueError('completed065 study with open uniform bound')
    names = sorted(PARENT.glob('energy_*.json'))
    if len(names) != 36:
        raise ValueError('all36 admitted parents')
    output.mkdir()
    (output/'source_snapshot').mkdir()
    for name, data in frozen.items():
        (output/'source_snapshot'/name).write_bytes(data)
    meter = Meter(cap=500_000_000, seconds=300)
    summaries = []
    try:
        for path in names:
            size = path.stat().st_size
            if size > 64*1024**2:
                raise MemoryError('bounded diagnostic input size')
            meter.reserve(64*1024**2+12*size)
            saved = json.loads(path.read_text())
            candidates = [c for c in saved['candidates'] if '1' in c['weight_powers']]
            if len(candidates) != 1:
                raise ValueError('unique saved beta-one policy')
            candidate = candidates[0]
            cert, parent = candidate['certificate'], saved['source_parent_certificate']
            if not candidate['source_bound_by_same_admitted_064_parent'] or not candidate['verification']['verified']:
                raise ValueError('saved source-bound independent admission')
            for k in ('N', 'y', 'H', 'K', 'conditioned_primes'):
                if parent[k] != cert[k] or candidate['verification'][k] != cert[k]:
                    raise ValueError('same065 parent')
            endpoints = []
            for e, (p, c) in enumerate(zip(parent['endpoints'], cert['endpoints'])):
                result = analyze_endpoint(p, c, parent['H'], max(parent['H'], parent['K']),
                                          set(parent['conditioned_primes']), meter)
                if result['global']['actual_variation'] != saved['actual_repair_endpoint_l1'][e]:
                    raise ValueError('same actual064/063 repair price')
                if result['global']['all_free_plus_variation'] != candidate['verification']['endpoints'][e]['all_free_plus_l1']:
                    raise ValueError('same common-sign witness')
                endpoints.append(result)
            record = {k: saved[k] for k in ('N', 'y', 'H', 'K', 'theta', 'rule', 'remaining_prime_count')}
            record.update({'source_energy_file': path.name, 'weight_powers': candidate['weight_powers'],
                           'endpoints': endpoints, 'finite_diagnostic_only': True,
                           'new_universal_bound_proved': False, 'uniform_growth_proved': False})
            write(output/path.name.replace('energy_', 'moments_', 1), record)
            summaries.append({k: v for k, v in record.items() if k != 'endpoints'} |
                             {'endpoints': [{k: v for k, v in e.items() if k != 'rows'} for e in endpoints]})
        for name, data in frozen.items():
            if (ROOT/name).read_bytes() != data:
                raise ValueError('preserve diagnostic source '+name)
        write(output/'summary.json', {'cases': summaries, 'finite_diagnostic_only': True})
        report = {'status': 'EXACT_ACTUAL_AND_COMMON_SIGN_BLOCK_MOMENTS_UNIFORM_BOUND_OPEN',
                  'cases': len(summaries), 'two_way_endpoint_energy_equalities': 4*len(summaries),
                  'new_synthetic_tests': receipt['unique_new_synthetic_tests'],
                  'development_operations': development, 'diagnostic_operations': meter.operations,
                  'elapsed_seconds': time.monotonic()-started,
                  'peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
                  'prospective_storage_bytes': meter.peak_bytes_estimate, 'new_frozen_files': len(files),
                  'source_065_scores_previously_observed': True, 'protocol_frozen_before_new_moments': True,
                  'partition': '[2^k,min(2^(k+1)-1,H)]', 'actual_moments_are_not_universal_uppers': True,
                  'old_studies_or_test_suites_replayed': False, 'hashes_used': False,
                  'new_universal_bound_proved': False, 'uniform_growth_proved': False, 'RH_proved': False}
        write(output/'report.json', report)
        print(json.dumps(report, sort_keys=True))
    except BaseException as exc:
        write(output/'failure.json', {'type': type(exc).__name__, 'message': str(exc),
                                     'completed_cases': len(summaries), 'RH_proved': False})
        raise


if __name__ == '__main__':
    main()
