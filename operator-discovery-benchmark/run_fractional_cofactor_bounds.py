"""Run the adaptive rational-weight extension on verified035 states."""
from fractions import Fraction as F
import json
from pathlib import Path
import resource
import time

import adaptive_rational_exponents as A
import fractional_cofactor_bounds as P

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'prime-cofactor-bound-results/pilot-001'
OUT = ROOT / 'fractional-cofactor-bound-results/pilot-001'
FILES = ['adaptive_rational_exponents.py', 'fractional_cofactor_bounds.py',
         'check_fractional_cofactor_bounds.py', 'run_fractional_cofactor_bounds.py',
         'test_adaptive_rational_exponents.py', 'test_fractional_cofactor_bounds.py',
         'test_check_fractional_cofactor_bounds.py',
         'adaptive_rational_exponents_development.json',
         'fractional_cofactor_bounds_development.json',
         'check_fractional_cofactor_bounds_development.json',
         'fractional_cofactor_bounds_protocol.txt']


def write(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as stream:
        json.dump(obj, stream, indent=2, sort_keys=True)
        stream.write('\n')


def read(path):
    return json.loads(path.read_text())


def main():
    import check_fractional_cofactor_bounds as C
    started = time.monotonic()
    resource.setrlimit(resource.RLIMIT_AS, (16*1024**3,
                        resource.getrlimit(resource.RLIMIT_AS)[1]))
    if read(BASE/'report.json')['status'] != 'PRIME_STATES_AND_AUXILIARY_BOUNDS_VERIFIED_JOINED_BOUND_OPEN':
        raise ValueError('completed035source-bound result required')
    if not read(BASE/'verification.json')['verified']:
        raise ValueError('035state and bound admission required')
    # Reusing the checked source-law backend is a premise check, not an old run.
    if (ROOT/'check_prime_cofactor_discovery.py').read_bytes() != (
            BASE/'source_snapshot/check_prime_cofactor_discovery.py').read_bytes():
        raise ValueError('unchanged035source-law checker required')
    OUT.mkdir(parents=True, exist_ok=False)
    try:
        for name in FILES:
            destination = OUT/'source_snapshot'/name
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes((ROOT/name).read_bytes())
        for name in ('search.json', 'verification.json', 'next_search_input.json'):
            (OUT/'source_snapshot'/('base035_'+name)).write_bytes((BASE/name).read_bytes())
        base = read(BASE/'search.json')['certificate']
        cursor, batches, exponents = None, [], []
        for index in range(4):
            batch = A.next_batch(cursor=cursor, lower='0', upper='1',
                max_candidates=32, work_budget=100000,
                requested=['1/257'] if index == 0 else ())
            cursor = batch['cursor']
            batches.append(batch)
            exponents.extend(batch['candidates'])
        if len(set(exponents)) != len(exponents) or '1/257' not in exponents:
            raise ValueError('resumable canonical enumeration and requested coverage')
        write(OUT/'exponent_batches.json', batches)
        proposal = P.search(base, exponents)
        write(OUT/'search.json', proposal)
        meter = C.C.Meter()
        verification = C.verify(base['source'], base, proposal, meter=meter)
        if not verification['verified']:
            raise ValueError('fractional bounds and recovery admission failed')
        write(OUT/'verification.json', verification)
        root = [c for c in proposal['candidates'] if c['state'] == 0]
        report = dict(status='ADAPTIVE_FRACTIONAL_COMPONENT_BOUNDS_VERIFIED_JOINED_BOUND_OPEN',
            exponent_count=len(exponents), candidate_count=len(proposal['candidates']),
            denominators=sorted({F(x).denominator for x in exponents}),
            no_semantic_denominator_ceiling=True, resumable_cursor=cursor,
            weighted_root_subpower_bounds=sum(F(c['energy_upper']['power']) <= 0 for c in root),
            recovered_root_power_improvements=sum(c['recovery']['strict_power_improvement'] for c in root),
            recovered_all_state_power_improvements=proposal['recovered_strict_power_improvements'],
            representative_root_candidates=[c for c in root if c['gamma'] in
                ('0', '1/257', '1/7', '1/5', '1/2', '2/3', '1')],
            source='complete original f and035machine-generated states',
            arithmetic_observations_rerun=False, numerical_slopes_used=False,
            scope='coefficient twists with full partial-prefix Abel recovery',
            broader_fractional_constructions_refuted=False,
            search_operations=proposal['operations'],
            enumeration_operations=sum(batch['operations'] for batch in batches),
            checker_operations=meter.operations,
            enumeration_batches='exponent_batches.json', verification='verification.json',
            development_receipts={name:read(ROOT/name) for name in FILES if name.endswith('_development.json')},
            elapsed_seconds=time.monotonic()-started,
            peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            whole_signed_bound_proved=False, RH_proved=False)
        next_input = read(BASE/'next_search_input.json')
        next_input['fractional_language'] = dict(
            exponent_scheduler='adaptive_rational_exponents.next_batch',
            cursor=cursor, semantic_denominator_ceiling=None,
            constructions=['coefficient_twist', 'explicit_signed_power'],
            checked_provider='rational coefficient twist + every-prefix signed Abel recovery',
            current_result='no power improvement survives recovery in this supplied proof family',
            next_target='fractional coupled scale/cutoff constructions with genuinely cheaper recovery',
            energy_endpoint_alone_does_not_pay_Abel_input=True,
            unrelated_fractional_constructions_refuted=False)
        write(OUT/'next_search_input.json', next_input)
        for name in FILES:
            if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
                raise ValueError('frozen036source changed: '+name)
        for name in ('search.json', 'verification.json', 'next_search_input.json'):
            if (BASE/name).read_bytes() != (OUT/'source_snapshot'/('base035_'+name)).read_bytes():
                raise ValueError('035source premise changed: '+name)
        if time.monotonic()-started > 900:
            raise RuntimeError('036runtime cap900seconds')
        write(OUT/'report.json', report)
        print(json.dumps({k:v for k,v in report.items() if k not in
            ('development_receipts', 'resumable_cursor', 'representative_root_candidates')}), flush=True)
    except Exception as error:
        write(OUT/'terminal_failure.json', dict(error=type(error).__name__, message=str(error),
            elapsed_seconds=time.monotonic()-started, whole_signed_bound_proved=False, RH_proved=False))
        raise


if __name__ == '__main__':
    main()
