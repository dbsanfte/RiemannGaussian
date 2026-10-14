"""Frozen symbolic operator/argument discovery, with independent admission."""
from collections import Counter
from pathlib import Path
from fractions import Fraction as Q
import json
import multiprocessing as mp
import resource
import time

import run_prime_insertion_middle_057 as PRIOR
from run_fractional_prime_kernel_051 import write, emit, check_receipt
import prime_transfer_algebra_058 as ALG
import prime_transfer_search_058 as SEARCH

ROOT = Path(__file__).resolve().parent
OUT = PRIOR.OUT/'transfer_followup_001'
UNIVERSE = [2, 3, 5]
ALPHAS = ['1/5', '2/7', '3/11']
FILES = ['prime_transfer_algebra_058.py', 'test_prime_transfer_algebra_058.py',
    'prime_transfer_algebra_058_development.json', 'PRIME_TRANSFER_ALGEBRA_SCOPE_058.txt',
    'check_prime_transfer_058.py', 'test_check_prime_transfer_058.py',
    'check_prime_transfer_058_development.json', 'PRIME_TRANSFER_CHECK_SCOPE_058.txt',
    'prime_transfer_search_058.py', 'test_prime_transfer_search_058.py',
    'run_prime_transfer_058.py', 'test_run_prime_transfer_058.py',
    'prime_transfer_root_058_development.json', 'prime_transfer_protocol_058.txt',
    'PRIME_TRANSFER_REVIEW_058.txt']
WORKER_UNIVERSE = WORKER_ATOMS = None


def validate_parent():
    counts = PRIOR.validate_parent()
    snapshots = list((PRIOR.OUT/'source_snapshot').iterdir())
    if len(snapshots) != len(PRIOR.FILES) or any((ROOT/p.name).read_bytes() != p.read_bytes() for p in snapshots):
        raise ValueError('preserve all frozen057 sources')
    report = json.loads((PRIOR.OUT/'report.json').read_text())
    if report['uniform_middle_bound_proved'] is not False or report['RH_proved'] is not False:
        raise ValueError('057 arithmetic bound remains open')
    name = 'PRIME_INSERTION_MIDDLE_CANDIDATE_REVIEW_057.txt'
    if (ROOT/name).read_bytes() != (PRIOR.OUT/name).read_bytes(): raise ValueError('preserve the new057 analytic input')
    return counts+[len(snapshots)]


def basis_request(universe, atoms, relation):
    active = [(a, c) for a, c in zip(atoms, relation['coefficients']) if Q(c)]
    if len(relation['coefficients']) != len(atoms) or not active: raise ValueError('complete nonzero basis relation')
    return {'universe': universe, 'atoms': [a for a, c in active], 'coefficients': [c for a, c in active]}


def compile_candidate(universe, atoms, row):
    import check_prime_transfer_058 as CHECK
    sm, cm = SEARCH.Meter(), CHECK.Meter(cap=10_000_000_000, seconds=7200)
    req = SEARCH.request(universe, atoms, row)
    identity = CHECK.verify_identity(req, cm)
    current = SEARCH.request(universe, atoms, row, True)
    order = SEARCH.order_certificate(current, sm)
    verified_order = CHECK.verify_source_order(current, order, cm)
    return {'candidate': row, 'identity_request': req, 'identity_verification': identity,
        'current_operator': current, 'source_order': order, 'source_order_verification': verified_order,
        'interpretation': SEARCH.identify_exchange(universe, atoms, row, sm),
        'proof_attempt': SEARCH.closure_attempt(universe, atoms, row, order),
        'operations': {'producer': sm.operations, 'checker': cm.operations},
        'worker_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'uniform_full_source_bound_proved': False, 'RH_proved': False}


def worker_init(universe, atoms):
    global WORKER_UNIVERSE, WORKER_ATOMS
    WORKER_UNIVERSE, WORKER_ATOMS = universe, atoms


def worker_task(row): return compile_candidate(WORKER_UNIVERSE, WORKER_ATOMS, row)


def target_obstruction(universe, forced_primes, meter, checker_meter):
    import check_prime_transfer_058 as CHECK
    req = {'universe': universe, 'atoms': [{'primes': forced_primes, 'divisor': 1, 'attenuation': 1}], 'coefficients': ['1']}
    cert = SEARCH.order_certificate(req, meter)
    checked = CHECK.verify_source_order(req, cert, checker_meter)
    free = next(c for c in cert['cases'] if not any(c['presence']))
    return {'target': req, 'source_order': cert, 'verification': checked,
        'unregistered_sector_polynomial_in_y': free['terms'],
        'obstruction': 'NONZERO_CURRENT_SECTOR_WHILE_EVERY_STRICTLY_LOWER_ATOM_VANISHES' if free['terms'] else 'NO_SECTOR_OBSTRUCTION',
        'scope': 'pointwise complete-valuation identity grammar with registered-prime divisors>1',
        'rules_out_all_arithmetic_proofs': False, 'uniform_bound_proved': False, 'RH_proved': False}


def main():
    import check_prime_transfer_058 as CHECK
    if OUT.exists(): raise FileExistsError('preserve any058 scientific run')
    started = time.monotonic(); counts = validate_parent()
    development = sum(check_receipt(json.loads((ROOT/n).read_text())) for n in FILES if n.endswith('_development.json'))
    frozen = {n: (ROOT/n).read_bytes() for n in FILES}
    OUT.mkdir(); (OUT/'source_snapshot').mkdir()
    for n, data in frozen.items(): (OUT/'source_snapshot'/n).write_bytes(data)
    try:
        write(OUT/'protocol.json', {'universe': UNIVERSE, 'max_attenuation_degree': 2,
            'operator_archive_limit': 512, 'proof_selection_limit': 16, 'alphas': ALPHAS,
            'gamma_max_denominator': 64, 'tau': '1/2', 'source_arrays_evaluated': False,
            'previous_goal_turn': 'PROGRESS:057 executed, refuted fixed claims and changed the search input',
            'workers_for_independent_candidates': 3, 'RREF_processes': 1,
            'isomorphic_prime_matrices_repeated': False, 'aggregate_memory_limit_bytes': 16*1024**3,
            'seconds_per_module': 7200, 'hashes_used': False,
            'prior_frozen_source_counts': counts, 'new_frozen_source_count': len(FILES),
            'old_suites_or_studies_replayed': False})
        am = ALG.Meter(cap=100_000_000_000, seconds=7200)
        grammar = ALG.grammar(UNIVERSE, am); atoms = grammar['atoms']
        write(OUT/'grammar.json', grammar)
        emit('transfer_grammar_frozen', atoms=len(atoms), universe=UNIVERSE)
        discovered = ALG.discover(UNIVERSE, atoms, am)
        write(OUT/'inferred_relations.json', discovered)
        emit('transfer_identities_inferred', rank=discovered['rank'], relations=len(discovered['relations']))
        sm = SEARCH.Meter(cap=100_000_000_000, seconds=7200)
        cm = CHECK.Meter(cap=100_000_000_000, seconds=7200)
        basis_checks = [CHECK.verify_identity(basis_request(UNIVERSE, atoms, r), cm) for r in discovered['relations']]
        write(OUT/'basis_verification.json', {'rows': basis_checks, 'universal_identities_not_signed_bounds': True})
        proposed = SEARCH.promote(atoms, discovered['relations'], sm, 512)
        write(OUT/'proposed_operators.json', proposed)
        compiled = []
        with mp.get_context('fork').Pool(3, initializer=worker_init, initargs=(UNIVERSE, atoms)) as pool:
            for row in pool.imap_unordered(worker_task, proposed['rows'], chunksize=4):
                compiled.append(row)
                if len(compiled) % 64 == 0: emit('transfer_proof_progress', completed=len(compiled), total=len(proposed['rows']))
        compiled.sort(key=lambda r: r['candidate']['id'])
        write(OUT/'proof_candidates.json', {'rows': compiled, 'uniform_full_source_bound_proved': False})
        obstruction = target_obstruction(UNIVERSE, [2, 3], sm, cm)
        write(OUT/'target_obstruction.json', obstruction)
        selected = SEARCH.select_for_proof(compiled, 16)
        write(OUT/'selected.json', {'ids': [r['candidate']['id'] for r in selected],
            'reason': 'reviewable exchange family and distinct unclassified source/forcing structures',
            'numerical_constants_used': False})
        grid = SEARCH.parameter_grid(64); endpoints = []
        for r in selected:
            for alpha in ALPHAS:
                gamma = SEARCH.select_endpoint_gamma(r['source_order'], alpha, grid, sm)
                if gamma is None: continue
                program = SEARCH.endpoint_program(r['current_operator'], r['source_order'], alpha, gamma)
                checked = CHECK.verify_endpoint_bound(program['request'], program, cm)
                endpoints.append({'id': r['candidate']['id'], 'program': program, 'verification': checked})
        write(OUT/'endpoint_programs.json', {'rows': endpoints, 'uniform_full_source_bound_proved': False})
        write(OUT/'next_search_input.json', {'schema': 'prime-transfer-forcing-feedback-v1',
            'prior_failures_and_ranking_evidence': str((PRIOR.OUT/'mechanism_feedback.json').relative_to(ROOT)),
            'operators': [{k: r[k] for k in ('candidate', 'current_operator', 'interpretation', 'proof_attempt')} for r in selected],
            'target_sector_obstruction': obstruction,
            'paid': ['complete valuation identities', 'current-only source orders and endpoint bounds'],
            'unpaid': 'joined ordinary-mu/cofactor floor forcing of the complete weighted middle source',
            'small_step_contraction_without_controlled_forcing_is_not_a_bound': True,
            'weighted_exchange_RH_bridge': 'separate analytic review, conditional on a complete uniform source bound',
            'finite_prime_padding_alone_does_not_close_forcing': True,
            'uniform_full_source_bound_proved': False, 'RH_proved': False})
        validate_parent()
        if any((ROOT/n).read_bytes() != data for n, data in frozen.items()): raise ValueError('preserve frozen058 bytes')
        report = {'status': 'EXACT_OPERATOR_ARGUMENTS_INFERRED_ARITHMETIC_FORCING_OPEN',
            'atoms': len(atoms), 'rank': discovered['rank'], 'basis_relations': len(basis_checks),
            'proposals': {k: proposed[k] for k in ('pair_attempts','distinct_proposals','distinct_current_operators','archive_truncated')},
            'checked_operator_programs': len(compiled),
            'interpretation_counts': dict(Counter(r['interpretation']['family'] for r in compiled)),
            'source_order_counts': dict(Counter(str(r['source_order']['order']) for r in compiled)),
            'literal_closed_self_recurrences': sum(r['proof_attempt']['literal_self_state_recurrence'] for r in compiled),
            'selected_ids': [r['candidate']['id'] for r in selected], 'checked_endpoint_programs': len(endpoints),
            'target_sector_obstruction': obstruction['obstruction'],
            'development_operations': development, 'algebra_counts': am.counts(), 'planner_operations': sm.operations,
            'parent_checker_operations': cm.operations,
            'candidate_producer_operations': sum(r['operations']['producer'] for r in compiled),
            'candidate_checker_operations': sum(r['operations']['checker'] for r in compiled),
            'elapsed_seconds': time.monotonic()-started,
            'parent_peak_rss_kib': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'largest_worker_peak_rss_kib': max([0]+[r['worker_peak_rss_kib'] for r in compiled]),
            'source_arrays_evaluated': False, 'hashes_used': False, 'old_suites_or_studies_replayed': False,
            'prior_frozen_source_counts': counts, 'new_frozen_source_count': len(FILES),
            'uniform_full_source_bound_proved': False, 'RH_proved': False, 'RH_refuted': False}
        write(OUT/'report.json', report)
        emit('transfer_search_completed', elapsed_seconds=report['elapsed_seconds'], operators=len(compiled), endpoints=len(endpoints))
        return report
    except BaseException as exc:
        write(OUT/'failure.json', {'type': type(exc).__name__, 'message': str(exc),
            'elapsed_seconds': time.monotonic()-started, 'uniform_full_source_bound_proved': False, 'RH_proved': False})
        raise


if __name__ == '__main__': main()
