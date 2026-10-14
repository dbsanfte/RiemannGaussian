"""Independent prospective NEW086 audit helpers; no scientific evaluations.

The saved-artifact binding layer will be added once the runner schema exists.
These helpers deliberately do not import a proposer, source model, or solver.
"""
from fractions import Fraction as Q
import ast
import copy
import json
import os
from pathlib import Path
import tempfile
import time
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent
RECEIPT = ROOT / 'mobius_arithmetic_bank_audit_086_development.jsonl'


class AuditError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise AuditError(message)


def above_power_target(lower, constant, u, j=31, bit_budget=100000):
    """Exact strict lower > C*u**(1+1/j), including zero/sign cases."""
    require(type(u) is int and u >= 1, 'positive integer parent')
    require(type(j) is int and 1 <= j <= 10000, 'positive bounded exponent index')
    p, c = Q(lower), Q(constant)
    require(c >= 0, 'nonnegative frozen growth constant')
    if p <= 0:
        return False
    if c == 0:
        return True
    ratio = p / c
    work_bits = j * (ratio.numerator.bit_length() + ratio.denominator.bit_length()) + (j + 1) * u.bit_length()
    require(work_bits <= bit_budget, 'prospective exact exponent bit budget')
    return ratio.numerator ** j > ratio.denominator ** j * u ** (j + 1)


def exact_rank_gain(old_columns, new_column, signs):
    """Check the separating witness proof, without numerical rank tolerances."""
    require(type(signs) is list and all(type(s) is int and s in (-1, 1) for s in signs), 'complete Boolean signs')
    require(bool(signs) and signs[0] == 1, 'known anchor exactly +1')
    require(type(old_columns) is list and type(new_column) is list, 'exact columns')
    require(len(new_column) == len(signs), 'complete new column')
    for col in old_columns:
        require(type(col) is list and len(col) == len(signs), 'complete old column')
        require(sum((Q(v) * s for v, s in zip(col, signs)), Q(0)) == 0, 'old bank compatibility')
    dot = sum((Q(v) * s for v, s in zip(new_column, signs)), Q(0))
    require(dot != 0, 'strict new information requires nonzero violation')
    return dict(new_identity_dot=str(dot), finite_geometry_rank_gain=True, uniform_rank_gain_proved=False)


def elapsed_guard(started, now=None, limit=7200):
    elapsed = (time.monotonic() if now is None else now) - started
    require(0 <= elapsed <= limit, 'per-stage cumulative elapsed budget')
    return elapsed


def development_tests():
    tests = []
    def test(name, action):
        action()
        tests.append(dict(name=name, status='PASS'))
    def rejects(action):
        try:
            action()
        except AuditError:
            return
        raise AssertionError('expected audit rejection')
    test('strict_target_equality_and_neighbors', lambda: (
        require(not above_power_target('16', '1', 4, 1), 'equality is not violation'),
        require(above_power_target('16001/1000', '1', 4, 1), 'strict positive gap'),
        require(not above_power_target('15999/1000', '1', 4, 1), 'strict negative gap')))
    test('target_zero_and_sign_cases', lambda: (
        require(above_power_target('1/100000', '0', 9), 'positive against zero'),
        require(not above_power_target('-1', '0', 9), 'negative lower'),
        rejects(lambda: above_power_target('1', '-1', 9))))
    test('exact_rational_separation_rank_gain', lambda: require(
        exact_rank_gain([['1/3', '1/3']], ['1/7', '0'], [1, -1])['new_identity_dot'] == '1/7', 'exact separator'))
    test('old_bank_and_new_zero_spoilage', lambda: (
        rejects(lambda: exact_rank_gain([['1', '0']], ['1', '0'], [1, -1])),
        rejects(lambda: exact_rank_gain([], ['1', '1'], [1, -1])),
        rejects(lambda: exact_rank_gain([], ['1'], [True]))))
    test('prospective_exponent_resource_fault', lambda: rejects(lambda: above_power_target('1000001/999999', '1', 3475, bit_budget=1)))
    test('serial_elapsed_fault_propagates', lambda: (
        require(elapsed_guard(5, now=10, limit=6) == 5, 'finite elapsed'),
        rejects(lambda: elapsed_guard(5, now=12, limit=6))))
    return tests


def runner_prospective_tests(only=None):
    """Metadata and fault integration only; never draw the future parent."""
    for key in ('OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'OMP_NUM_THREADS'):
        os.environ[key] = '1'
    import run_mobius_arithmetic_bank_086 as run
    results = []
    def test(name, action):
        if only is not None and name not in only:
            return
        try:
            details = action()
            results.append(dict(name=name, status='PASS', details=details))
        except Exception as exc:
            results.append(dict(name=name, status='FAIL', error_type=type(exc).__name__, reason=str(exc)))

    def metadata():
        spec = run.SPEC
        require(spec['training_parent'] == 3475 and spec['modes'] == ['divisor', 'union'], 'prospective training/arms')
        require(spec['maximum_additions'] == 4 and spec['maximum_bank_size'] <= 16, 'bounded bank expansion')
        require(spec['validation_bands'] == [[3600, 4095]] and spec['fresh_parents_per_band'] == 1, 'fresh band metadata only')
        require(spec['prospective_draw_values_seen_in_preflight'] is False, 'no precomputed draw')
        require(spec['shared_initial_witness'] and not spec['selection_uses_upper_results'], 'shared initial/lower-only enrichment')
        require(spec['workers'] == 3 and spec['native_threads'] == 1 and spec['max_aggregate_bytes'] == 16*1024**3, 'resource metadata')
        require(spec['trigger_j'] == 31 and Q(spec['trigger_constant']) == 1, 'unchanged residual target')
        old = run.read(run.PRIOR.OUT/'frozen_candidates.json')['candidates']
        require(len(old) == 8 and len({c['id'] for c in old}) == 8, 'complete fixed roster')
        for c in old:
            require(len(c['banks']['adaptive']) == 8, 'initial adaptive bank exactly eight')
            require(c['program']['prime_anchor'] is True, 'complete known-prime anchor')
            require({h['j'] for h in c['calibrated_growth_hypotheses']} == {1,3,7,15,31}, 'frozen growth roster')
            require(all(Q(h['constant']) == 1 for h in c['calibrated_growth_hypotheses']), 'unchanged growth constants')
        missing = [name for name in run.FILES if not (run.ROOT/name).is_file()]
        require(len(set(run.FILES)) == len(run.FILES) and not missing, 'complete lexical source roster; missing='+repr(missing))
        return dict(operators=8, initial_rows_per_operator=8, future_draw_not_computed=True,
                    scientific_program_values_not_evaluated=True, source_files=len(run.FILES))

    def lexical_order():
        tree = ast.parse((run.ROOT/'run_mobius_arithmetic_bank_086.py').read_text())
        main = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'main')
        calls = sorted(((n.lineno, n) for n in ast.walk(main) if isinstance(n, ast.Call)), key=lambda pair:pair[0])
        def line_for_literal(text):
            return min(line for line,n in calls if any(isinstance(a,ast.Constant) and a.value == text for a in ast.walk(n)))
        freeze = line_for_literal('frozen_candidates.json')
        random_start = min(line for line,n in calls if isinstance(n.func,ast.Attribute) and n.func.attr == 'Random')
        first_upper = min(line for line,n in calls if isinstance(n.func,ast.Name) and n.func.id == 'upper_roster')
        require(freeze < random_start and freeze < first_upper, 'banks freeze before upper roster and RNG')
        require('validation_draw.json' in (run.ROOT/'run_mobius_arithmetic_bank_086.py').read_text(), 'draw history retained')
        return dict(freeze_line=freeze, first_upper_roster_line=first_upper, RNG_line=random_start,
                    RNG_executed=False)

    candidate = dict(id='synthetic_audit', source_id='synthetic', family_id='fault_only',
                     program={}, outer_certificate={}, initial_bank=[],
                     banks={'divisor':[], 'union':[]}, calibrated_growth_hypotheses=[])
    def task(stage):
        return dict(id='synthetic_'+stage, candidate=copy.deepcopy(candidate), operator_index=0,
                    mode='divisor', u=59, stage=stage, bank=[])

    def fresh_lower_after_upper_fault():
        with tempfile.TemporaryDirectory(prefix='mobius086audit_') as directory:
            with patch.object(run,'OUT',Path(directory)), \
                 patch.object(run.UPPER,'build_model',side_effect=RuntimeError('synthetic upper fault')), \
                 patch.object(run,'lower_search',return_value=dict(id='synthetic_validation',status='NO_EXACT_COMPATIBLE_WITNESS_FOUND')) as lower:
                outcome = run.upper_task(task('validation'))
                require(lower.call_count == 1, 'every fresh row must attempt lower even when upper fails')
                saved = run.read(Path(directory)/('bound_'+outcome['id']+'.json'))
                require(saved['status'] == 'TASK_FAILED', 'upper failure retained')
                return dict(upper_failure_retained=True, fresh_lower_attempted=True, source_geometry_built=False)

    def unavailable_incumbent_keeps_final_upper():
        t = task('training');t['incumbent_file'] = 'failed_initial.json'
        with tempfile.TemporaryDirectory(prefix='mobius086audit_') as directory:
            path = Path(directory)
            (path/'failed_initial.json').write_text(json.dumps(dict(candidate_id=candidate['id'],u=59,status='TASK_FAILED',bank=[])))
            proposal = dict(status='EXACT_MIXED_ZERO_SQUARE_PROPOSAL',certificate={'price':'3/7'},selected_attempt='SYNTHETIC_VALID')
            with patch.object(run,'OUT',path), patch.object(run.UPPER,'build_model',return_value={}), \
                 patch.object(run.BANK,'vectors',return_value=(None,{})), \
                 patch.object(run.UPPER,'solve_model',return_value=copy.deepcopy(proposal)), \
                 patch.object(run.CHECK,'verify_upper',return_value={'status':'VERIFIED_FINITE_ARITHMETIC_BANK_MIXED_UPPER_BOUND'}):
                outcome = run.upper_task(t)
                require(outcome['status'] == 'EXACT_MIXED_ZERO_SQUARE_PROPOSAL', 'failed initial upper must not discard final certificate')
                saved = run.read(path/('bound_'+outcome['id']+'.json'))
                require(saved['certificate']['price'] == '3/7', 'new exact proposal retained')
                return dict(unavailable_initial_incumbent_nonfatal=True, source_geometry_built=False)

    def exact_boolean_inconsistency_is_fatal():
        with tempfile.TemporaryDirectory(prefix='mobius086audit_') as directory:
            with patch.object(run,'OUT',Path(directory)), \
                 patch.object(run.UPPER,'build_model',return_value={}), \
                 patch.object(run.LOWER,'solve_model',return_value={'status':'EXACT_BOOLEAN_BANK_INFEASIBLE','certificate':None}):
                row = run.lower_search(candidate,[],59,'inconsistency_fault',17)
                require(row['status']=='ARITHMETIC_IDENTITY_IMPLEMENTATION_INCONSISTENCY', 'exact infeasibility is an implementation inconsistency')
                require(not run.admitted_lower(row), 'inconsistency cannot trigger extension')
                return dict(inconsistency_not_scientific_infeasibility=True)

    def exact_trigger_matches_independent_rule():
        count = 0
        for u in (1,4,59):
            for j in (1,3,31):
                for p in ('-1','0','1/7','1','16','65537/16'):
                    require(run.target_excluded(p,u,j,'1')==above_power_target(p,'1',u,j), 'independent exact trigger agreement')
                    count += 1
        try:
            run.target_excluded('2',59,1000000,'1')
        except run.BANK.B.ResourceLimit:
            return dict(exact_cases=count, prospective_power_resource_fault_rejected=True)
        raise AuditError('runner must reject power work before huge exponent construction')

    def tiny_arithmetic_roundtrip():
        # Complete tiny source geometry; signs are literal artificial labels,
        # never a Mobius-value oracle or an old scientific data replay.
        p = dict(schema='coupled-divisor-completion-v1',
                 kernel=[dict(divisor=d,weight=w) for d,w in [(4,'-1'),(5,'1'),(8,'1'),(10,'-1')]],
                 memory=2,rays=[dict(a=['1','1'],weight='1/4')],drift_multiplier='3/2',
                 coupled_terms=[dict(cut=dict(scale='1',n_exponent='1',u_exponent='0',complement=c,unit_balance=True),
                                     weight=dict(kind='product',i=0,j=0,arithmetic='all'),theta='5/2') for c in (False,True)],
                 gram_weights=['0','0','0'],prime_anchor=True)
        outer = run.UPPER.SQUARE.O.synthesize(p)['certificate']
        model = run.UPPER.build_model(p,59)
        n = model['price_dimension']
        require(n==4, 'tiny complete anchor and three composite labels')
        signs = [1,-1,1,1]
        lower = run.LOWER.certificate(model,[],signs)
        admitted = run.CHECK.verify_lower(p,59,outer,[],lower)
        require(admitted['status']=='VERIFIED_FINITE_ARITHMETIC_BANK_LOWER_BOUND', 'tiny full lower admission')
        added = dict(kind='prime_pair',cut_on='prime',cut=dict(scale='2/59',u_exponent='1',complement=False),weight=dict(kind='one'))
        gain = run.CHECK.verify_extension(p,59,outer,[],lower,added)
        require(gain['status']=='VERIFIED_FINITE_ARITHMETIC_BANK_INFORMATION_GAIN', 'tiny prime-cofactor separation independently admitted')
        V,meta = run.BANK.vectors(model,[added])
        independent = run.CHECK.build_identities(run.CHECK.C.build_model(p,59),[added])
        require([[Q(str(V[i,0]))] for i in range(n)]==independent['vectors'], 'complete numerator/anchor binding')
        cert,diag = run.UPPER.certificate(model,V,[['0'] for _ in range(n)],1,[[] for _ in range(n)])
        upper = run.CHECK.verify_upper(p,59,outer,[added],cert)
        require(upper['status']=='VERIFIED_FINITE_ARITHMETIC_BANK_MIXED_UPPER_BOUND', 'tiny full upper admission')
        bad = copy.deepcopy(lower);bad['lower_bound']=str(Q(bad['lower_bound'])+1)
        require(run.CHECK.verify_lower(p,59,outer,[],bad)['status']!='VERIFIED_FINITE_ARITHMETIC_BANK_LOWER_BOUND', 'full value spoilage rejected')
        return dict(parent=59,effective_dimension=n,full_lower_and_upper_and_information_gain_admitted=True,
                    actual_unknown_signs_queried=False, prime_pair_count=meta['prime_pair_counts'][0],
                    source_model_evaluated_at_tiny_development_geometry=True)

    def final_search_failure_keeps_initial_upper():
        t = task('training');t['incumbent_file'] = 'initial.json'
        inherited = dict(status='EXACT_EMBEDDED_INCUMBENT',source_file='initial.json',
                         certificate={'price':'3/7'},admission={'status':'VERIFIED_FINITE_ARITHMETIC_BANK_MIXED_UPPER_BOUND'},
                         exact_zero_partner_embedding=True)
        with tempfile.TemporaryDirectory(prefix='mobius086audit_') as directory:
            with patch.object(run,'OUT',Path(directory)), patch.object(run.UPPER,'build_model',side_effect=RuntimeError('synthetic final search failure')), \
                 patch.object(run,'embedded_incumbent',return_value=inherited), \
                 patch.object(run.CHECK,'verify_upper',return_value={'status':'VERIFIED_FINITE_ARITHMETIC_BANK_MIXED_UPPER_BOUND'}):
                outcome = run.upper_task(t)
                saved = run.read(Path(directory)/('bound_'+outcome['id']+'.json'))
                require(saved['status']=='EXACT_MIXED_ZERO_SQUARE_PROPOSAL' and saved['certificate']['price']=='3/7', 'admitted initial upper retained after final search fails')
                require('search_failure' in saved, 'failed new search retained alongside fallback')
                return dict(initial_exact_bound_retained=True, failed_search_preserved=True, source_geometry_built=False)

    def serial_watchdog_fault_blocks_science():
        with tempfile.TemporaryDirectory(prefix='mobius086audit_') as directory:
            root = Path(directory);(root/'synthetic_source.txt').write_text('synthetic fixture\n')
            out = root/'out'
            with patch.object(run,'ROOT',root),patch.object(run,'OUT',out),patch.object(run,'FILES',['synthetic_source.txt']), \
                 patch.object(run,'validate_parent',return_value=[686]), \
                 patch.object(run.POOL,'stage_check',side_effect=[None,TimeoutError('synthetic serial watchdog')]) as guard, \
                 patch.object(run.POOL,'pool_tasks',side_effect=AssertionError('science must not run')) as pool, \
                 patch.object(run.random,'Random',side_effect=AssertionError('future draw must not run')) as rng:
                try:
                    run.main()
                except TimeoutError as exc:
                    require('synthetic serial watchdog' in str(exc), 'watchdog propagates')
                else:
                    raise AuditError('serial watchdog swallowed')
                require(guard.call_count==2 and pool.call_count==0 and rng.call_count==0, 'serial guard before science and draw')
                require((out/'source_snapshot'/'synthetic_source.txt').read_text()=='synthetic fixture\n', 'source-copy step covered by guard')
                return dict(serial_guard_after_source_write=True, scientific_workers_started=False, future_draw_executed=False)

    test('runner_fixed_roster_and_metadata_without_future_draw', metadata)
    test('lexical_bank_freeze_before_upper_and_random_draw', lexical_order)
    test('fresh_lower_attempt_survives_upper_resource_or_solver_fault', fresh_lower_after_upper_fault)
    test('unavailable_initial_incumbent_preserves_final_proposal', unavailable_incumbent_keeps_final_upper)
    test('exact_boolean_contradiction_is_implementation_fault', exact_boolean_inconsistency_is_fatal)
    test('runner_trigger_exact_comparison_and_prospective_work_gate', exact_trigger_matches_independent_rule)
    test('tiny_complete_prime_cofactor_extension_upper_lower_roundtrip', tiny_arithmetic_roundtrip)
    test('failed_final_search_retains_checked_initial_incumbent', final_search_failure_keeps_initial_upper)
    test('serial_watchdog_after_snapshot_propagates_before_science', serial_watchdog_fault_blocks_science)
    return results


if __name__ == '__main__':
    import sys
    started = time.monotonic()
    only = set(sys.argv[2:]) if len(sys.argv)>1 and sys.argv[1]=='--only' else None
    receipt = dict(stage='prospective_pure_invariant_helpers' if only is None else 'affected_followup_only', tests=development_tests() if only is None else [],
                   old_science_replayed=False, unknown_Mobius_values_used=False,
                   scientific_geometry_evaluated=False, producer_imported=False)
    if (ROOT/'run_mobius_arithmetic_bank_086.py').is_file():
        receipt['runner_tests'] = runner_prospective_tests(only)
        receipt['producer_imported'] = True
        receipt['tiny_development_geometry_evaluated'] = True
    receipt.update(status='PASS' if all(t['status']=='PASS' for t in receipt.get('runner_tests',[])) else 'FAIL', elapsed_seconds=time.monotonic()-started)
    with RECEIPT.open('a') as stream:
        stream.write(json.dumps(receipt, sort_keys=True)+'\n')
    print(json.dumps(receipt, sort_keys=True))
