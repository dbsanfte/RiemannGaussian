"""One immutable symbolic bound-synthesis and common-mode audit."""
import json
from pathlib import Path
import re
import resource
import subprocess
import sys
import time
from prime_bank_candidates import Meter
import core_frame_bounds as P
import check_core_cutoff_frame as FRAME_CHECK
import run_core_cutoff_frame as PRIOR

ROOT = Path(__file__).resolve().parent
PARENT = ROOT/'core-cutoff-frame-results/pilot-001'
OUT = ROOT/'core-frame-bound-results/pilot-001'
INPUT = 'candidate10_cutoff_frame_obligation.json'
TESTS = ['test_core_frame_bounds', 'test_check_core_frame_bounds', 'test_run_core_frame_bounds']
RECEIPTS = ['core_frame_bounds_development.json', 'core_frame_bounds_checker_development.json',
            'core_frame_bounds_runner_development.json']
FILES = ['core_frame_bounds.py', 'check_core_frame_bounds.py', 'run_core_frame_bounds.py',
         'core_frame_bound_protocol.txt', 'prime_bank_candidates.py', INPUT]+[t+'.py' for t in TESTS]+RECEIPTS
PARENT_FILES = ['catalogue.json', 'representations.json', 'selection.json', 'report.json',
                'source_representation_checks.json', 'catalogue_verification.json']
CAP = 300000000


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    with path.open('x') as stream:
        json.dump(value, stream, indent=2, sort_keys=True)
        stream.write('\n')


def verify():
    PRIOR.verify()
    for name in read(OUT/'source_files.json'):
        if (ROOT/name).read_bytes() != (OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('changed frozen source '+name)
    for name in read(OUT/'parent_files.json'):
        if (PARENT/name).read_bytes() != (OUT/'parent_snapshot'/name).read_bytes():
            raise ValueError('changed inherited frame artifact '+name)


def compile_feedback(prior, certificates, representations, source_conditions):
    parents = prior['generated_bound_constructions']
    identifiers = [p['candidate_id'] for p in parents]
    if len(set(identifiers)) != len(identifiers):
        raise ValueError('unique inherited selected constructions')
    by_id = {c['id']: c for c in certificates}
    sources = {c['candidate_id']: c for c in source_conditions}
    if set(sources) != set(identifiers) or len(sources) != len(source_conditions):
        raise ValueError('every selected actual arithmetic condition exactly once')
    routes = set(parents[0]['source_binding_ids'])
    for parent in parents:
        if len(set(parent['source_binding_ids'])) != len(parent['source_binding_ids']) or set(parent['source_binding_ids']) != routes:
            raise ValueError('every original channel and transport route retained')
    if len({r['geometry_id'] for r in representations}) != len(representations):
        raise ValueError('unique complete source representations')
    references = []
    for g in representations:
        bindings = [b['parent_obligation_id'] for b in g['bindings']]
        if set(bindings) != routes or len(bindings) != len(routes):
            raise ValueError('every inherited representation binding retained')
        references.append(dict(geometry_id=g['geometry_id'],
            file='core-cutoff-frame-results/pilot-001/representations.json',
            all_source_binding_ids=bindings, common_horizon='N=4X-1', exact_transport_error_retained=True))
    result = []
    for parent in parents:
        ident = parent['candidate_id']
        certificate = by_id[ident]
        source = sources[ident]
        if source['status'] != 'open' or source['arithmetic_inequality_proved']:
            raise ValueError('algebraic substitution is not the required uniform arithmetic estimate')
        item = P.feedback(parent, certificate, references)
        item['actual_moment_condition'] = source
        result.append(item)
    return result


def main():
    import check_core_frame_bounds as CHECK
    started = time.monotonic()
    _, hard = resource.getrlimit(resource.RLIMIT_AS)
    resource.setrlimit(resource.RLIMIT_AS, (4*1024**3, hard))
    PRIOR.verify()
    if (ROOT/INPUT).read_bytes() != (PARENT/'publication-001/next_search_input.json').read_bytes():
        raise ValueError('exact published current frame obligation')
    if read(PARENT/'report.json')['status'] != 'CUTOFF_FRAME_CONSTRUCTIONS_VERIFIED_WITH_OPEN_ARITHMETIC_BOUNDS':
        raise ValueError('verified prior frame construction search')
    prior = read(ROOT/INPUT)
    receipts = [read(ROOT/n) for n in RECEIPTS]
    if any(r['runs'][-1]['returncode'] or r['operations'] != sum(v['operations'] for v in r['runs']) for r in receipts):
        raise ValueError('complete passed owned development receipts')
    if OUT.exists():
        raise FileExistsError('preserve immutable study and terminal outcomes')
    OUT.mkdir(parents=True)
    (OUT/'source_snapshot').mkdir()
    (OUT/'parent_snapshot').mkdir()
    for name in FILES:
        (OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    for name in PARENT_FILES:
        (OUT/'parent_snapshot'/name).write_bytes((PARENT/name).read_bytes())
    write(OUT/'source_files.json', FILES)
    write(OUT/'parent_files.json', PARENT_FILES)
    write(OUT/'protocol.json', dict(schema='core-frame-bound-run-v1', input=INPUT,
        grammar='exact multivariate quotient first; generated Lagrange square witness otherwise',
        monomial_order='graded lexicographic d0..dm-1',
        arithmetic_goal='S>0 and S>=c*(1+log2X)^(-q)*B for fixed c>0,q>=0 at every dyadic X>=X0',
        scope='conditional recovery theorem, explicit actual moment inequality, and common-mode equivalence audit',
        supplied=['polynomial arithmetic', 'Lagrange/Cauchy identity', 'abstract unit-vector countermodel language'],
        generated=['quadratic bound numerator', 'exact quotient or SOS proof', 'actual moment condition', 'retained common-mode coefficient'],
        actual_source_evaluations=0, numerical_candidate_scores=0, model_calls_in_search=0,
        inclusive_operation_cap=CAP, runtime_limit_seconds=1800, memory_limit_bytes=4*1024**3,
        hashes=False, whole_signed_bound_proved=False, RH_proved=False))
    meter = Meter(CAP, 1800)
    meter.charge(2000000)
    test_start = time.monotonic()
    tests = subprocess.run([sys.executable, '-B', '-m', 'unittest', *TESTS], cwd=ROOT,
        capture_output=True, text=True, timeout=300)
    test_ops = sum(map(int, re.findall(r'operations=(\d+)', tests.stdout)))
    write(OUT/'frozen_tests.json', dict(returncode=tests.returncode, stdout=tests.stdout, stderr=tests.stderr,
        operations=test_ops, elapsed_seconds=time.monotonic()-test_start))
    if tests.returncode:
        raise RuntimeError('frozen independent suites failed')
    catalogue = read(OUT/'parent_snapshot/catalogue.json')
    representations = read(OUT/'parent_snapshot/representations.json')
    catalogue_check = FRAME_CHECK.check_catalogue(catalogue, meter)
    result = P.synthesize(catalogue, meter)
    checked = CHECK.verify(catalogue, result, meter)
    write(OUT/'certificates.json', result)
    write(OUT/'verification.json', dict(parent_catalogue=catalogue_check, bound_certificates=checked))
    selected_ids = read(OUT/'parent_snapshot/selection.json')['selected_ids']
    if sorted(p['candidate_id'] for p in prior['generated_bound_constructions']) != selected_ids:
        raise ValueError('unchanged prior independently selected constructions')
    selected = [c for c in result['certificates'] if c['id'] in selected_ids]
    conditions = P.source_conditions(representations, selected, meter)
    condition_check = CHECK.verify_source_conditions(representations, selected, conditions, meter)
    write(OUT/'actual_moment_conditions.json', conditions)
    write(OUT/'actual_moment_condition_verification.json', condition_check)
    feedback = compile_feedback(prior, result['certificates'], representations, conditions)
    next_input = dict(schema='core-frame-bound-feedback-v1', status='open', parent_obligation=prior,
        generated_arithmetic_bound_obligations=feedback,
        catalogue_certificate_file='core-frame-bound-results/pilot-001/certificates.json',
        search_policy=dict(equivalent_algebraic_rewrite_signed_control_credit=0,
            recovery_condition_and_signed_residual_must_be_separate=True,
            weak_frame_facts_cannot_close_residual=True,
            source_specific_unknown_lemmas_remain_valid_search_targets=True),
        next_priority='Search a source-specific arithmetic proof of the explicit moment inequality and a genuinely independent bound for the complete residual; cutoff identities and conditioned recovery alone cannot supply the latter',
        original_target_and_all_corrections_retained=True, new_uniform_arithmetic_estimates=0,
        detector_synthesizes_sufficient_arithmetic_estimates=True, detector_has_general_analytic_prover=False,
        all_scale_signed_control_proved=False, whole_signed_bound_proved=False, RH_proved=False)
    write(OUT/'next_search_input.json', next_input)
    total = meter.operations+test_ops+sum(r['operations'] for r in receipts)
    if total > CAP:
        raise OverflowError('inclusive symbolic study work limit')
    verify()
    report = dict(status='FRAME_RECOVERY_BOUND_REDUCTIONS_AND_COMMON_MODE_OBSTRUCTION_VERIFIED',
        **result['statistics'], selected_ids=selected_ids,
        selected_branches=[dict(id=c['id'], branch=c['branch'], numerator_terms=len(c['bound_numerator'])) for c in selected],
        actual_moment_conditions=len(conditions), shared_actual_moment_variables=len(conditions[0]['variables']),
        retained_source_representation_bindings=sum(len(g['bindings']) for g in representations),
        common_mode_countermodels=len(result['certificates']), new_uniform_arithmetic_estimates=0,
        source_evaluations=0, model_calls_in_search=0, numerical_scores_used=False,
        main_operations=meter.operations, inclusive_operations=total, elapsed_seconds=time.monotonic()-started,
        peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        whole_signed_bound_proved=False, RH_proved=False)
    write(OUT/'report.json', report)
    print(json.dumps(report), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        if OUT.exists() and not (OUT/'report.json').exists() and not (OUT/'terminal_failure.json').exists():
            write(OUT/'terminal_failure.json', dict(status='incomplete', error_type=type(error).__name__,
                error=str(error), whole_signed_bound_proved=False, RH_proved=False))
        raise
