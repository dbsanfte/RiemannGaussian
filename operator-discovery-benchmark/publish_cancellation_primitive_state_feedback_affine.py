"""Publish an independently checked exact affine update, without hashing."""
import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'cancellation-arithmetic-results'
RUN = BASE / 'primitive-state-feedback-affine-001'
OUT = BASE / 'publication-024'
NOTE = 'PRIMITIVE_STATE_FEEDBACK_AFFINE_HANDOFF.txt'
FLAGS = dict(global_bound_proved=False, RH_proved=False,
             universal_identity_proved=False, candidate_admitted=False,
             exact_admission=False, infeasibility_proved=False)
STATUSES = dict(independent='AFFINE_UPDATED', redundant='REDUNDANT',
                inconsistent='FORMAL_SYSTEM_INCONSISTENT')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path, cap=8388608):
    path = Path(path)
    require(path.stat().st_size <= cap, 'bounded publication input')
    with path.open('rb') as handle:
        data = handle.read(cap + 1)
    require(len(data) <= cap, 'bounded publication read')
    return json.loads(data)


def write_new(path, value):
    data = json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)
    require(len(data.encode()) <= 1048576, 'bounded publication summary')
    with Path(path).open('x') as handle:
        handle.write(data + '\n')


def checked_outcome(review, affine):
    """Interpret the independent mathematical result without repeating replay."""
    require(review.get('schema') == 'primitive-state-feedback-affine-independent-review-v1',
            'independent exact affine review')
    for name in FLAGS:
        require(review.get(name) is False, 'finite update cannot establish ' + name)
    joint = review.get('joint_work', {})
    require(joint.get('max_work') == 450000000
            and joint.get('total_work_reserve') == 450000000,
            'single joint 450m reservation')
    status = review.get('status')
    require(status in (*STATUSES.values(), 'UNKNOWN'), 'explicit exact update disposition')
    require(review.get('all_passed') is True or
            (status == 'UNKNOWN' and review.get('all_passed') is False
             and isinstance(review.get('resource_failure'), dict)),
            'completed review or explicit bounded audit failure')
    if status == 'UNKNOWN':
        require(review.get('chart_verified') is False
                and review.get('candidate_equations_verified') is False
                and review.get('finite_candidate_feasible') is None,
                'incomplete update authorizes no map or candidate')
        return None
    check = review.get('independent_affine_check')
    require(isinstance(check, dict) and check.get('verified') is True
            and check.get('complete') is True, 'complete independent mathematical replay')
    for name in FLAGS:
        require(check.get(name) is False, 'finite replay cannot establish ' + name)
    for name in ('all_original_rows_replayed', 'projection_dependencies_verified',
                 'feedback_reduction_verified'):
        require(check.get(name) is True, 'required complete arithmetic check: ' + name)
    require(isinstance(affine, dict) and affine.get('complete') is True
            and affine.get('status') == 'complete', 'actual completed affine receipt')
    classification = check.get('classification')
    require(classification in STATUSES and status == STATUSES[classification]
            and affine.get('classification') == classification,
            'independently checked exact classification')
    independent = classification == 'independent'
    inconsistent = classification == 'inconsistent'
    rank = 779 + int(independent)
    augmented_rank = 779 + int(classification != 'redundant')
    free = None if inconsistent else 445 - int(independent)
    require(check.get('old_rank') == 779 and check.get('old_free_count') == 445
            and check.get('new_rank') == affine.get('coefficient_rank') == rank
            and check.get('augmented_rank') == affine.get('augmented_rank') == augmented_rank
            and check.get('new_free_count') == affine.get('free_dimension') == free,
            'coefficient and augmented ranks kept distinct')
    require(check.get('normalized_chart_verified') is (not inconsistent)
            and review.get('chart_verified') is (not inconsistent)
            and affine.get('chart_available') is (not inconsistent),
            'a contradictory system has no usable chart')
    if inconsistent:
        require(check.get('candidate_equations_verified') is False
                and review.get('candidate_equations_verified') is False
                and check.get('finite_candidate_feasible') is None
                and review.get('finite_candidate_feasible') is None
                and affine.get('candidate_original_vector') is None,
                'contradiction supplies no repaired candidate')
    else:
        require(check.get('candidate_equations_verified') is True
                and review.get('candidate_equations_verified') is True,
                'all original and feedback endpoint equations checked')
        diagnostics = affine.get('diagnostics', {})
        require(diagnostics.get('affine_equalities_satisfied') is True,
                'actual exact endpoint satisfies all equations')
        feasible = check.get('finite_candidate_feasible')
        require(type(feasible) is bool
                and review.get('finite_candidate_feasible') is feasible
                and diagnostics.get('all_cones_satisfied') is feasible,
                'equation satisfaction remains distinct from cone feasibility')
    return check


def publish(run=RUN, destination=OUT):
    run, destination = Path(run).resolve(), Path(destination).resolve()
    require(not destination.exists(), 'new publication destination')
    latest = read(BASE / 'latest.json', 65536)
    require(latest.get('publication') == 'publication-023', 'expected predecessor')
    review = read(run / 'independent_verification.json')
    affine_path = run / 'jobs/affine.json'
    affine = read(affine_path) if affine_path.exists() else None
    job_path = run / 'jobs/affine-job.json'
    job = read(job_path, 65536) if job_path.exists() else {}
    check = checked_outcome(review, affine)
    consistent = check is not None and check['normalized_chart_verified']
    report = dict(
        schema=24, title='Exact counterexample constraint incorporated into the affine search space',
        previous_publication='publication-023', seed_origin='publication-021',
        constraint_origin='publication-023/constraint.json',
        run=str(run.relative_to(ROOT)), status=review['status'],
        independent_audit_complete=review['all_passed'],
        independent_mathematical_replay_complete=check is not None,
        independent_resource_failure=review.get('resource_failure'),
        chart_verified=consistent,
        chart_path=str((run / 'jobs/chart.json').relative_to(ROOT)) if consistent else None,
        affine_receipt_path=str(affine_path.relative_to(ROOT)) if affine is not None else None,
        independent_review_path=str((run / 'independent_verification.json').relative_to(ROOT)),
        classification=check['classification'] if check is not None else None,
        old_coefficient_rank=779, old_free_count=445,
        coefficient_rank=check['new_rank'] if check is not None else None,
        augmented_rank=check['augmented_rank'] if check is not None else None,
        free_count=check['new_free_count'] if check is not None else None,
        candidate_equations_verified=review.get('candidate_equations_verified') is True,
        finite_candidate_feasible=review.get('finite_candidate_feasible'),
        chosen_pivot=affine['reduction']['chosen_pivot'] if check is not None else None,
        no_cone_optimization_performed=True, feedback_is_discovery_data=True,
        joint_work=review['joint_work'], tests_passed=review.get('tests_passed'),
        producer_status=job.get('status'), producer_failure=job.get('reason'),
        producer_counts=affine.get('counts') if affine is not None else None,
        producer_cost=job.get('cost'), independent_cost=review.get('cost'),
        remaining_obligations=['finite cone feasibility', 'universal formal nonconstant identity',
                               'uniform scalar bound, initial storage cost, and ordinary-zeta bridge'],
        interpretation='The new row is a necessary formal constraint. The repaired seed is an exact affine diagnostic; satisfying this learned row is not fresh evaluation evidence.',
        scalar_budget_obligation_verified=False, **FLAGS)
    destination.mkdir()
    write_new(destination / 'report.json', report)
    if (ROOT / NOTE).exists():
        (destination / NOTE).write_text((ROOT / NOTE).read_text())
    require(read(BASE / 'latest.json', 65536) == latest, 'no intervening publication')
    pointer = BASE / 'latest-024.tmp'
    write_new(pointer, dict(publication=destination.name, report='report.json',
                            status=review['status'], **FLAGS))
    pointer.replace(BASE / 'latest.json')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    print(json.dumps(publish(), sort_keys=True))
