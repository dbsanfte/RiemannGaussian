"""Publish a checked cone-search endpoint on the learned affine chart."""
import argparse
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'cancellation-arithmetic-results'
RUN = BASE / 'primitive-state-backtracking-cone-search-001'
OUT = BASE / 'publication-026'
NOTE = 'PRIMITIVE_STATE_BACKTRACKING_CONE_SEARCH_HANDOFF.txt'
FLAGS = dict(global_bound_proved=False, RH_proved=False,
             universal_identity_proved=False, candidate_admitted=False,
             exact_admission=False, infeasibility_proved=False)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path, cap=16777216):
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


def display_number(record):
    """A display-only float; the independently checked export is retained too."""
    if record is None:
        return None
    require(type(record) is list and len(record) == 3, 'bounded numerical export')
    sign, mantissa, exponent = record
    require(type(sign) is int and sign in (0, 1) and type(mantissa) is str
            and 0 < len(mantissa) <= 68
            and all(c in '0123456789abcdef' for c in mantissa)
            and type(exponent) is int and abs(exponent) <= 4096,
            'bounded numerical display input')
    try:
        value = math.ldexp((-1 if sign else 1) * int(mantissa, 16), exponent)
    except OverflowError:
        return None
    return value if math.isfinite(value) else None


def checked_outcome(review, proposal, endpoint):
    require(review.get('schema') == 'primitive-state-backtracking-cone-search-independent-review-v1',
            'independent constrained cone-search review')
    for name in FLAGS:
        require(review.get(name) is False, 'finite search cannot establish ' + name)
    joint = review.get('joint_work', {})
    require(joint.get('max_work') == 450000000
            and joint.get('total_work_reserve') == 450000000,
            'one complete joint work reservation')
    status = review.get('status')
    require(status in ('ENDPOINT_CHECKED', 'UNKNOWN'), 'explicit finite endpoint disposition')
    require(review.get('all_passed') is True or
            (status == 'UNKNOWN' and review.get('all_passed') is False
             and isinstance(review.get('resource_failure'), dict)),
            'completed review or bounded audit failure')
    if status == 'UNKNOWN':
        require(review.get('endpoint_verified') is False
                and review.get('candidate_equations_verified') is False
                and review.get('finite_candidate_feasible') is None,
                'partial search cannot admit an endpoint')
        return None
    check = review.get('independent_search_check')
    require(isinstance(check, dict) and check.get('verified') is True
            and check.get('complete') is True, 'complete independent endpoint review')
    for name in FLAGS:
        require(check.get(name) is False, 'finite endpoint cannot establish ' + name)
    for name in ('endpoint_verified', 'candidate_equations_verified', 'feedback_row_verified',
                 'chart_used_without_old_tape_replay', 'trace_exports_checked'):
        require(check.get(name) is True, 'required independent check: ' + name)
    require(check.get('full_original_rows_checked') == 5641,
            'all original equations checked')
    require(review.get('endpoint_verified') is True
            and review.get('candidate_equations_verified') is True,
            'complete endpoint committed by whole-run review')
    require(type(check.get('finite_candidate_feasible')) is bool
            and review.get('finite_candidate_feasible') is check['finite_candidate_feasible'],
            'separate exact finite cone result')
    require(isinstance(proposal, dict) and proposal.get('complete') is True
            and isinstance(endpoint, dict) and endpoint.get('complete') is True,
            'actual complete proposal and exact endpoint retained')
    require(type(endpoint.get('candidate_original_vector')) is list
            and len(endpoint['candidate_original_vector']) == 1957,
            'all original endpoint coordinates present')
    require(type(check.get('accepted_iterations')) is int
            and 0 <= check['accepted_iterations'] <= 128,
            'bounded complete iteration trace')
    return check


def publish(run=RUN, destination=OUT):
    run, destination = Path(run).resolve(), Path(destination).resolve()
    require(not destination.exists(), 'new publication destination')
    latest = read(BASE / 'latest.json', 65536)
    require(latest.get('publication') == 'publication-025', 'expected predecessor')
    review = read(run / 'independent_verification.json')
    artifacts = {}
    for name, cap in [('map', 8388608), ('proposal', 33554432),
                      ('endpoint', 2097152), ('search-job', 65536)]:
        path = run / 'jobs' / (name + '.json')
        artifacts[name] = read(path, cap) if path.exists() else None
    proposal, endpoint = artifacts['proposal'], artifacts['endpoint']
    job = artifacts['search-job'] or {}
    check = checked_outcome(review, proposal, endpoint)
    report = dict(
        schema=26, title='Extended backtracking from a verified cone-search endpoint',
        previous_publication='publication-025', seed_origin='publication-025',
        constraint_origin='publication-023/constraint.json',
        run=str(run.relative_to(ROOT)), status=review['status'],
        coefficient_rank=780, free_count=444,
        endpoint_verified=check is not None,
        candidate_equations_verified=review.get('candidate_equations_verified') is True,
        finite_candidate_feasible=review.get('finite_candidate_feasible'),
        independent_audit_complete=review['all_passed'],
        independent_resource_failure=review.get('resource_failure'),
        independent_review_path=str((run / 'independent_verification.json').relative_to(ROOT)),
        artifact_paths={name: str((run / 'jobs' / (name + '.json')).relative_to(ROOT))
                        for name, value in artifacts.items() if value is not None},
        chart_reused_without_old_elimination=True,
        saved_positive_scales_reused=True, new_column_norm_responses=0,
        normalizers_reused_from='publication-025', exact_affine_center_origin='publication-024',
        maximum_backtracking_trials=12, initial_step_rule='half the final rejected publication025 trial',
        numerical_norms_certified=False, numerical_gradients_certified=False,
        numerical_optimality_certified=False, feedback_is_discovery_data=True,
        negative_scalar_count=(check.get('endpoint_check') or {}).get('negative_scalar_count') if check is not None else None,
        PSD_failures=(check.get('endpoint_check') or {}).get('PSD_failures') if check is not None else None,
        joint_work=review['joint_work'], tests_passed=review.get('tests_passed'),
        producer_status=job.get('status'), producer_failure=job.get('reason'),
        producer_cost=job.get('cost'), independent_cost=review.get('cost'),
        accepted_iterations=check.get('accepted_iterations') if check is not None else None,
        stop_reason=check.get('stop_reason') if check is not None else None,
        initial_objective_export=check.get('initial_objective') if check is not None else None,
        final_objective_export=check.get('final_objective') if check is not None else None,
        initial_block_penalties=check.get('initial_block_penalties') if check is not None else None,
        final_block_penalties=check.get('final_block_penalties') if check is not None else None,
        remaining_obligations=([] if review.get('finite_candidate_feasible') is True
                               else ['finite cone feasibility']) +
                              ['universal formal nonconstant identity',
                               'uniform scalar bound, initial storage cost, and ordinary-zeta bridge'],
        interpretation='Finite exact equations and cone checks apply to the saved endpoint. Numerical merit improvement and the learned constraint do not establish an all-scale bound.',
        scalar_budget_obligation_verified=False, **FLAGS)
    report['initial_objective_display'] = display_number(report['initial_objective_export'])
    report['final_objective_display'] = display_number(report['final_objective_export'])
    destination.mkdir()
    write_new(destination / 'report.json', report)
    if (ROOT / NOTE).exists():
        (destination / NOTE).write_text((ROOT / NOTE).read_text())
    require(read(BASE / 'latest.json', 65536) == latest, 'no intervening publication')
    pointer = BASE / 'latest-026.tmp'
    write_new(pointer, dict(publication=destination.name, report='report.json',
                            status=review['status'], **FLAGS))
    pointer.replace(BASE / 'latest.json')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    print(json.dumps(publish(), sort_keys=True))
