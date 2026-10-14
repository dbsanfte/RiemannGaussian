"""Publish exact incorporation of learned rows and the ensuing cone search."""
import argparse
import json
from pathlib import Path
from publish_cancellation_primitive_state_backtracking_cone_search import display_number

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'cancellation-arithmetic-results'
RUN = BASE / 'primitive-state-augmented-cone-search-001'
OUT = BASE / 'publication-028'
NOTE = 'PRIMITIVE_STATE_AUGMENTED_CONE_SEARCH_HANDOFF.txt'
FLAGS = dict(global_bound_proved=False, RH_proved=False,
             universal_identity_proved=False, candidate_admitted=False,
             exact_admission=False, infeasibility_proved=False)


def require(value, message):
    if not value:
        raise ValueError(message)


def read(path, cap=8388608):
    with Path(path).open('rb') as handle:
        data = handle.read(cap+1)
    require(len(data) <= cap, 'bounded publication input')
    return json.loads(data)


def write_new(path, value):
    data = json.dumps(value, sort_keys=True, separators=(',', ':'),
                      allow_nan=False).encode() + b'\n'
    require(len(data) <= 1048576, 'bounded publication summary')
    with Path(path).open('xb') as handle:
        handle.write(data)


def false_flags(value):
    require(type(value) is dict, 'explicit checked record')
    for key in FLAGS:
        require(value.get(key) is False, 'finite endpoint cannot establish '+key)


def checked_outcome(review, chart, center, proposal, endpoint):
    require(review.get('schema') == 'primitive-state-augmented-cone-search-independent-review-v1',
            'independent augmented cone-search review')
    false_flags(review)
    joint = review.get('joint_work', {})
    require(joint.get('max_work') == joint.get('total_work_reserve') == 450000000,
            'one combined research budget')
    status = review.get('status')
    require(status in ('SCALAR_REJECTED', 'CONE_CHECKED', 'UNKNOWN'),
            'explicit finite endpoint disposition')
    if status == 'UNKNOWN':
        require(review.get('all_passed') is False
                and review.get('endpoint_verified') is False
                and review.get('candidate_equations_verified') is False
                and review.get('finite_candidate_feasible') is None,
                'incomplete work cannot promote a point')
        return None
    require(review.get('all_passed') is True and review.get('resource_failure') is None,
            'one completed independent audit')
    for key in ('chart_verified', 'center_verified', 'endpoint_verified', 'candidate_equations_verified'):
        require(review.get(key) is True, 'required completed component: '+key)
    check = review.get('independent_search_check')
    false_flags(check)
    require(check.get('verified') is True and check.get('complete') is True,
            'complete independent mathematical and trace checks')
    require(type(chart) is dict and chart.get('schema') == 'primitive-state-augmented-cone-chart-v1'
            and chart.get('complete') is True and chart.get('width') == 1224
            and chart.get('original_width') == 1957
            and len(chart.get('normalized_rows', [])) == 782
            and len(chart.get('pivot_columns', [])) == 782
            and len(chart.get('free_indices', [])) == 442,
            'complete reusable augmented chart')
    require(type(center) is dict and center.get('schema') == 'primitive-state-augmented-cone-center-v1'
            and center.get('complete') is True and center.get('preserved_seed_free_coordinates') is True
            and center.get('free_indices') == chart['free_indices']
            and len(center.get('initial_free_vector', [])) == 442
            and len(center.get('center_projected_vector', [])) == 1224
            and len(center.get('candidate_original_vector', [])) == 1957,
            'exact center preserves the surviving seed coordinates')
    for value in (proposal, endpoint):
        require(type(value) is dict and value.get('complete') is True,
                'complete saved proposal and endpoint')
        false_flags(value)
    require(endpoint.get('free_indices') == chart['free_indices']
            and len(endpoint.get('final_free_vector', [])) == 442
            and len(endpoint.get('final_projected_vector', [])) == 1224
            and len(endpoint.get('candidate_original_vector', [])) == 1957,
            'complete exact point in the new coordinates')
    exact = check.get('endpoint_check')
    require(type(exact) is dict and exact.get('full_original_rows_checked') == 5641
            and exact.get('learned_rows_checked') == 3
            and exact.get('full_equations_checked') == 5644
            and exact.get('endpoint_verified') is True
            and exact.get('candidate_equations_verified') is True,
            'all old and all three learned equations hold at the endpoint')
    feasible = review.get('finite_candidate_feasible')
    require(type(feasible) is bool and exact.get('finite_candidate_feasible') is feasible,
            'consistent exact finite cone verdict')
    count = exact.get('negative_scalar_count')
    require(type(count) is int and 0 <= count <= 1597, 'all original scalar signs counted')
    if status == 'SCALAR_REJECTED':
        require(count > 0 and feasible is False
                and exact.get('psd_status') == 'NOT_CHECKED_AFTER_SCALAR_REJECTION'
                and exact.get('PSD_blocks_checked') == 0 and exact.get('PSD_failures') is None,
                'scalar rejection leaves matrix diagnostics unchecked')
    else:
        failures = exact.get('PSD_failures')
        require(count == 0 and exact.get('psd_status') == 'ALL_THREE_EXACT_BLOCKS_CHECKED'
                and exact.get('PSD_blocks_checked') == 3
                and type(failures) is int and 0 <= failures <= 3
                and feasible is (failures == 0),
                'scalar success requires all three exact matrix tests')
    trace = check.get('trace_check')
    require(type(trace) is dict and trace.get('verified') is True and trace.get('complete') is True
            and type(trace.get('accepted_iterations')) is int
            and 0 <= trace['accepted_iterations'] <= 128,
            'complete bounded numerical trace')
    return check


def publish(run=RUN, destination=OUT):
    run, destination = Path(run).resolve(), Path(destination).resolve()
    require(not destination.exists(), 'fresh publication destination')
    latest = read(BASE / 'latest.json', 65536)
    require(latest.get('publication') == 'publication-027', 'expected predecessor publication')
    review = read(run / 'independent_verification.json')
    artifacts = {}
    for name, cap in [('chart', 8388608), ('center', 2097152), ('map', 8388608),
                      ('proposal', 33554432), ('endpoint', 2097152), ('search-job', 65536)]:
        path = run / 'jobs' / (name+'.json')
        artifacts[name] = read(path, cap) if path.exists() else None
    check = checked_outcome(review, artifacts['chart'], artifacts['center'],
                            artifacts['proposal'], artifacts['endpoint'])
    exact = check.get('endpoint_check', {}) if check else {}
    trace = check.get('trace_check', {}) if check else {}
    job = artifacts['search-job'] or {}
    report = dict(
        schema=28, title='Learned constraints incorporated and cone search resumed',
        previous_publication='publication-027', seed_origin='publication-026',
        prior_chart_origin='publication-024', added_constraints_origin='publication-027',
        run=str(run.relative_to(ROOT)), status=review['status'], coefficient_rank=782, free_count=442,
        chart_verified=review.get('chart_verified') is True,
        center_verified=review.get('center_verified') is True,
        endpoint_verified=check is not None, candidate_equations_verified=check is not None,
        finite_candidate_feasible=review.get('finite_candidate_feasible'),
        full_original_rows_checked=exact.get('full_original_rows_checked'),
        learned_rows_checked=exact.get('learned_rows_checked'),
        full_equations_checked=exact.get('full_equations_checked'),
        independent_audit_complete=review.get('all_passed') is True,
        independent_resource_failure=review.get('resource_failure'),
        independent_review_path=str((run / 'independent_verification.json').relative_to(ROOT)),
        artifact_paths={name: str((run / 'jobs' / (name+'.json')).relative_to(ROOT))
                        for name, value in artifacts.items() if value is not None},
        new_column_norm_responses=98 if check else None,
        unchanged_column_scales=344 if check else None,
        normalizers_reused_from='publication-025 via the verified publication-026 map',
        initial_step_rule='eight weighted power steps on the augmented map',
        maximum_backtracking_trials=12, old_elimination_replayed=False,
        numerical_norms_certified=False, numerical_gradients_certified=False,
        numerical_optimality_certified=False, feedback_is_discovery_data=True,
        accepted_iterations=trace.get('accepted_iterations'), stop_reason=trace.get('stop_reason'),
        initial_objective_export=trace.get('initial_objective'),
        final_objective_export=trace.get('final_objective'),
        initial_block_penalties=trace.get('initial_block_penalties'),
        final_block_penalties=trace.get('final_block_penalties'),
        negative_scalar_count=exact.get('negative_scalar_count'),
        PSD_status=exact.get('psd_status'), PSD_blocks_checked=exact.get('PSD_blocks_checked'),
        PSD_failures=exact.get('PSD_failures'),
        joint_work=review['joint_work'], tests_passed=review.get('tests_passed'),
        producer_status=job.get('status'), producer_failure=job.get('reason'),
        producer_cost=job.get('cost'), independent_cost=review.get('cost'),
        remaining_obligations=([] if review.get('finite_candidate_feasible') is True else ['finite cone feasibility'])
                              + ['universal nonconstant formal identity',
                                 'uniform scalar budget and initial storage cost',
                                 'cofinal parameter family and ordinary-zeta bridge'],
        interpretation='The saved exact point is tested against all finite and learned equations. '
                       'A scalar rejection decides this point only; skipped matrix diagnostics remain unknown. '
                       'Numerical descent does not prove an all-scale signed bound.',
        scalar_budget_obligation_verified=False, **FLAGS)
    for prefix in ('initial', 'final'):
        report[prefix+'_objective_display'] = display_number(report[prefix+'_objective_export'])
    destination.mkdir()
    write_new(destination / 'report.json', report)
    if (ROOT / NOTE).exists():
        (destination / NOTE).write_bytes((ROOT / NOTE).read_bytes())
    require(read(BASE / 'latest.json', 65536) == latest, 'no intervening publication')
    pointer = BASE / 'latest-028.tmp'
    write_new(pointer, dict(publication=destination.name, report='report.json',
                            status=review['status'], **FLAGS))
    pointer.replace(BASE / 'latest.json')
    return report


if __name__ == '__main__':
    argparse.ArgumentParser(description=__doc__).parse_args()
    print(json.dumps(publish(), sort_keys=True))
