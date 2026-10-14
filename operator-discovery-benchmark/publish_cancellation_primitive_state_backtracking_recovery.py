"""Publish independent restoration without promoting the failed producer."""
import argparse
import json
from pathlib import Path
import publish_cancellation_primitive_state_backtracking_cone_search as B

ROOT, RUN, OUT, FLAGS = B.ROOT, B.RUN, B.OUT, B.FLAGS
NOTE = 'PRIMITIVE_STATE_BACKTRACKING_CONE_SEARCH_HANDOFF.txt'
require, read, write_new = B.require, B.read, B.write_new


def checked_outcome(review, endpoint):
    require(review.get('schema') == 'primitive-state-backtracking-recovery-independent-review-v1',
            'explicit independent recovery policy')
    for key in FLAGS:
        require(review.get(key) is False, 'no global admission from recovery')
    joint = review.get('joint_work', {})
    require(joint.get('max_work') == joint.get('total_work_reserve') == 450000000,
            'same combined research reservation')
    status = review.get('status')
    require(status in ('RECOVERED_SCALAR_REJECTED', 'RECOVERED_CONE_CHECKED', 'UNKNOWN'),
            'explicit recovery disposition')
    if status == 'UNKNOWN':
        require(review.get('endpoint_verified') is False
                and review.get('candidate_equations_verified') is False
                and review.get('finite_candidate_feasible') is None,
                'no promotion from incomplete restoration')
        return None
    require(review.get('all_passed') is True and review.get('endpoint_verified') is True
            and review.get('candidate_equations_verified') is True,
            'completed independent restoration')
    check = review.get('recovery_check')
    require(isinstance(check, dict) and check.get('full_original_rows_checked') == 5641
            and check.get('feedback_row_verified') is True, 'all source and learned equations')
    require(type(review.get('finite_candidate_feasible')) is bool, 'exact finite verdict')
    require(isinstance(endpoint, dict) and endpoint.get('complete') is True
            and len(endpoint.get('candidate_original_vector', [])) == 1957
            and len(endpoint.get('final_projected_vector', [])) == 1224
            and len(endpoint.get('final_free_vector', [])) == 444,
            'complete separately restored exact point')
    if status == 'RECOVERED_SCALAR_REJECTED':
        require(review['finite_candidate_feasible'] is False
                and type(check.get('negative_scalar_count')) is int
                and check['negative_scalar_count'] > 0
                and check.get('psd_status') == 'NOT_CHECKED_AFTER_SCALAR_REJECTION'
                and check.get('PSD_blocks_checked') == 0 and check.get('PSD_failures') is None,
                'scalar rejection does not imply matrix diagnostics')
    else:
        require(check.get('negative_scalar_count') == 0
                and check.get('psd_status') == 'ALL_THREE_EXACT_BLOCKS_CHECKED'
                and check.get('PSD_blocks_checked') == 3
                and type(check.get('PSD_failures')) is int
                and 0 <= check['PSD_failures'] <= 3
                and review['finite_candidate_feasible'] is (check['PSD_failures'] == 0),
                'all matrix cones required after scalar success')
    return check


def publish(run=RUN, destination=OUT):
    run, destination = Path(run).resolve(), Path(destination).resolve()
    require(not destination.exists(), 'fresh publication')
    latest = read(B.BASE / 'latest.json', 65536)
    require(latest.get('publication') == 'publication-025', 'expected predecessor')
    review = read(run / 'independent_recovery_verification.json', 65536)
    path = run / 'recovered-endpoint.json'
    endpoint = read(path, 2097152) if path.exists() else None
    check = checked_outcome(review, endpoint)
    job = read(run / 'jobs/search-job.json', 65536)
    failed = read(run / 'jobs/endpoint.json', 2097152)
    require(job.get('status') == 'UNKNOWN' and job.get('endpoint_complete') is False
            and failed.get('complete') is False, 'original failed producer remains failed')
    trace = review.get('independent_search_check') or {}
    report = dict(
        schema=26, title='Extended cone descent and independent exact restoration',
        previous_publication='publication-025', seed_origin='publication-025',
        exact_affine_center_origin='publication-024', run=str(run.relative_to(ROOT)),
        status=review['status'], coefficient_rank=780, free_count=444,
        endpoint_verified=check is not None,
        candidate_equations_verified=check is not None,
        finite_candidate_feasible=review.get('finite_candidate_feasible'),
        independent_audit_complete=review.get('all_passed') is True and check is not None,
        independent_review_path=str((run / 'independent_recovery_verification.json').relative_to(ROOT)),
        endpoint_path=str(path.relative_to(ROOT)) if check is not None else None,
        producer_status=job['status'], producer_failure=job.get('reason'),
        producer_cost=job.get('cost'), independent_cost=review.get('cost'),
        independent_resource_failure=review.get('resource_failure'),
        joint_work=review['joint_work'], tests_passed=review.get('tests_passed'),
        accepted_iterations=trace.get('accepted_iterations'), stop_reason=trace.get('stop_reason'),
        initial_objective_export=trace.get('initial_objective'),
        final_objective_export=trace.get('final_objective'),
        initial_block_penalties=trace.get('initial_block_penalties'),
        final_block_penalties=trace.get('final_block_penalties'),
        negative_scalar_count=check.get('negative_scalar_count') if check else None,
        PSD_status=check.get('psd_status') if check else None,
        PSD_blocks_checked=check.get('PSD_blocks_checked') if check else None,
        PSD_failures=check.get('PSD_failures') if check else None,
        maximum_backtracking_trials=12, saved_scales_and_normalizers_reused=True,
        new_column_norm_responses=0, native_numerical_merits_certified=False,
        original_failed_endpoint_promoted=False, feedback_is_discovery_data=True,
        interpretation='The exact point is independently restored from the saved numerical increment. Scalar rejection decides this point only; skipped PSD diagnostics are unknown.',
        remaining_obligations=([] if review.get('finite_candidate_feasible') is True else ['finite cone feasibility']) +
                              ['universal nonconstant identity', 'uniform scalar budget and initial storage cost',
                               'cofinal parameter family and ordinary-zeta bridge'], **FLAGS)
    for prefix in ('initial', 'final'):
        report[prefix + '_objective_display'] = B.display_number(report[prefix + '_objective_export'])
    destination.mkdir()
    write_new(destination / 'report.json', report)
    if (ROOT / NOTE).exists():
        (destination / NOTE).write_text((ROOT / NOTE).read_text())
    require(read(B.BASE / 'latest.json', 65536) == latest, 'no intervening publication')
    pointer = B.BASE / 'latest-026.tmp'
    write_new(pointer, dict(publication=destination.name, report='report.json',
                            status=review['status'], **FLAGS))
    pointer.replace(B.BASE / 'latest.json')
    return report


if __name__ == '__main__':
    argparse.ArgumentParser(description=__doc__).parse_args()
    print(json.dumps(publish(), sort_keys=True))
