"""Publish exact LP equivalence separately from any finite-cone separator."""
import argparse
from pathlib import Path
import primitive_state_chart_dual_reduction_protocol as C

RUN = C.ROOT/(C.BASE+'primitive-state-chart-dual-reduction-001')
OUT = C.ROOT/(C.BASE+'publication-031')
NOTE = 'PRIMITIVE_STATE_CHART_DUAL_REDUCTION_HANDOFF.txt'


def checked_review(review):
    C.require(review.get('schema') == 'primitive-state-chart-dual-reduction-independent-review-v1',
              'independent reduction review')
    C.require(review.get('joint_work', {}).get('total_work_reserve') == 450000000
              and review['joint_work'].get('allocations') == C.ALLOCATIONS,
              'one combined complete budget')
    for key in C.FLAGS:
        C.require(review.get(key) is False, 'finite reduction cannot establish '+key)
    status = review.get('status')
    C.require(status in ('REDUCTION_VERIFIED', 'FINITE_CONE_INFEASIBLE', 'UNKNOWN'),
              'explicit independent reduction disposition')
    proved, reduced = status == 'FINITE_CONE_INFEASIBLE', status != 'UNKNOWN'
    C.require(review.get('reduction_verified') is reduced
              and review.get('certificate_verified') is proved
              and review.get('finite_augmented_cone_infeasibility_certified') is proved,
              'separate reduction and separator proof flags')
    check = review.get('independent_check') or {}
    if reduced:
        C.require(review.get('all_passed') is True and review.get('resource_failure') is None
                  and check.get('schema') == 'primitive-state-chart-dual-reduction-independent-check-v1'
                  and check.get('verified') is True and check.get('complete') is True
                  and check.get('reduction_verified') is True,
                  'complete independent exact reduction proof')
        C.require(check.get('certificate_verified') is proved
                  and check.get('finite_augmented_cone_infeasibility_certified') is proved,
                  'independent separator flags agree')
    if proved:
        witness = check.get('certificate_check') or {}
        C.require(check.get('status') == 'FINITE_CONE_INFEASIBLE'
                  and witness.get('schema') == 'primitive-state-chart-dual-independent-check-v1'
                  and witness.get('status') == 'FINITE_CONE_INFEASIBLE'
                  and witness.get('verified') is True and witness.get('complete') is True
                  and witness.get('finite_augmented_cone_infeasibility_certified') is True
                  and witness.get('pairing') == '-1',
                  'complete exact negative-pairing witness')
    return reduced, proved


def publish(run=RUN, destination=OUT):
    run, destination = Path(run).resolve(), Path(destination).resolve()
    C.require(not destination.exists(), 'new publication destination')
    latest_path = C.ROOT/(C.BASE+'latest.json')
    latest = C.read(latest_path)
    C.require(latest.get('publication') == 'publication-030', 'designated predecessor')
    review = C.read(run/'independent_verification.json', 8388608)
    reduced, proved = checked_review(review)
    check = review.get('independent_check') or {}
    job = C.read(run/'jobs/search-job.json') if (run/'jobs/search-job.json').exists() else {}
    proposal = C.read(run/'jobs/proposal.json', 8388608) if (run/'jobs/proposal.json').exists() else {}
    report = dict(schema=31, title='Exact conic equation reduction and dual search',
                  previous_publication='publication-030', prior_chart_publication='publication-028',
                  run=str(run.relative_to(C.ROOT)), status=review['status'],
                  search_status=review.get('search_status'), reduction_verified=reduced,
                  certificate_verified=proved,
                  finite_augmented_cone_infeasibility_certified=proved,
                  original_unlearned_cone_infeasibility_certified=False,
                  restricted_system_inconsistent=check.get('restricted_system_inconsistent'),
                  forced_zero_dual_columns=check.get('forced_zero_columns'),
                  discarded_zero_target_dual_columns=check.get('discarded_zero_target_columns'),
                  reduction_steps=check.get('steps'), reduction_rounds=check.get('rounds'),
                  reduced_rows=check.get('reduced_rows'), reduced_columns=check.get('reduced_columns'),
                  source_rows=317, source_columns=695, original_rays=851,
                  original_lp_rows=443, rank=782, free_count=442,
                  independent_audit_complete=review.get('all_passed') is True,
                  independent_validation_failure=review.get('validation_failure'),
                  independent_resource_failure=review.get('resource_failure'),
                  independent_check=check, joint_work=review['joint_work'],
                  synthetic_work=review.get('synthetic_work'),
                  tests_passed=review.get('tests_passed'),
                  producer_cost=job.get('cost'), independent_cost=review.get('cost'),
                  stage_counts=job.get('stage_counts'), route=proposal.get('route'),
                  numerical=proposal.get('native'), restoration=proposal.get('restoration_stats'),
                  reason=review.get('reason') or proposal.get('reason', job.get('reason')),
                  artifacts=dict(reduction=str((run/'jobs/reduction.json').relative_to(C.ROOT)),
                     proposal=str((run/'jobs/proposal.json').relative_to(C.ROOT)),
                     review=str((run/'independent_verification.json').relative_to(C.ROOT))),
                  interpretation='Reduction preserves feasibility of the selected nonnegative '
                    'generator system by exact row operations and zero extension. A contradiction '
                    'in that system does not prove primal infeasibility. Only a separate full '
                    'negative-pairing witness proves infeasibility of the augmented finite cone.',
                  remaining_obligations=['signed arithmetic control across all scales',
                    'uniform scalar and initial storage bounds',
                    'cofinal parameter family and ordinary-zeta bridge'], **C.FLAGS)
    destination.mkdir()
    C.write(destination/'report.json', report, 1048576)
    if (C.ROOT/NOTE).exists():
        (destination/NOTE).write_bytes((C.ROOT/NOTE).read_bytes())
    C.require(C.read(latest_path) == latest, 'no intervening publication')
    C.write(latest_path, dict(publication=destination.name, report='report.json',
                status=review['status'], reduction_verified=reduced,
                finite_augmented_cone_infeasibility_certified=proved, **C.FLAGS))
    return report


if __name__ == '__main__':
    argparse.ArgumentParser(description=__doc__).parse_args()
    result = publish()
    print(C.encoded({key:result[key] for key in ('schema', 'status', 'search_status',
         'reduction_verified', 'finite_augmented_cone_infeasibility_certified')}).decode(), end='')
