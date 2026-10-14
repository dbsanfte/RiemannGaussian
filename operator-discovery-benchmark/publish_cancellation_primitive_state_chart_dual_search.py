"""Publish a directly checked dual witness or an explicitly uncertified search."""
import argparse
from pathlib import Path
import primitive_state_chart_dual_protocol as C

RUN = C.ROOT/(C.BASE+'primitive-state-chart-dual-search-001')
OUT = C.ROOT/(C.BASE+'publication-029')
NOTE = 'PRIMITIVE_STATE_CHART_DUAL_SEARCH_HANDOFF.txt'


def checked_review(review):
    C.require(review.get('schema') == 'primitive-state-chart-dual-independent-review-v1',
              'independent chart dual review')
    C.require(review.get('joint_work', {}).get('total_work_reserve') == 450000000
              and review['joint_work'].get('allocations') == C.ALLOCATIONS,
              'single complete work allowance')
    for key in C.FLAGS:
        C.require(review.get(key) is False, 'finite review cannot establish '+key)
    status = review.get('status')
    C.require(status in ('FINITE_CONE_INFEASIBLE', 'NONCERTIFIED', 'UNKNOWN'),
              'explicit independent outcome')
    proved = status == 'FINITE_CONE_INFEASIBLE'
    C.require(review.get('certificate_verified') is proved
              and review.get('finite_augmented_cone_infeasibility_certified') is proved,
              'certificate flags agree with scope')
    if proved:
        check = review.get('independent_check', {})
        C.require(review.get('all_passed') is True and review.get('resource_failure') is None
                  and check.get('schema') == 'primitive-state-chart-dual-independent-check-v1'
                  and check.get('status') == 'FINITE_CONE_INFEASIBLE'
                  and check.get('verified') is True and check.get('complete') is True
                  and check.get('pairing') == '-1' and check.get('rank') == 782
                  and check.get('free_coordinates') == 442
                  and check.get('finite_augmented_cone_infeasibility_certified') is True,
                  'complete exact independent separator proof')
    return proved


def publish(run=RUN, destination=OUT):
    run, destination = Path(run).resolve(), Path(destination).resolve()
    C.require(not destination.exists(), 'new publication destination')
    latest_path = C.ROOT/(C.BASE+'latest.json')
    latest = C.read(latest_path)
    C.require(latest.get('publication') == 'publication-028', 'designated predecessor')
    review = C.read(run/'independent_verification.json', 8388608)
    proved = checked_review(review)
    job = C.read(run/'jobs/search-job.json')
    proposal = C.read(run/'jobs/proposal.json', 8388608) if (run/'jobs/proposal.json').exists() else {}
    report = dict(schema=29, title='Direct dual search on the augmented equation chart',
                  previous_publication='publication-028', status=review['status'],
                  run=str(run.relative_to(C.ROOT)), rank=782, free_count=442,
                  fixed_scalar_generators=371, fixed_matrix_generators=450,
                  endpoint_matrix_generators=30,
                  finite_augmented_cone_infeasibility_certified=proved,
                  independent_audit_complete=review.get('all_passed') is True,
                  certificate_verified=proved,
                  scope='complete publication028 finite cone including all three learned rows',
                  independent_review=str((run/'independent_verification.json').relative_to(C.ROOT)),
                  artifact=str((run/'jobs/proposal.json').relative_to(C.ROOT)) if proposal else None,
                  producer_status=job.get('status'), reason=proposal.get('reason', job.get('reason')),
                  assembly=proposal.get('assembly_stats'), numerical=proposal.get('native'),
                  restoration=proposal.get('restoration_stats'), stage_counts=job.get('stage_counts'),
                  producer_cost=job.get('cost'), independent_cost=review.get('cost'),
                  independent_check=review.get('independent_check'),
                  joint_work=review['joint_work'], tests_passed=review.get('tests_passed'),
                  numerical_ray_positivity='exact rank-one sums; eigenvector accuracy is unnecessary',
                  interpretation=('An exact separator excludes this augmented finite proof cone. '
                                  'It does not refute an arithmetic bound or RH.' if proved else
                                  'No exact separator was obtained. Finite feasibility remains unresolved.'),
                  remaining_obligations=['signed arithmetic control across all scales',
                    'uniform scalar and initial storage bounds',
                    'cofinal parameter family and ordinary-zeta bridge'], **C.FLAGS)
    destination.mkdir()
    C.write(destination/'report.json', report, 1048576)
    if (C.ROOT/NOTE).exists():
        (destination/NOTE).write_bytes((C.ROOT/NOTE).read_bytes())
    C.require(C.read(latest_path) == latest, 'no intervening publication')
    C.write(latest_path, dict(publication=destination.name, report='report.json',
                status=review['status'], finite_augmented_cone_infeasibility_certified=proved,
                **C.FLAGS))
    return report


if __name__ == '__main__':
    argparse.ArgumentParser(description=__doc__).parse_args()
    value = publish()
    print(C.encoded({key:value[key] for key in ('schema', 'status',
        'finite_augmented_cone_infeasibility_certified', 'reason')}).decode(), end='')
