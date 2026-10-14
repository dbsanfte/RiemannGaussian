"""Publish exactly verified conditional cone geometry and separator disposition."""
import argparse
from pathlib import Path
import primitive_state_chart_dual_geometry_protocol as C

RUN = C.ROOT/(C.BASE+'primitive-state-chart-dual-geometry-search-001')
OUT = C.ROOT/(C.BASE+'publication-030')
NOTE = 'PRIMITIVE_STATE_CHART_DUAL_GEOMETRY_HANDOFF.txt'


def checked_review(review):
    C.require(review.get('schema') == 'primitive-state-chart-dual-geometry-independent-review-v1',
              'independent geometry review')
    C.require(review.get('joint_work', {}).get('total_work_reserve') == 450000000
              and review['joint_work'].get('allocations') == C.ALLOCATIONS,
              'one combined complete budget')
    for key in C.FLAGS:
        C.require(review.get(key) is False, 'finite geometry cannot establish '+key)
    status = review.get('status')
    C.require(status in ('GEOMETRY_VERIFIED', 'FINITE_CONE_INFEASIBLE', 'UNKNOWN'),
              'explicit independent geometry disposition')
    proved, geometry = status == 'FINITE_CONE_INFEASIBLE', status != 'UNKNOWN'
    C.require(review.get('geometry_verified') is geometry
              and review.get('certificate_verified') is proved
              and review.get('finite_augmented_cone_infeasibility_certified') is proved,
              'separate geometry and separator proof flags')
    check = review.get('independent_check') or {}
    if geometry:
        C.require(review.get('all_passed') is True and review.get('resource_failure') is None
                  and check.get('schema') == 'primitive-state-chart-dual-geometry-independent-check-v1'
                  and check.get('verified') is True and check.get('complete') is True
                  and check.get('geometry_verified') is True,
                  'complete independent geometry proof')
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
    return geometry, proved


def publish(run=RUN, destination=OUT):
    run, destination = Path(run).resolve(), Path(destination).resolve()
    C.require(not destination.exists(), 'new publication destination')
    latest_path = C.ROOT/(C.BASE+'latest.json')
    latest = C.read(latest_path)
    C.require(latest.get('publication') == 'publication-029', 'designated predecessor')
    review = C.read(run/'independent_verification.json', 8388608)
    geometry, proved = checked_review(review)
    check = review.get('independent_check') or {}
    job = C.read(run/'jobs/search-job.json') if (run/'jobs/search-job.json').exists() else {}
    proposal = C.read(run/'jobs/proposal.json', 8388608) if (run/'jobs/proposal.json').exists() else {}
    report = dict(schema=30, title='Exact cone faces and compressed dual search',
                  previous_publication='publication-029', prior_chart_publication='publication-028',
                  run=str(run.relative_to(C.ROOT)), status=review['status'],
                  search_status=review.get('search_status'), geometry_verified=geometry,
                  certificate_verified=proved,
                  finite_augmented_cone_infeasibility_certified=proved,
                  original_unlearned_cone_infeasibility_certified=False,
                  conditional_face_constraints=geometry,
                  zero_ray_count=check.get('zero_ray_count'),
                  exposed_ray_count=check.get('exposed_ray_count'),
                  forced_scalar_indices=check.get('forced_scalar_indices'),
                  kernel_spans=check.get('kernel_spans'),
                  compressed_rows=check.get('compressed_rows'),
                  compressed_columns=check.get('compressed_columns'),
                  negative_constant_ray=check.get('negative_constant_ray'),
                  rank=782, free_count=442, original_lp_rows=443, original_lp_columns=851,
                  independent_audit_complete=review.get('all_passed') is True,
                  independent_check=check, joint_work=review['joint_work'],
                  tests_passed=review.get('tests_passed'),
                  producer_cost=job.get('cost'), independent_cost=review.get('cost'),
                  stage_counts=job.get('stage_counts'), route=proposal.get('route'),
                  numerical=proposal.get('native'), restoration=proposal.get('restoration_stats'),
                  reason=proposal.get('reason', job.get('reason')),
                  artifacts=dict(geometry=str((run/'jobs/geometry.json').relative_to(C.ROOT)),
                     proposal=str((run/'jobs/proposal.json').relative_to(C.ROOT)),
                     review=str((run/'independent_verification.json').relative_to(C.ROOT))),
                  interpretation='Verified faces are necessary conditions for any feasible point. '
                    'They do not establish that such a point exists or prove an arithmetic bound. '
                    'Only a separate exact negative-pairing witness establishes finite infeasibility.',
                  remaining_obligations=['signed arithmetic control across all scales',
                    'uniform scalar and initial storage bounds',
                    'cofinal parameter family and ordinary-zeta bridge'], **C.FLAGS)
    destination.mkdir()
    C.write(destination/'report.json', report, 1048576)
    if (C.ROOT/NOTE).exists():
        (destination/NOTE).write_bytes((C.ROOT/NOTE).read_bytes())
    C.require(C.read(latest_path) == latest, 'no intervening publication')
    C.write(latest_path, dict(publication=destination.name, report='report.json',
                status=review['status'], geometry_verified=geometry,
                finite_augmented_cone_infeasibility_certified=proved, **C.FLAGS))
    return report


if __name__ == '__main__':
    argparse.ArgumentParser(description=__doc__).parse_args()
    result = publish()
    print(C.encoded({key:result[key] for key in ('schema', 'status', 'search_status',
         'geometry_verified', 'finite_augmented_cone_infeasibility_certified')}).decode(), end='')
