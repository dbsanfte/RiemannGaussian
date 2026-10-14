"""Publish sparse numerical diagnostics and only fully checked exact witnesses."""
import argparse
from pathlib import Path
import primitive_state_chart_dual_metric_protocol as C

RUN = C.ROOT/(C.BASE+'primitive-state-chart-dual-metric-001')
OUT = C.ROOT/(C.BASE+'publication-034')
NOTE = 'PRIMITIVE_STATE_CHART_DUAL_METRIC_HANDOFF.txt'


def checked_review(review):
    C.require(review.get('schema') == 'primitive-state-chart-dual-metric-independent-review-v1',
              'independent accelerated review')
    C.require(review.get('joint_work',{}).get('total_work_reserve') == 450000000
              and review['joint_work'].get('allocations') == C.ALLOCATIONS,
              'one combined complete allocation')
    for key in C.FLAGS:
        C.require(review.get(key) is False,'finite proposal cannot establish '+key)
    status = review.get('status')
    C.require(status in ('FINITE_CONE_INFEASIBLE','NONCERTIFIED','UNKNOWN'),
              'explicit mathematical or numerical disposition')
    proved = status == 'FINITE_CONE_INFEASIBLE'
    C.require(review.get('certificate_verified') is proved
              and review.get('finite_augmented_cone_infeasibility_certified') is proved
              and review.get('all_passed') is proved,'only a complete witness is admitted')
    check = review.get('independent_check')
    if check is not None:
        C.require(check.get('schema') == 'primitive-state-chart-dual-metric-independent-check-v1'
                  and check.get('verified') is True and check.get('complete') is proved
                  and check.get('certificate_verified') is proved
                  and check.get('finite_augmented_cone_infeasibility_certified') is proved
                  and check.get('numerical_trajectory_replayed') is False
                  and check.get('numerical_scores_verified') is False,
                  'exact proof separated from numerical diagnostics')
    if proved:
        C.require(type(check) is dict and review.get('workflow_verified') is True
                  and review.get('resource_failure') is None and review.get('validation_failure') is None
                  and check.get('status') == 'FINITE_CONE_INFEASIBLE','complete exact witness outcome')
        witness = check.get('certificate_check') or {}
        C.require(witness.get('schema') == 'primitive-state-chart-dual-independent-check-v1'
                  and witness.get('status') == 'FINITE_CONE_INFEASIBLE'
                  and witness.get('verified') is True and witness.get('complete') is True
                  and witness.get('finite_augmented_cone_infeasibility_certified') is True
                  and witness.get('pairing') == '-1','full original-coordinate exact negative pairing')
    return proved


def publish(run=RUN,destination=OUT):
    run,destination = Path(run).resolve(),Path(destination).resolve()
    C.require(not destination.exists(),'new publication destination')
    latest_path = C.ROOT/(C.BASE+'latest.json'); latest = C.read(latest_path)
    C.require(latest.get('publication') == 'publication-033','designated predecessor')
    review = C.read(run/'independent_verification.json',8388608)
    proved = checked_review(review); check = review.get('independent_check') or {}
    job = C.read(run/'jobs/search-job.json') if (run/'jobs/search-job.json').exists() else {}
    proposal = C.read(run/'jobs/proposal.json',8388608) if (run/'jobs/proposal.json').exists() else {}
    numerical = proposal.get('numerical') or {}; selected = numerical.get('selected') or {}
    report = dict(schema=34,title='Diagonal-metric search for a finite-cone separator',
        previous_publication='publication-033',prior_chart_publication='publication-028',
        run=str(run.relative_to(C.ROOT)),status=review['status'],search_status=review.get('search_status'),
        workflow_verified=review.get('workflow_verified') is True,certificate_verified=proved,
        finite_augmented_cone_infeasibility_certified=proved,
        original_unlearned_cone_infeasibility_certified=False,
        numerical_trajectory_replayed=False,numerical_scores_verified=False,
        source_rows=302,source_columns=687,original_rays=851,rank=782,free_count=442,
        model_stats=proposal.get('model_stats'),
        numerical={key:value for key,value in numerical.items() if key not in ('checkpoints','selected')},
        checkpoints_recorded=len(numerical.get('checkpoints',[])),
        selected_iteration=selected.get('iteration'),selected_support_size=len(selected.get('support',[])),
        selected_relative_residual=selected.get('relative_residual'),
        restoration=proposal.get('restoration_stats'),stage_counts=job.get('stage_counts'),
        independent_check=check,joint_work=review['joint_work'],synthetic_work=review.get('synthetic_work'),
        independent_validation_failure=review.get('validation_failure'),
        independent_resource_failure=review.get('resource_failure'),
        independent_audit_complete=(review.get('workflow_verified') is True and check.get('verified') is True),
        tests_passed=review.get('tests_passed'),producer_cost=job.get('cost'),independent_cost=review.get('cost'),
        reason=review.get('reason') or proposal.get('reason',job.get('reason')),
        artifacts=dict(proposal=str((run/'jobs/proposal.json').relative_to(C.ROOT)),
                       review=str((run/'independent_verification.json').relative_to(C.ROOT))),
        interpretation='Sparse residual minimization proposes a nonnegative support. Numerical '
          'residuals, line tests and stationarity do not prove feasibility or infeasibility. Only a complete '
          'exact negative-pairing witness excludes this augmented finite proof template.',
        remaining_obligations=['signed arithmetic control across all scales',
          'uniform scalar and initial storage bounds','cofinal parameter family and ordinary-zeta bridge'],**C.FLAGS)
    destination.mkdir(); C.write(destination/'report.json',report,1048576)
    if (C.ROOT/NOTE).exists():
        (destination/NOTE).write_bytes((C.ROOT/NOTE).read_bytes())
    C.require(C.read(latest_path) == latest,'no intervening publication')
    C.write(latest_path,dict(publication=destination.name,report='report.json',status=review['status'],
        finite_augmented_cone_infeasibility_certified=proved,**C.FLAGS))
    return report


if __name__ == '__main__':
    argparse.ArgumentParser(description=__doc__).parse_args()
    result = publish()
    print(C.encoded({key:result[key] for key in ('schema','status','search_status',
        'workflow_verified','finite_augmented_cone_infeasibility_certified')}).decode(),end='')
