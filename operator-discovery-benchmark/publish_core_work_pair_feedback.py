"""Publish reviewed actual-prime profiles and generated exact pair obligations."""
import json
from pathlib import Path
import time
import core_work_pair_reduction as P
from prime_bank_candidates import Meter
from run_core_signed_work import verify

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'core-signed-work-results/pilot-001'
SOURCE=ROOT/'joint-preconditioner-results/pilot-001/selection.json'
OUT=PARENT/'proof-followup-001'
FILES=['core_work_pair_reduction.py','test_core_work_pair_reduction.py',
       'core_work_pair_reduction_development.json','publish_core_work_pair_feedback.py',
       'CORE_WORK_DIAGONAL_REVIEW_008.txt','CORE_SIGNED_WORK_CANDIDATE_REVIEW_008.txt']


def read(path):return json.loads(path.read_text())


def write(path,value):
    with path.open('x') as f:json.dump(value,f,sort_keys=True,indent=2);f.write('\n')


def main():
    start=time.monotonic();verify(PARENT)
    prior=read(PARENT/'report.json');receipt=read(ROOT/'core_work_pair_reduction_development.json')
    if prior['status']!='SIGNED_PRIME_WORK_SEARCH_AND_INDEPENDENT_VERIFICATION_COMPLETE' or receipt['runs'][-1]['returncode']:
        raise ValueError('completed source verification and owned checks')
    if OUT.exists():raise FileExistsError('new immutable proof followup')
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name in FILES:(OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json',FILES)
    write(OUT/'protocol.json',dict(schema='signed-work-exact-pair-feedback-v1',source_parent=str(SOURCE.relative_to(ROOT)),
        source_rerun=False,refitting=False,reselection=False,operations_limit=8000000,metadata_reserve=1000000,
        development=receipt,proof_scope='exact complete source local algebra plus independently reviewed008 divisor-counting theorems',
        whole_signed_bound_proved=False,RH_proved=False))
    m=Meter(8000000,60);m.charge(1000000)
    s=read(SOURCE);profile=P.source_profile(s['selected'],s['tails'],m)
    write(OUT/'source_mass_profile.json',profile)
    records=read(PARENT/'final_bounds.json')
    reduced=[P.reduce_obligation(r,profile) for r in records];m.charge(1000*len(records))
    write(OUT/'pair_obligations.json',reduced)
    old=read(PARENT/'next_search_input.json')
    next_input=dict(schema='signed-fresh-pair-obligations-v1',status='open',prior_input='candidate10_core_bound_obligation.json',
        target=old['target'],source_mass_profile=profile,generated_pair_obligations=reduced,
        original_generated_obligations=old['generated_obligations'],source_log_bank=old['exact_source_bank'],
        completed_search_report=prior,source_horizon_now_observed=524287,
        new_uniform_proof_rules=['signed shell recovery with strict smaller-scale history mass below2/5',
             'actual squared-coefficient mass c_a*x*log^3x+O(xlog^2x), c_a>0',
             'actual absolute coefficient mass d_a*x*logx+O(x), d_a>0',
             'exact fresh-pair support reduction with explicit unproved-sign old-head product'],
        proof_route_guards=dict(full_termwise_absolute_majorant='reject for cofinal claims: actual majorant growsTheta(X log^2X)',
             separate_diagonal_log_squared_payment='reject for the selected strict contractions: positive cubic forcing remains',
             signed_candidate_itself='open, neither proved nor refuted',
             selective_grouping_then_absolute='allowed only with exact coverage and paid complements'),
        ranking_feedback='all fixed polylog degrees supply the same cofinal goal; do not require logdegree2. Prefer proof closure and signed source pairings over smaller fitted constants or a denser eta grid.',
        next_priority='generate source-specific signed pairings for the complete fresh-leg kernel, retaining old-head product, all prime valuations and bounded-mode prefix crosses; expose every residual as a new obligation',
        degree2_frontier='negative cubic off-diagonal credit must compensate the complete positive diagonal increment',
        broader_cofinal_frontier='degree3 or higher may pay the diagonal directly, but full termwise absolute bounds still lose a power ofX',
        fresh_data_policy='all current numerical values are observed; next adapted final test needs a new declared range',
        unresolved='an independently proved all-scale signed fresh-pair/covariance estimate',
        all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'next_search_input.json',next_input)
    report=dict(status='ACTUAL_PRIME_PROOF_PROFILES_AND_PAIR_REDUCTIONS_COMPLETE',compiled_hadamard_pairs=len(profile['hadamard_pairs']),
        generated_pair_obligations=len(reduced),separate_diagonal_routes_ruled_out=sum(r['separate_diagonal_payment_insufficient'] for r in reduced),
        signed_candidates_disproved=0,all_scale_signed_bounds_proved=0,new_source_evaluations=0,
        operations=m.operations,development_operations=receipt['operations'],total_operations=m.operations+receipt['operations'],
        total_with_parent_operations=prior['total_operations']+m.operations+receipt['operations'],elapsed_seconds=time.monotonic()-start,
        whole_signed_bound_proved=False,RH_proved=False)
    if report['total_operations']>8000000:raise OverflowError('inclusive followup cap')
    verify(PARENT)
    for name in FILES:
        if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():raise ValueError('unchanged new proof source')
    write(OUT/'report.json',report)
    print(json.dumps(report))


if __name__=='__main__':main()
