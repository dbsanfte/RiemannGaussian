"""Compile selected-candidate analysis into reusable guards and paid sectors."""
from collections import Counter
from fractions import Fraction as Q
import json
from pathlib import Path
import time
from flint import arb,ctx
import core_grouping_proof_feedback as P
from prime_bank_candidates import Meter
from run_core_arithmetic_grouping import verify

ROOT=Path(__file__).resolve().parent
PARENT=ROOT/'core-arithmetic-grouping-results/pilot-001'
OUT=PARENT/'proof-followup-001'
FILES=['core_grouping_proof_feedback.py','test_core_grouping_proof_feedback.py',
       'core_grouping_proof_feedback_development.json','publish_core_grouping_proof_feedback.py',
       'CORE_SELECTED_GROUPING_REVIEW_010.txt']


def read(path):return json.loads(path.read_text())
def write(path,value):
    with path.open('x') as f:json.dump(value,f,indent=2,sort_keys=True);f.write('\n')


def main():
    start=time.monotonic();ctx.prec=192;verify();parent=read(PARENT/'report.json')
    if parent['status']!='ARITHMETIC_GROUPING_SEARCH_AND_COMPLETE_VERIFICATION_FINISHED':raise ValueError('terminal verified parent study')
    if OUT.exists():raise FileExistsError('one immutable proof feedback publication')
    receipt=read(ROOT/'core_grouping_proof_feedback_development.json')
    if receipt['runs'][-1]['returncode'] or receipt['operations']!=sum(r['operations'] for r in receipt['runs']):raise ValueError('owned affected checks')
    for name in FILES:
        if not (ROOT/name).is_file():raise FileNotFoundError(name)
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name in FILES:(OUT/'source_snapshot'/name).write_bytes((ROOT/name).read_bytes())
    write(OUT/'source_files.json',FILES)
    write(OUT/'protocol.json',dict(schema='source-driven-grouping-proof-feedback-v1',new_source_runs=0,reselection=False,
        full_group_matrices_already_verified=True,development=receipt,work_cap=8000000,metadata_reserve=1000000,
        head_cutoff_log_powers=['0','1/6','1/3','1/2','1','2'],
        proof_scope='reviewed infinite arguments plus exact local-source algebra; no formal theorem prover claim',
        whole_signed_bound_proved=False,RH_proved=False))
    m=Meter(8000000,120);m.charge(1000000)
    source=read(ROOT/'core-signed-work-results/pilot-001/source_program.json')
    z=(arb(2)/3).zeta();Ru=arb(9)/2*((arb(4)/3).zeta()/(z*z)-1/z);m.charge(1000)
    programs=read(PARENT/'programs.json');evaluations=[P.evaluate(r,source,Ru,m) for r in programs]
    for row,result in zip(programs,evaluations):
        cert=result['certificate']
        if cert and cert['rule']=='complete_positive_fresh_semiprime_classes':
            a,b=map(Q,cert['label_prime_band']);c,d=map(Q,cert['complementary_prime_band'])
            if not (a<b and c<d and a*c>2 and b*d<Q(5,2)):raise ArithmeticError('complete comparable prime rectangle')
            if row['program']['post']['op']=='remove_smallest_once':
                if not (a>2 and c>1 and d<a):raise ArithmeticError('fresh smallest-removal class')
            elif not (a*a>2 and b<c):raise ArithmeticError('fresh largest-removal class including its diagonal')
            m.charge(100)
    by_id={r['program_id']:r for r in evaluations};write(OUT/'proof_gates.json',evaluations)
    heads=[]
    for row in programs:
        if row['proof_gate']!='open_grouped_arithmetic_premise' or by_id[row['id']]['uniform_group_bound_disproved']:continue
        for a in ('0','1/6','1/3','1/2','1','2'):
            cert=P.square_lift_head(row['program'],Ru,a,m)
            if cert:heads.append(dict(program_id=row['id'],program=row['program'],certificate=cert))
    write(OUT/'paid_head_certificates.json',heads)
    selection=read(PARENT/'selection.json');selected=[dict(program_id=r['id'],program=r['program'],proof=by_id[r['id']]) for r in selection]
    write(OUT/'selected_proof_feedback.json',selected)
    # Shape audit supplements the parent entrywise comparison: no zip truncation.
    for row in selection:
        for backend in ('producer','checker'):
            r=read(PARENT/(backend+'-program-'+str(row['id'])+'.json'));G=len(r['group_labels'])
            if len(r['group_matrix'])!=G or any(len(v)!=G for v in r['group_matrix']):raise ArithmeticError('full square selected matrix')
            m.charge(G*G+10)
    old=read(PARENT/'next_search_input.json');selected_ids={r['id'] for r in selection}
    remaining=[r for r in old['generated_grouped_obligations'] if not by_id[r['program_id']]['uniform_group_bound_disproved']]
    new_obligations=[]
    for row in heads:
        if row['program_id'] not in selected_ids:continue
        cert=row['certificate']
        new_obligations.append(dict(program_id=row['program_id'],program=row['program'],log_cutoff_power=cert['log_cutoff_power'],
            paid_low_low_certificate=cert,expression=cert['signed_remainder'],required_bound=cert['remaining_lemma'],
            original_target_recovery='paid low-low sector plus one-sided signed remainder gives complete step; then original recurrence/history/correction chain applies',
            domain=cert['domain'],same_scale_partition_in_parent_and_child=True,
            every_high_low_low_high_high_high_pair_retained_once=True,
            source_horizon_already_observed=524287,uniform_remainder_bound_proved=False,whole_signed_bound_proved=False,RH_proved=False))
    next_input=dict(schema='square-lift-signed-remainder-search-input-v1',status='open',target=old['target'],
        prior_input='candidate10_signed_work_obligation.json',parent_grouping_search=str(PARENT.relative_to(ROOT)),
        source_mass_profile=old['source_mass_profile'],selected_proof_feedback=selected,
        surviving_full_grouped_obligations=remaining,generated_signed_remainder_obligations=new_obligations,
        reusable_proof_gates=evaluations,generated_paid_head_certificate_count=len(heads),
        original_corrections_and_recovery_retained=True,source_horizon_now_observed=524287,
        evidence='selected117 and37 grouped polylog claims disproved analytically; selected110 remains open with a uniformly paid polylog-growing low-cell sector',
        next_priority='search constructions for the complete signed high-cell remainder, retaining all low/high crosses and unremoved prime-square contributions; consider weighted cross-cofactor transport',
        exclusion='do not rerun the same eta/constants or relabel known finite probes as fresh; partial-sector theorems do not bound the remaining signed covariance',
        all_scale_signed_control_proved=False,whole_signed_bound_proved=False,RH_proved=False)
    write(OUT/'next_search_input.json',next_input)
    counts=Counter(r['certificate']['rule'] for r in evaluations if r['certificate'])
    report=dict(status='GROUPING_PROOF_FEEDBACK_AND_PAID_HEAD_COMPILATION_COMPLETE',
        compiled_programs=len(programs),new_grouped_routes_disproved=sum(r['uniform_group_bound_disproved'] for r in evaluations),
        new_proof_rules=dict(counts),selected_grouped_routes_disproved=sum(r['proof']['uniform_group_bound_disproved'] for r in selected),
        selected_candidates_remaining_open=len(remaining),paid_head_certificates=len(heads),
        paid_head_programs=len(set(r['program_id'] for r in heads)),new_signed_remainder_obligations=len(new_obligations),
        operations=m.operations,development_operations=receipt['operations'],total_operations=m.operations+receipt['operations'],
        total_with_parent_operations=parent['total_operations']+m.operations+receipt['operations'],
        elapsed_seconds=time.monotonic()-start,new_source_evaluations=0,
        full_all_scale_bounds_proved=0,whole_signed_bound_proved=False,RH_proved=False)
    if report['total_operations']>8000000:raise OverflowError('inclusive new proof work cap')
    verify()
    for name in FILES:
        if (ROOT/name).read_bytes()!=(OUT/'source_snapshot'/name).read_bytes():raise ValueError('changed new proof source')
    write(OUT/'report.json',report);print(json.dumps(report))


if __name__=='__main__':main()
