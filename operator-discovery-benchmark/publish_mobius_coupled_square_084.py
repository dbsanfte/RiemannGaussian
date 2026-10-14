"""Publish exact finite square bounds and the explicit unpaid uniform target."""
import json
import os
import time
from fractions import Fraction as Q
import run_mobius_coupled_square_084 as RUN
import run_mobius_square_witness_084 as WIT
from run_fractional_prime_kernel_051 import write


def read(path):
    return json.loads(path.read_text())


def post_files():
    names=['audit_mobius_coupled_square_084.py','MOBIUS_COUPLED_SQUARE_INDEPENDENT_REVIEW_084.txt',
           'mobius_coupled_square_preflight_084.json','audit_mobius_coupled_square_artifacts_084.py',
           'MOBIUS_COUPLED_SQUARE_ARTIFACT_REVIEW_084.txt','publish_mobius_coupled_square_084.py',
           'audit_mobius_square_witness_artifacts_084.py']+WIT.FILES
    names += [p.name for p in sorted(RUN.ROOT.glob('mobius_coupled_square_independent_review_084*.json'))]
    if len(names)!=len(set(names)):raise ValueError('duplicate publication file')
    return names


def test_totals():
    result=dict(distinct_tests=0,test_executions=0,passed_test_executions=0,failed_test_executions=0)
    for name in ['mobius_coupled_square_search_084_development.json',
                 'mobius_coupled_square_checker_084_development.json','mobius_rh_target_084_development.json',
                 'mobius_square_witness_084_development.json']:
        data=read(RUN.ROOT/name)
        if data['status']!='PASS':raise ValueError('unfinished test receipt '+name)
        result['distinct_tests']+=data['distinct_tests']
        for attempt in data['attempts']:
            count=attempt['tests']
            if 'passed' in attempt:passed=attempt['passed']
            elif attempt.get('exit_code')==0:passed=count
            else:raise ValueError('unaccounted development attempt')
            result['test_executions']+=count;result['passed_test_executions']+=passed
            result['failed_test_executions']+=count-passed
    return result


def details(candidate):
    discovery=read(RUN.OUT/('search_'+candidate['id']+'.json'))
    validation=read(RUN.OUT/('validation_'+candidate['id']+'.json'))
    if validation['program']!=candidate['program']:raise ValueError('operator freeze binding')
    good=[r for r in validation['rows'] if r['status']=='EXACT_SQUARE_PROPOSAL']
    rows=[]
    for r in [discovery]+good:
        u=r['u'];old=Q(r['diagnostics']['old_residual_price']);new=Q(r['certificate']['price'])
        rows.append(dict(u=u,old_residual_price_over_u=str(old/u),square_price_over_u=str(new/u),
                         exact_price_reduction=str(old-new),factor_rank=r['diagnostics']['rank'],
                         solver_status=r['solver_status'],solver_seconds=r['solver_seconds'],
                         solver_objective_over_u=r['float_objective_over_u'],
                         factor_fallback=r.get('factor_fallback'),
                         grammar_lower_over_u=str(Q(r['dual']['lower_bound'])/u) if 'dual' in r else None,
                         growth_tests=r.get('calibrated_growth_tests',[])))
    return dict(id=candidate['id'],source_id=candidate['source_id'],family_id=candidate['family_id'],rows=rows,
                validation_failures=[dict(u=r['u'],status=r['status'],error=r.get('error')) for r in validation['rows']
                                     if r['status']!='EXACT_SQUARE_PROPOSAL'],
                calibrated_growth_hypotheses=candidate['calibrated_growth_hypotheses'])


def target(candidate):
    return dict(id=candidate['id']+'_uniform_square_price',source_id=candidate['source_id'],program=candidate['program'],
                outer_certificate=candidate['outer_certificate'],
                conditional_RH_target=RUN.TARGET.compile_target(candidate['program'],RUN.transfer(candidate['source_id'])),
                domain='every integer u>=1 and every integer j>=1; q_j=1+1/j',
                matrix='R(u)=P^T(A(u)-O(u)-G(u))P on the complete unit/prime anchor and all squarefree composites',
                bound='B(R_theta_j(u)+L_j(u)L_j(u)^T)<=C_j*u^(1+1/j)',
                Boolean_price='trace(S)+2*sum_(i<k)|S_ik|, retaining signed diagonals',
                constants='C_j finite, nonnegative, independent of u; may depend on j',
                operator_family='theta_j and positive energy may depend on j, with each complete program independently bound to the same fixed source and all outer/domination obligations',
                full_drift='DeltaE(u)<=Astar_j*u+B(R_theta_j(u)+L_j(u)L_j(u)^T)',
                recurrence='E(u)<=r*E(floor(u/2))+(Astar_j+C_j)*u^(1+1/j), E(0)=0; 1<=r<2',
                source_transfer='Exact locally finite two-dilation inverse, and optional convergent third-dilation inverse; either fixed source suffices for RH with every j',
                uniform_proof_leaves=[dict(id='complete_factor_or_diagonal_construction',status='UNPAID'),
                                      dict(id='all_u_all_j_complete_price_bound',status='UNPAID')],
                finite_certificates_do_not_pay_uniform_leaves=True,uniform_remaining_bound_proved=False,RH_proved=False)


def main():
    start=time.monotonic();root,out=RUN.ROOT,RUN.OUT
    if (out/'publication_integrity.json').exists():raise FileExistsError('preserve published084')
    counts=RUN.validate_parent()
    for name in RUN.FILES:
        if (root/name).read_bytes()!=(out/'source_snapshot'/name).read_bytes():raise ValueError('frozen084 source '+name)
    report=read(out/'report.json');audit=read(out/'independent_square_artifact_audit_084.json')
    if report['status']!='COMPLETE_COUPLED_SQUARE_SEARCH':raise ValueError('incomplete science')
    if audit['status']!='VERIFIED_COUPLED_SQUARE_ARTIFACT_BINDING':raise ValueError('independent saved-artifact admission required')
    witness=read(out/'witness_report.json');witness_audit=read(out/'independent_witness_artifact_audit_084.json')
    if witness['status']!='COMPLETE_FIXED_OPERATOR_SQUARE_OBSTRUCTION_DIAGNOSTIC':raise ValueError('incomplete fixed-operator diagnostic')
    if witness_audit['status']!='VERIFIED_SQUARE_WITNESS_ARTIFACT_BINDING':raise ValueError('independent fixed-operator witness admission required')
    for name in WIT.FILES:
        if (root/name).read_bytes()!=(out/'witness_source_snapshot'/name).read_bytes():raise ValueError('frozen witness source '+name)
    witness_details=[]
    for item in witness['outcomes']:
        row=read(out/('witness_'+item['id']+'.json'))
        item={k:row.get(k) for k in ['id','candidate_id','u','status','error','lower_bound_over_u',
                                   'verified_upper_bound','growth_obstructions']}
        item['certificate_file']='witness_'+row['id']+'.json';witness_details.append(item)
    candidates=read(out/'frozen_candidates.json')['candidates'];roster=read(out/'frozen_task_roster.json')['tasks']
    if len(candidates)!=report['frozen_operators']:raise ValueError('candidate count')
    summary=[details(c) for c in candidates]
    attempts=[read(out/('search_'+t['id']+'.json')) for t in roster]
    tests=test_totals();post=post_files();frozen={name:(root/name).read_bytes() for name in post}
    feedback=dict(schema='coupled-square-uniform-target-feedback-v1',previous_goal_turn='PROGRESS',
        finite_candidate_programs=[dict(id=c['id'],program=c['program']) for c in candidates],
        executable_uniform_targets=[target(c) for c in candidates],
        finite_bound_diagnostics=summary,
        observed_residual_growth_tests=report['growth_hypotheses_by_j'],
        fixed_operator_method_diagnostics=witness_details,
        fixed_operator_growth_obstructions=witness['growth_obstructions_by_j'],
        obstruction_scope='Exact finite artificial Boolean witnesses exclude meeting specified frozen constants by ANY positive-square factor for the fixed operator at that u. They do not lower-bound actual Mobius drift, exclude another operator, or establish a uniform obstruction.',
        obstruction_response_rule='For an excluded fixed constant, increasing square rank or solver precision cannot meet that target. Feed the witness into new operator or exact arithmetic-identity synthesis, or seek a separately justified growth theorem with a different constant. Larger finite constants alone are not all-scale progress.',
        finite_factor_artifacts=[dict(id=c['id'],discovery_file='search_'+c['id']+'.json',
                                     new_geometry_file='validation_'+c['id']+'.json',
                                     geometry_specific_not_uniform=True) for c in candidates],
        prior_complete_remainder_input=str(RUN.PRIOR.OUT/'published_next_search_input.json'),
        supersedes_prior_target_wording='For these particular invertible kernels no extra source-parameter family is needed. The all-j exponent family is RH-sufficient; q=1 remains a stronger optional target.',
        arithmetic_information='Known mu(1)=1 and mu(p)=-1 for every actual prime; full divisor zero identities; all squarefree composites and cross pairs retained',
        new_bound_language='Arbitrary rational PSD square completion of the full prime-anchored remainder, jointly synthesized with theta under exact outer constraints',
        proof_rule_origin='PSD and Boolean majorization rule supplied analytically; detector synthesizes operators and exact finite square factors inside that language',
        operator_versus_method_diagnostics='Compare zero-factor price, exact reconstructed square price, noncertified SDP objective and admitted whole-roster dual at the SAME geometry. A finite dual constrains this proof grammar, not actual Mobius cancellation.',
        next_language_priority='Discover structured arithmetic factors or a diagonal majorant with an all-scale trace bound; use remaining trace/correlation estimates and exact fixed-operator counterwitnesses as new detector inputs',
        candidate_mechanisms=['structured complete factors indexed by cofactor, cut or scale',
                              'diagonal-minus-remainder identity with uniformly PSD sparse or rank-one pieces',
                              'new exact zero identities or arithmetic relations that control the retained artificial counterwitnesses while preserving the paid outer equations',
                              'cross-scale trace or energy recurrence retaining every signed prime/composite term'],
        required_progress='A new uniform exponent, a proved complete recurrence, or a reduction to independently paid estimates; finite constants are secondary',
        forbidden_shortcuts=['treating geometry-specific new L as validation of an unchanged or uniform factor',
                             'dropping the paid outer contribution from the full drift',
                             'using unknown composite signs or complete observed source values to fit controls',
                             'claiming an all-j theorem from a finite exponent roster',
                             'promoting floating PSD or a finite grammar dual to an arithmetic theorem'],
        formal_theorem_prover_checked=False,uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False)
    results=dict(status='PUBLISHED_COUPLED_SQUARE_BOUNDS_AND_UNIFORM_TARGETS',science=report,selected_details=summary,
                 discovery_failures=[{k:r.get(k) for k in ['id','status','error']} for r in attempts if r['status']!='EXACT_SQUARE_PROPOSAL'],
                 tests=tests,independent_artifact_admission=audit['status'],
                 witness_diagnostic={k:v for k,v in witness.items()if k!='outcomes'},
                 witness_details=witness_details,independent_witness_admission=witness_audit['status'],
                 corrected_producer_resource_audit_failure_retained=True,preflight_reporting_error_retained=True,
                 uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False)
    write(out/'published_next_search_input.json',feedback);write(out/'published_results.json',results)
    lines=[]
    for d in summary:
        first=d['rows'][0];last=max(d['rows'],key=lambda r:r['u'])
        lines.append(d['id']+': calibration old/square B/u='+format(float(Q(first['old_residual_price_over_u'])),'.7g')+'/'+
                     format(float(Q(first['square_price_over_u'])),'.7g')+'; at u='+str(last['u'])+' old/square B/u='+
                     format(float(Q(last['old_residual_price_over_u'])),'.7g')+'/'+format(float(Q(last['square_price_over_u'])),'.7g'))
    handoff=f'''CURRENT CONTINUATION: JOINT OPERATOR AND SQUARE-BOUND SEARCH084

The RH objective remains active and unfinished. Authoritative machine input:
stage084/published_next_search_input.json, alongside published_results.json.
No uniform complete signed remainder bound or RH proof has been obtained.

What changed
The detector now synthesizes the arithmetic operator and an auxiliary PSD
square factor together. The complete residual is R=A-O-G, with the raw outer
block removed and all prior Gram additions subtracted BEFORE prime projection.
The supplied rule y^T R y<=B(R+L L^T) admits exact rational factors; B retains
signed diagonals and every off-diagonal pair. All actual prime and unit signs
are known jointly, while every squarefree composite and cross pair remains.
No unknown composite signs or observed full source values enter discovery.
An exact dual prices all theta in the same box and outer equality family;
it lower-bounds the finite certificate grammar, not actual arithmetic.

Actual experiment
Eight frozen rosters: two fixed sources times inherited/cofactor/reciprocal/
fractional cuts. Extra rational powers include 2/5, 5/7 and 11/9, with signed
scale exponents; the syntax permits arbitrary rational powers under bit gates.
{report['admitted_proposals']} independently admitted discovery proposals at u=1024.
All admitted families were retained and their operators frozen before draws.
New parents: {report['new_geometry_parents']}.
{report['independently_admitted_auxiliary_rows']} of {report['new_auxiliary_rows']} new-geometry rows admitted.
Each new geometry searches a NEW auxiliary factor with theta unchanged. This
is new certificate search, not a uniform factor theorem or fixed-factor test.
The floating solver objective is guidance; only reconstructed exact prices
are admitted, including explicit zero-square fallback where it is better.
Every failure and solver warning remains in its original record.

Same-operator old/new price diagnostics (decimal presentation only)
'''+ '\n'.join(lines)+f'''

Additional fixed-operator method diagnostic
{witness['admitted']} of {witness['tasks']} artificial Boolean lower witnesses admitted
on the same registered geometries. These are post hoc diagnostics, with no
new SDP search, operator retuning or fresh-validation claim. The exact value
s^T R s, s_i in {{-1,1}}, lower-bounds EVERY PSD-completed Boolean price for
that fixed R. Tests of the frozen growth constants distinguish a factor-search
limitation from a limitation of that fixed operator and proof method.
The witnesses need not satisfy divisor identities and are never presented as
actual Mobius values. No all-scale or whole-operator-grammar no-go follows.
Failure to find an excluding witness is not proof that a target is attainable.
Obstructed finite cases by j: {witness['growth_obstructions_by_j']}.

Correct RH target and missing theorem
For either fixed source G or G+(3547/8192)G(u/3), an explicit locally finite
dilation inverse transfers bounds to Mertens sums. A further source-parameter
family is unnecessary for these kernels. Seek energy exponents q_j=1+1/j for
EVERY integer j>=1, with constants allowed to depend on j. The old q=1 target
is stronger than necessary. Finite j choices are diagnostic only.
For all u and j, construct complete theta_j and L_j(u) and prove
B(R_theta_j(u)+L_j(u)L_j(u)^T)<=C_j*u^(1+1/j), with C_j independent of u.
The already paid outer contribution adds Astar_j*u. Positive energy domination,
E(0)=0 and r=3/2 yield the complete source bound by a factor-4 recurrence.
The target compiler verifies this CONDITIONAL implication; the all-u/all-j
arithmetic leaf is still unpaid. Imported analytic dependencies and explicit
source inverses are reviewed in MOBIUS_RH_TARGET_AUDIT_084.txt.

Next detector input
Search structured factors or diagonal majorants with a proved complete trace
bound or scale recurrence. Feed the exact remaining trace/correlation estimate
back into discovery. Do not replace this with repeated finite constant fitting.
Finite square factors provide witnesses, but their changing dimensions alone
give no all-scale construction or price theorem. All prior outer obligations
and transferred costs remain explicit in the machine targets.

Verification and resources
{tests['distinct_tests']} distinct focused tests, {tests['test_executions']} executions,
{tests['passed_test_executions']} passing. Independent producer/resource and saved-artifact audits pass.
The producer audit first exposed an oversized eigensolver-helper guard gap;
it was fixed before freeze and affected checks passed, retaining the failure.
An ad hoc preflight reporting-key error is also retained; it executed no science.
Main elapsed {report['elapsed_seconds']:.3f}s; three workers, native threads=1.
Sampled aggregate RSS {report['sampled_aggregate_peak_rss_bytes']} bytes;
conservative process-peak sum {report['conservative_process_peak_sum_bytes']} bytes.
Separate witness diagnostic elapsed {witness['elapsed_seconds']:.3f}s;
sampled aggregate RSS {witness['sampled_aggregate_peak_rss_bytes']} bytes,
conservative process-peak sum {witness['conservative_process_peak_sum_bytes']} bytes.
Limits: 16GiB and 7200 seconds. Operation counters cover instrumented matrix/
factor work, not solver instructions, symbolic target/outer or growth work.
All {sum(counts)} prior frozen files and {len(RUN.FILES)} new scientific sources
are preserved by direct bytes, with {len(post)} publication/audit sources.
No hashes, no old scientific reruns. Sol 6.1 agents performed substantial
independent mathematical, certificate and saved-artifact reviews.
'''
    for path in [out/'HANDOFF.txt',root/'MOBIUS_COUPLED_SQUARE_HANDOFF.txt']:
        with path.open('x') as file:file.write(handoff)
    prior=read(RUN.PRIOR.OUT/'publication_integrity.json')
    pointers=prior['continuation_pointers_updated']+['MOBIUS_COUPLED_COMPLETION_HANDOFF.txt']
    for name in pointers:
        (root/name).write_text('Latest continuation: MOBIUS_COUPLED_SQUARE_HANDOFF.txt\n\n'
                              '084 searches full signed remainders with joint operators and exact PSD square bounds.\n'
                              'The fixed-source all-j RH target is explicit; the uniform arithmetic bound remains unpaid.\n'
                              'Preserve historical evidence; authoritative input is stage084/published_next_search_input.json.\n')
    snapshot=out/'postrun_snapshot';snapshot.mkdir()
    for name,content in frozen.items():
        (snapshot/name).write_bytes(content)
        if (root/name).read_bytes()!=content:raise ValueError('postrun source changed '+name)
    RUN.validate_parent();RUN.PRIOR.stage_check(start,[os.getpid()])
    write(out/'publication_integrity.json',dict(status=results['status'],prior_frozen_counts=counts,pre_run_files=RUN.FILES,
          postrun_files=post,total_frozen_files=sum(counts)+len(RUN.FILES)+len(post),tests=tests,
          continuation_pointers_updated=pointers,historical_handoffs_unchanged=True,
          publication_elapsed_seconds=time.monotonic()-start,source_bytes_preserved=True,hashes_used=False,RH_proved=False))
    print(json.dumps(dict(status=results['status'],discovery_admitted=report['admitted_proposals'],
                         new_auxiliary_admitted=report['independently_admitted_auxiliary_rows'],tests=tests,
                         total_frozen_files=sum(counts)+len(RUN.FILES)+len(post),uniform_remaining_bound_proved=False)))


if __name__=='__main__':main()
