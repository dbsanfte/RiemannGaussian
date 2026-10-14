"""Publish coupled search, paid outer controls and executable unpaid remainders."""
import json
import re
import time
from fractions import Fraction as Q
import run_mobius_coupled_completion_083 as RUN
import run_mobius_coupled_remainder_083 as REM
from run_fractional_prime_kernel_051 import write


def post_files():
    names=REM.FILES+[
        'audit_mobius_coupled_completion_083.py','audit_mobius_coupled_completion_postfix_083.py',
        'mobius_coupled_completion_independent_review_083.json','mobius_coupled_completion_postfix_audit_receipt_083.json',
        'audit_mobius_coupled_artifacts_083.py','MOBIUS_COUPLED_ARTIFACT_REVIEW_083.txt',
        'audit_mobius_coupled_remainder_artifacts_083.py','MOBIUS_COUPLED_REMAINDER_ARTIFACT_REVIEW_083.txt',
        'publish_mobius_coupled_completion_083.py']
    for pattern in ['mobius_coupled_completion_postfix_independent_review_083*.json',
                    'mobius_coupled_runner_preflight_083*.json','mobius_coupled_remainder_integration_083*.json']:
        names += [p.name for p in sorted(RUN.ROOT.glob(pattern))]
    if len(set(names))!=len(names):raise ValueError('duplicate postrun source')
    return names


def test_totals():
    names=['mobius_coupled_completion_search_083_development.json','mobius_coupled_completion_checker_083_development.json',
           'mobius_coupled_outer_control_083_development.json','mobius_coupled_outer_control_checker_083_development.json',
           'mobius_coupled_remainder_checker_083_development.json']
    totals=dict(distinct_tests=0,test_executions=0,successful_test_executions=0,failed_test_executions=0)
    for name in names:
        data=json.loads((RUN.ROOT/name).read_text())
        if data['status']!='PASS':raise ValueError('development incomplete '+name)
        totals['distinct_tests']+=data['distinct_tests']
        for a in data.get('attempts',data.get('test_attempts',[])):
            count=a['tests']
            if 'passed'in a:passed=a['passed']
            elif a.get('exit_code',0)==0 and a.get('status','PASS')=='PASS':passed=count
            else:
                failed=sum(map(int,re.findall(r'(?:failures|errors)=(\d+)',a.get('output',''))))
                if not failed:raise ValueError('unaccounted test failure '+name)
                passed=count-failed
            totals['test_executions']+=count;totals['successful_test_executions']+=passed;totals['failed_test_executions']+=count-passed
    return totals


def target(candidate):
    return dict(id=candidate['id']+'_complete_signed_remainder',source_id=candidate['source_id'],program=candidate['program'],
                outer_certificate=candidate['outer_certificate'],
                compiler='mobius_coupled_remainder_083.raw_remainder',
                independent_checker='check_mobius_coupled_remainder_083.verify_certificate',
                schema='coupled-complete-signed-remainder-v1',
                domain='every positive integer u; all squarefree n<=floor(u/4), including unit and every actual prime',
                raw_matrix='A=A0+sum(theta*Z)+G with G=sum(gram_i*f_i*f_i^T)',
                paid_matrix='O(m,n)=A(m,n)*1[u/5<m<=u/4]*1[u/5<n<=u/4]',
                residual_matrix='R=A-O-G',
                exact_identity='DeltaE(u)=mu^T O mu+mu^T R mu, since all coupled Z have zero actual quadratic form',
                proved_outer_bound='abs(mu^T O mu)<=Astar*u for all integer u>=1',
                Astar=candidate['outer_certificate']['uniform_bound_coefficient'],
                required_signed_bound='There exists finite K independent of u such that mu^T R(u) mu<=K*u for all positive integer u',
                allowed_alternative='A proved complete scale recurrence or sufficiently small power bound, with constants and all source parameters uniform',
                bound_must_include=['every inner and outer/inner cross pair','negative Gram subtraction, including its outer entries',
                                   'joint known-prime anchor constant and affine composite terms','all squarefree composite quadratic terms'],
                new_control_rule='Any added control affecting O must either preserve the proved outer equations or obtain a new full outer certificate.',
                dependency_graph=[dict(node='coupled_zero_identities',status='EXACT_IDENTITY',depends_on=['complete_divisor_convolution']),
                                  dict(node='outer_bound',status='VERIFIED_UNIFORM_BLOCK_BOUND',depends_on=['exact_outer_geometry','coefficient_equations']),
                                  dict(node='signed_remainder_bound',status='UNPAID',depends_on=[]),
                                  dict(node='original_drift_bound',status='UNPAID',depends_on=['coupled_zero_identities','outer_bound','signed_remainder_bound']),
                                  dict(node='full_source_parameter_RH_transfer',status='UNPAID',depends_on=['original_drift_bound'])],
                uniform_remaining_bound_proved=False,uniform_original_source_bound_proved=False,RH_proved=False)


def main():
    started=time.monotonic();root,out=RUN.ROOT,RUN.OUT
    if (out/'publication_integrity.json').exists():raise FileExistsError('preserve published083')
    counts=RUN.validate_parent()
    for name in RUN.FILES:
        if (root/name).read_bytes()!=(out/'source_snapshot'/name).read_bytes():raise ValueError('preserve main083 '+name)
    for name in REM.FILES:
        if (root/name).read_bytes()!=(out/'remainder_source_snapshot'/name).read_bytes():raise ValueError('preserve residual083 '+name)
    post=post_files();frozen={name:(root/name).read_bytes()for name in post}
    report=json.loads((out/'report.json').read_text());residual=json.loads((out/'remainder_report.json').read_text())
    audit=json.loads((out/'independent_artifact_audit_083.json').read_text())
    remainder_audit=json.loads((out/'saved_remainder_artifact_admission_083_attempt002.json').read_text())
    if audit['status']!='VERIFIED_COUPLED_ARTIFACT_BINDING':raise ValueError('saved main-artifact audit required')
    if remainder_audit['status']!='VERIFIED_COUPLED_REMAINDER_ARTIFACT_BINDING':raise ValueError('saved remainder-artifact audit required')
    if report['admitted_proposals']!=24 or report['admitted_validation_rows']!=48 or residual['admitted_rows']!=12:
        raise ValueError('all declared main/residual admissions required')
    candidates=json.loads((out/'frozen_candidates.json').read_text())['candidates'];details=[]
    for c in candidates:
        v=json.loads((out/('validation_'+c['id']+'.json')).read_text())
        if v['program']!=c['program']:raise ValueError('frozen program binding')
        last=max(v['rows'],key=lambda r:r['u'])
        details.append(dict(id=c['id'],source_id=c['source_id'],family_id=c['family_id'],
                            calibration_price_over_u=str(Q(c['certificate']['price'])/c['u']),
                            largest_validation_parent=last['u'],largest_validation_price_over_u=last['price_over_u'],
                            largest_validation_price_over_u2=last['price_over_u2'],
                            uniform_outer_block_proved='outer_certificate'in c,
                            uniform_full_growth_proved=False,uniform_original_source_bound_proved=False,RH_proved=False))
    targets=[target(c)for c in candidates if 'outer_certificate'in c]
    prior=json.loads((RUN.PRIOR.OUT/'published_next_search_input.json').read_text())
    feedback=dict(schema='coupled-signed-remainder-feedback-v1',
        original_obligation=prior['original_obligation'],exact_complete_target=prior['exact_complete_target'],
        original_signed_bound_still_unpaid=True,search_input_is_the_unpaid_bound_not_an_observed_constant=True,
        finite_candidate_programs=[dict(id=c['id'],program=c['program'])for c in candidates],
        executable_remainder_targets=targets,
        retained_old_obstructions=dict(path=str(RUN.PRIOR.OUT/'published_next_search_input.json'),
            scope='Fixed separable group-box prices082 only; do not transfer their dual to the new physical Boolean/prime-anchor grammar without rechecking.'),
        known_prime_information=dict(signs='mu(1)=1; mu(p)=-1 for all actual primes in the current complete range',
            anchored_divisor_functional='h(K)=c(K)-sum_(p<=K)floor(K/p)-c(K)/(N-1)*(N-1-sum_(p<=N)floor(N/p))',
            conventions='c(K)=max(K-1,0); N>=2. K=0 gives0. For N<2, use the original exact finite divisor identity.',
            possible_role='Preserve these complete prime sums jointly with composite terms; prime-filtered zero controls change the affine anchor part but leave the composite-composite quadratic block unchanged.'),
        next_language_priority='Synthesize joint carry/cofactor controls for the complete residual, or a provable recurrence for it; keep the paid outer equations as explicit dependencies.',
        candidate_mechanisms=[
            dict(kind='cofactor_carry',formula='floor(N/m)-floor(n/m)-floor((N-n)/m) in {0,1}',
                 extension='Admitted rationally scaled n/complement cuts and weights across inner/cross regions, including exact multiplicative boundaries.'),
            dict(kind='joint_prime_composite',extension='Controls coupling known prime divisor sums with the remaining composite quadratic kernel; pay transferred constants/cross terms.'),
            dict(kind='scale_recurrence',extension='Invent an auxiliary majorant/energy with independently proved increments or contraction controlling this entire residual.')],
        priority_rules=['proved stronger exponent or complete scale recurrence','an additional uniform block bound whose full transferred remainder is exposed',
                        'reduction to independently paid estimates','finite constants only as secondary evidence'],
        forbidden_shortcuts=['subtracting raw outer price from anchored full price','discarding unknown composite or prime/composite cross terms',
                             'treating a finite dual as an all-scale impossibility theorem','equating elementary prime signs with signed control of the full source',
                             'declaring RH from a q=1 fixed source experiment'],
        proof_template_origin='Outer theorem and coefficient equations derived analytically with Sol6.1 assistance; detector solves within that family. Three unrestricted families also searched.',
        formal_theorem_prover_checked=False,unknown_composite_signs_used=False,observed_full_source_values_used=False,
        uniform_remaining_bound_proved=False,uniform_original_source_bound_proved=False,RH_proved=False)
    write(out/'published_next_search_input.json',feedback)
    tests=test_totals();total=sum(counts)+len(RUN.FILES)+len(post)
    results=dict(status='PUBLISHED_COUPLED_CONTROLS_AND_COMPLETE_REMAINDER_TARGETS',science=report,
                 remainder={k:v for k,v in residual.items()if k not in ('rows','outcomes')},
                 selected_details=details,tests=tests,independent_main_audit=audit['status'],independent_remainder_audit=remainder_audit['status'],
                 retained_remainder_artifact_audit_attempts=['saved_remainder_artifact_admission_083.json','saved_remainder_artifact_admission_083_attempt002.json'],
                 combined_science_elapsed_seconds=report['elapsed_seconds']+residual['elapsed_seconds'],
                 operation_accounting_scope='Instrumented matrix constructors/checkers; main symbolic equality/synthesis setup is not included in matrix totals.',
                 saved_outer_checker_operations=audit['saved_outer_checker_operations'],
                 uniform_remaining_bound_proved=False,uniform_original_source_bound_proved=False,RH_proved=False)
    write(out/'published_results.json',results)
    lines=[d['id']+': B(1024)/1024='+format(float(Q(d['calibration_price_over_u'])),'.7g')+
           '; B('+str(d['largest_validation_parent'])+')/u='+format(float(Q(d['largest_validation_price_over_u'])),'.7g')for d in details]
    residue=[]
    for c in candidates:
        rows=[r for r in residual['rows']if r['candidate_id']==c['id']]
        if rows:
            r=max(rows,key=lambda x:x['u']);d=r['diagnostics'];u=r['u']
            residue.append(c['id']+' at u'+str(u)+': residual B/u='+format(float(Q(r['remainder_price_over_u'])),'.7g')+
                '; signed trace/u='+format(float(Q(d['signed_trace'])/u),'.7g')+
                '; anchor-composite abs/u='+format(float(Q(d['anchor_composite_absolute_price'])/u),'.7g')+
                '; composite-composite abs/u='+format(float(Q(d['composite_composite_absolute_price'])/u),'.7g'))
    handoff='''CURRENT CONTINUATION: COUPLED ARITHMETIC CONTROLS083

The RH objective remains ACTIVE and unfinished. Authoritative next machine
input: stage083/published_next_search_input.json. No uniform complete source
bound, full signed arithmetic cancellation or RH proof has been obtained.

What changed
The detector now searches full physical squarefree pair geometry using exact
divisor identities with coordinate-dependent cutsK_u(n), complementary cuts,
unit balancing, source/product/interval weights and prime/composite filters.
Arbitrary signed rational powers are supported under resource/bit guards.
The exact signs mu(1)=1 andmu(p)=-1 for EVERY actual prime in the range are
substituted jointly before absolute values. No unknown composite signs or
observed full source values enter discovery, selection or validation.
The full Boolean price preserves signed diagonals and every raw pair.

The two original unfolded kernels remain G=M(u//8)-M(u//10)-M(u//4)+M(u//5)
and G+(3547/8192)G(u//3). The target is the complete energy drift
DeltaE(u)=E(u)-(3/2)E(floor(u/2)), E>=source^2.

Actual all-scale progress and its origin
Six synthesized programs have independently checked uniform bounds for the
WHOLE corrected raw outer block u/5<m,n<=u/4, including all actual primes,
composites and their crosses. Matched unit-balanced n,N-n cuts satisfy exact
coefficient equations. They cancel its quadratic-size coefficient price,
leaving absolute block price<=Astar*u for every positive integeru.
The lemma/template was derived analytically with Sol6.1 assistance. The
detector chooses exact coefficients inside that proof family. It did not
invent this lemma unaided. Three unrestricted families remain in the pilot.
These are reviewed elementary proofs with exact independent certificate
checks, not formal theorem-prover proofs or proofs of the full target.

Observed full-price result
24 proposals (2sources,3energies,4families) all passed independent full upper
and price-dual checks at1024, with24 same-geometry zero-parameter baselines.
Eight winners were frozen before6 fresh geometry parents were drawn:
'''+str(report['fresh_geometry_parents'])+'''. All48 validation rows passed.
No retuning/reselection occurred. These are new geometry checks, not new
observed unknown-sign arithmetic. Prices per u increased at larger scales;
the finite results do not establish the required uniform linear bound.
Paying the outer block alone transfers substantial cost into the remainder.
Dual lower bounds concern the finite full coefficient boxes; proof-family
equalities are not imposed in these duals, so their gaps can be large.

Selected exact-program diagnostics (decimal presentation only)
'''+ '\n'.join(lines)+'''

Executable next target, with every term retained
For correctedrawA=A0+sumthetaZ+G, letO be its full rawouter block, including
the selected Gram contribution. Set R=A-O-G. The complete divisor identities
give DeltaE=mu^T O mu+mu^T R mu exactly. The first term is uniformly bounded
byAstar*u; require mu^T R mu<=K*u withK independentofu for EVERY positiveu.
The new compiler mobius_coupled_remainder_083.raw_remainder constructsR;
the independent remainder checker reconstructs it separately. Both selected
proof-family winners passed12 full residual checks on the6 frozen parents.
Negative Gram terms and all inner/cross terms are retained. Congruence onto
the prime anchor happens after this exact matrix partition. No price is
obtained by subtracting a raw outer price from the anchored full price.

Residual diagnostics at the largest checked scale
'''+ '\n'.join(residue)+f'''

Next research direction
Use the explicit residual operators and proof dependencies as detector input.
Search cofactor/carry controls, joint prime-divisor/composite constructions,
or new auxiliary energies with a proved scale recurrence. Require any change
to preserve the paid outer equations or establish a replacement certificate.
Prime-filtered identities alone leave the composite-composite block unchanged;
they can control its affine coupling only with the transferred cost retained.
Do not just fit a larger finite constant or import082 obstruction witnesses
without readmitting them to the new Boolean/prime-anchor geometry. Full source
and parameter transfer to RH remains separate and unpaid.

Verification/resources
{tests['distinct_tests']}distinct focused tests, {tests['test_executions']}executions,
{tests['successful_test_executions']}pass and{tests['failed_test_executions']}retained corrected fixture failures.
Independent producer/resource, main saved-artifact and residual audits pass.
Two earlier producer-audit fixture failures are retained separately; current
integration passes.12additional tiny producer/remainder integrations pass.
The first residual artifact audit assumed asynchronous rows had task order;
that audit failed and was retained. The corrected id-bijection audit passed.
Main science{report['elapsed_seconds']:.3f}s; residual stage{residual['elapsed_seconds']:.3f}s;
3workers, native threads1. Main sampled aggregateRSS{report['sampled_aggregate_peak_rss_bytes']}B,
conservative process-peak sum{report['conservative_process_peak_sum_bytes']}B.
Residual sampled aggregateRSS{residual['sampled_aggregate_peak_rss_bytes']}B,
conservative process-peak sum{residual['conservative_process_peak_sum_bytes']}B.
Authorized16GiB and7200seconds/stage; neither approached. Matrix work counts
are instrumented estimates, not all machine operations; main symbolic setup
is outside those matrix totals. Publication checks resources separately.
Native exact matrix work and duplicate-cut reuse reduce checker overhead.
No old science/tests replayed; no hashes. Sol6.1 agents handled substantial
parallel mathematical/checker/artifact work. Preserve{sum(counts)}older+
{len(RUN.FILES)}main+{len(post)}postrun={total}frozenfiles by direct bytes.
Historical archived handoffs remain intact; root continuation pointers advance.
'''
    for p in [out/'HANDOFF.txt',root/'MOBIUS_COUPLED_COMPLETION_HANDOFF.txt']:
        with p.open('x')as file:file.write(handoff)
    previous=json.loads((RUN.PRIOR.OUT/'publication_integrity.json').read_text())
    pointers=previous['continuation_pointers_updated']+['MOBIUS_DENSE_COMPLETION_HANDOFF.txt']
    for name in pointers:
        (root/name).write_text('Latest continuation: MOBIUS_COUPLED_COMPLETION_HANDOFF.txt\n\n'
            '083 searches coupled divisor operators with exact joint prime signs.\n'
            'Six programs have uniform whole-outer-block controls; the full signed bound remains open.\n'
            'Executable complete remainder targets are in stage083/published_next_search_input.json.\n'
            'Preserve all historical evidence; no RH proof or full uniform source bound.\n')
    snapshot=out/'postrun_snapshot';snapshot.mkdir()
    for name,content in frozen.items():
        (snapshot/name).write_bytes(content)
        if (root/name).read_bytes()!=content:raise ValueError('postrun source changed '+name)
    RUN.validate_parent();RUN.stage_check(started,[__import__('os').getpid()])
    write(out/'publication_integrity.json',dict(status=results['status'],prior_frozen_counts=counts,pre_run_files=RUN.FILES,
          postrun_files=post,total_frozen_files=total,tests=tests,continuation_pointers_updated=pointers,
          historical_handoffs_unchanged=True,publication_elapsed_seconds=time.monotonic()-started,
          source_bytes_preserved=True,hashes_used=False,RH_proved=False))
    print(json.dumps(dict(status=results['status'],uniform_outer_certificates=6,finite_complete_validations=48,
                         exact_remainder_validations=12,total_frozen_files=total,tests=tests,uniform_original_source_bound_proved=False)))


if __name__=='__main__':main()
