"""Publish exact complete-bound search and detector-invented price obstructions."""
import json
from fractions import Fraction as Q

import run_mobius_dense_completion_082 as RUN
import run_mobius_dense_rank_obstruction_082 as RANK
from run_fractional_prime_kernel_051 import write

POST_FILES=RANK.FILES+[
    'audit_mobius_dense_completion_082.py',
    'mobius_dense_completion_independent_review_082.json',
    'mobius_dense_completion_independent_review_082_attempt_1791722403082558712.json',
    'MOBIUS_DENSE_COMPLETION_INDEPENDENT_REVIEW_082.txt',
    'audit_mobius_dense_completion_artifacts_082.py',
    'MOBIUS_DENSE_COMPLETION_ARTIFACT_AUDIT_082.txt',
    'audit_mobius_dense_rank_artifacts_082.py',
    'MOBIUS_DENSE_RANK_ARTIFACT_AUDIT_082.txt',
    'publish_mobius_dense_completion_082.py']


def test_totals():
    names=['mobius_dense_completion_search_082_development.json',
           'mobius_dense_completion_checker_082_development.json',
           'mobius_dense_rank_obstruction_082_development.json',
           'mobius_dense_rank_obstruction_checker_082_development.json']
    totals=dict(distinct_tests=0,test_executions=0,successful_test_executions=0,failed_test_executions=0)
    for name in names:
        data=json.loads((RUN.ROOT/name).read_text())
        attempts=data.get('attempts',data.get('test_attempts',[]))
        if not attempts or data.get('status',attempts[-1].get('status'))!='PASS':
            raise ValueError('incomplete final development '+name)
        totals['distinct_tests']+=data.get('distinct_tests',max(a.get('tests',a.get('tests_run',0)) for a in attempts))
        for a in attempts:
            count=a.get('tests',a.get('tests_run'))
            if type(count) is not int:
                raise ValueError('test count '+name)
            passed=a.get('passed',count if a.get('exit_code',0)==0 and a.get('status','PASS')=='PASS' else 0)
            totals['test_executions']+=count
            totals['successful_test_executions']+=passed
            totals['failed_test_executions']+=count-passed
    return totals


def main():
    root,out=RUN.ROOT,RUN.OUT
    if (out/'publication_integrity.json').exists():
        raise FileExistsError('preserve completed082 publication')
    counts=RUN.validate_parent()
    for name in RUN.FILES:
        if (root/name).read_bytes()!=(out/'source_snapshot'/name).read_bytes():
            raise ValueError('preserve main082 '+name)
    for name in RANK.FILES:
        if (root/name).read_bytes()!=(out/'rank_source_snapshot'/name).read_bytes():
            raise ValueError('preserve rank082 '+name)
    frozen={name:(root/name).read_bytes() for name in POST_FILES}
    main_report=json.loads((out/'report.json').read_text())
    rank_report=json.loads((out/'rank_obstruction_results.json').read_text())
    audit=json.loads((out/'saved_artifact_admission_082.json').read_text())
    rank_audit=json.loads((out/'saved_rank_artifact_admission_082_attempt002.json').read_text())
    if audit['status']!='VERIFIED_SAVED_DENSE_ARTIFACT_BINDING':
        raise ValueError('independent saved main-artifact admission required')
    if rank_audit['status']!='VERIFIED_SAVED_UNIFORM_RANK_ARTIFACT_BINDING':
        raise ValueError('independent saved rank-artifact admission required')
    if rank_report['status']!='VERIFIED_COMPLETE_PILOT_GRAMMAR_PRICE_OBSTRUCTIONS' or len(rank_report['rows'])!=36:
        raise ValueError('all36 uniform interval admissions required')
    candidates=json.loads((out/'frozen_candidates.json').read_text())['candidates']
    obstructions={row['id']:row for row in rank_report['rows']}
    details=[]
    for candidate in candidates:
        name=candidate['id'];obstruction=obstructions[name]
        if candidate['program']!=obstruction['program']:
            raise ValueError('exact selected obstruction binding '+name)
        check=obstruction['admission'];cert=obstruction['certificate']
        if (check['status']!='VERIFIED_UNIFORM_DENSE_GRAMMAR_PRICE_OBSTRUCTION' or
            check['lower_coefficient']!=cert['lower_coefficient'] or check['threshold']!=cert['threshold']):
            raise ValueError('uniform obstruction admission binding '+name)
        validation=json.loads((out/('validation_'+name+'.json')).read_text())
        if validation['program']!=candidate['program']:
            raise ValueError('frozen validation program binding '+name)
        last=max(validation['rows'],key=lambda r:r['u'])
        details.append(dict(id=name,source_id=candidate['source_id'],energy_id=candidate['energy_id'],family_id=candidate['family_id'],
            calibration_parent=candidate['u'],calibration_full_price=str(Q(candidate['certificate']['price'])),
            calibration_price_over_u=str(Q(candidate['certificate']['price'])/candidate['u']),
            largest_validation_parent=last['u'],largest_validation_price_over_u=last['price_over_u'],
            largest_validation_price_over_u2=last['price_over_u2'],
            uniform_price_obstruction_coefficient=cert['lower_coefficient'],uniform_price_obstruction_threshold=cert['threshold'],
            fixed_program_has_no_price_bound_at_any_exponent_below_two=True,
            actual_arithmetic_drift_refuted=False,uniform_original_source_bound_proved=False,RH_proved=False))
    totals=test_totals()
    feedback=json.loads((out/'postrun_next_search_input.json').read_text())
    feedback.update(schema='dense-completion-coupled-arithmetic-feedback-v1',
        search_input_is_the_unpaid_bound_not_an_observed_constant=True,
        exact_next_zero_identity=dict(
            schedule='For every squarefree coordinate n<=N, choose integer 0<=K_u(n)<=N and rational geometry weight w_u(n).',
            profile='C_K(m)=floor(K/m)-1[m=1] for K>=1; C_0=0.',
            symmetric_kernel='Z_u(m,n)=(w_u(n)*C_{K_u(n)}(m)+w_u(m)*C_{K_u(m)}(n))/2.',
            identity='sum_(m,n squarefree<=N) mu(m)*mu(n)*Z_u(m,n)=0.',
            argument='For each n, the inner divisor identity sum_m mu(m)*C_{K_u(n)}(m)=0 holds exactly; symmetrization preserves the double sum.',
            exploratory_geometry_schedules=['K_u(n)=n','K_u(n)=min(N,floor(a*n^eta*u^beta)) with arbitrary admitted rational a,eta,beta',
                                            'K_u(n) determined by a cofactor or prime-divisibility partition'],
            signed_data_in_geometry_or_weights_permitted=False,
            required_representation_change='Rebuild complete physical-coordinate or joint pair geometry; K_u(n) generally varies within the old082 feature groups, which cannot be reused by averaging.',
            first_search_filter='Evaluate new identities against the saved artificial moment-null witnesses, then search complete upper certificates and new independent obstructions.',
            why_distinct='The index-dependent profile creates coupled prime/composite cross terms beyond the fixed separable floor-moment roster.',
            this_identity_alone_is_not_a_bound=True),
        requested_positive_outcome='An explicit auxiliary operator plus a proved scale recurrence or uniform price estimate for the complete signed target.',
        controls=['full original kernel binding','all unit, diagonal, actual-prime and composite cross terms',
                  'exact independent certificate checker','work/memory guards before complete geometry allocation',
                  'dependency and noncircularity checks for every residual obligation'],
        formal_theorem_prover_checked=False,uniform_original_source_bound_proved=False,RH_proved=False)
    write(out/'published_next_search_input.json',feedback)
    results=dict(status='PUBLISHED_COMPLETE_DRIFT_SEARCH_AND_UNIFORM_PRICE_OBSTRUCTIONS',
                 science=main_report,rank_obstructions={k:v for k,v in rank_report.items() if k!='rows'},
                 combined_main_and_rank_elapsed_seconds=main_report['elapsed_seconds']+rank_report['elapsed_seconds'],
                 selected_details=details,tests=totals,independent_saved_main_audit=audit['status'],
                 independent_saved_rank_audit=rank_audit['status'],
                 retained_rank_artifact_audit_attempts=['saved_rank_artifact_admission_082.json','saved_rank_artifact_admission_082_attempt002.json'],
                 actual_arithmetic_drift_refuted=False,uniform_original_source_bound_proved=False,RH_proved=False)
    write(out/'published_results.json',results)
    total=sum(counts)+len(RUN.FILES)+len(POST_FILES)
    lines=[]
    for row in details:
        lines.append(row['id']+': calibrationB/u='+format(float(Q(row['calibration_price_over_u'])),'.8g')+
                     '; B(8179)/8179='+format(float(Q(row['largest_validation_price_over_u'])),'.8g')+
                     '; uniformprice lower c='+row['uniform_price_obstruction_coefficient']+
                     ', threshold='+str(row['uniform_price_obstruction_threshold']))
    handoff='''CURRENT CONTINUATION: COMPLETE SIGNED DRIFT CERTIFICATES082

The RH objective remains ACTIVE and unfinished. The authoritative next
machine input is stage082/published_next_search_input.json. This turn has
not proved a uniform originalsource bound, the required signed arithmetic
cancellation, or RH. Earlier081 auxiliary packet proofs remain preserved.

What the detector now does
It directly searches a complete upper bound for
DeltaE(u)=E(u)-(3/2)E(floor(u/2)), E>=R(u)^2,
for both original unfolded kernelsG=M(u//8)-M(u//10)-M(u//4)+M(u//5)
andG+(3547/8192)G(u//3). Every squarefree coordinate throughu//4 remains,
includingunit, actualprimes, diagonal and all prime/composite cross terms.
The selection uses squarefree geometry and exact divisor identities, never
observedmu signs, source values or a saved joint remainder.

Its language includes arbitrary admitted rational powers in profile cuts,
exact zero moment additions frommu*1=delta, delayed energy cross terms,
nonnegative Gram additions and a complete diagonally dominant upper-price
certificate. A floating LP proposes coefficients. Independent exact checks
reconstruct full geometry and verify the finite upper prices. Exact dual
certificates independently bound how low this grammar's price can go.

Observed finite result
24LP programs:2sources,3energies,4full/linear profile families, discoveryu1024.
All24 admitted, with48 discovery upper checks includingzero baselines and
24 exact price-dual checks. Eight frozenwinners passed48 new geometry checks
at1722,1787,3588,3850,6444,8179. No new signedmu data/horizon was queried.
Some constants improve, but the certified price still grows quadratically.
Finite optimality does not supply the missing all-scale growth theorem.

The stronger detector discovery
An exact rational interval search constructs artificial sign averages whose
registered floor moments and delayedsource moments vanish, while the current
source moment grows linearly. Independent interval/nullspace/population/floor
checks turn this into B(u)>=c*u^2, c>0, beyond an explicit scale threshold.
All24pilot profile/energy programs plus12sublinear ablations have independent
uniform price-obstruction certificates. Thresholds range921600..8294400.
No signed arithmetic values or PNT are used; an elementary squarefree count
bound pays the interval populations. These are reviewed elementary arguments
with independently checked exact certificates, not formal theorem-prover proofs.

This rules out the requiredB(u)<=C*u inside these fixed-profile completions,
even if their coefficient boxes are enlarged. It is a limitation of the
relaxation: its artificial sign averages need not be actualMobius. It does
not refute the true signed drift bound, these arithmetic identities, or RH.
The independently reviewed general argument extends to every fixed finite
rational floor-profile roster in this same group-box completion language;
the36 saved certificates are effective concrete instances of that argument.

Selected rows (all have uniform grammar-price obstructions)
'''+ '\n'.join(lines)+f'''

Next search, already exported as typed mathematical input
Use the exact unpaid full bound and the discovered moment-null witnesses.
Search coupled identities with coordinate-dependent divisor cutsK_u(n),
weighted by geometryw_u(n): symmetricZ(m,n)=[w(n)C_K(n)(m)+w(m)C_K(m)(n)]/2.
Its Mobius quadratic form is exactlyzero by applyingmu*1 separately for
eachn. This is a next grammar template, not yet implemented or a bound.
Its pair geometry must be rebuilt: the current feature groups cannot hide
within-group index dependence. Growing multiplicative/cofactor constraints
and their uniform norm/scale recurrences are additional candidate mechanisms.
Require an explicit full-target certificate and a proved uniform bound;
recoveringmu numerically from all divisor relations would not suffice.
Further fixed floor moments, coefficient tuning, or positive Grams alone
cannot evade the current obstruction. Actual prime information across scales
remains an explicit requirement for the next arithmetic construction.

Validation/resources/provenance
Main search elapsed{main_report['elapsed_seconds']:.3f}s on3workers,
combined main+rankfollowup{main_report['elapsed_seconds']+rank_report['elapsed_seconds']:.3f}s,
sampled aggregateRSS{main_report['sampled_aggregate_peak_rss_bytes']}B,
conservativeprocess-peak sum{main_report['conservative_process_peak_sum_bytes']}B.
Authorized16GiB/7200s,120s perLP; no limits approached.
Main constructorwork{main_report['constructor_operations']}; independent
discovery/validationwork{main_report['independent_discovery_operations']}/{main_report['independent_validation_operations']}.
Rankfollowup newwork{rank_report['new_constructor_operations']}, checkerwork{rank_report['independent_price_checks']};
24prior geometry-discovery integrations were reused rather than replayed.
{totals['distinct_tests']}distinct tests,{totals['test_executions']}executions,
{totals['successful_test_executions']}pass,{totals['failed_test_executions']}retained failed expectation corrected.
Independent producer/resource, main saved-artifact and rankcertificate audits pass.
The first rank saved-artifact audit had a receipt-parser bug; its failed
attempt is preserved separately, and the corrected second audit passed.
Sol6.1 agents handled substantial parallel checker, proof and artifact work.
No oldscience/test reruns and no hashes. Preserve{sum(counts)}older+
{len(RUN.FILES)}pre-run082+{len(POST_FILES)}postrun082={total}frozenfiles by directbytes.
Historical archived handoffs remain intact; root continuation pointers advance.
'''
    for path in [out/'HANDOFF.txt',root/'MOBIUS_DENSE_COMPLETION_HANDOFF.txt']:
        with path.open('x') as file:
            file.write(handoff)
    previous=json.loads((RUN.PRIOR.OUT/'publication_integrity.json').read_text())
    pointers=previous['continuation_pointers_updated']+['MOBIUS_DENSITY_PACKET_HANDOFF.txt']
    for name in pointers:
        (root/name).write_text('Latest continuation: MOBIUS_DENSE_COMPLETION_HANDOFF.txt\n\n'
            '082 searches complete signed drift bounds and independently checks exact prices.\n'
            'The detector invented36 certified all-scale obstructions for fixed-profile completion prices.\n'
            'Required arithmetic bound remains open; next grammar must escape the saved witnesses.\n'
            'Use stage082/published_next_search_input.json; preserve all archived evidence.\n')
    snapshot=out/'postrun_snapshot';snapshot.mkdir()
    for name,content in frozen.items():
        (snapshot/name).write_bytes(content)
        if (root/name).read_bytes()!=content:
            raise ValueError('postrun source changed during publication '+name)
    write(out/'publication_integrity.json',dict(status=results['status'],prior_frozen_counts=counts,
        pre_run_files=RUN.FILES,postrun_files=POST_FILES,total_frozen_files=total,tests=totals,
        continuation_pointers_updated=pointers,historical_handoffs_unchanged=True,hashes_used=False,RH_proved=False))
    RUN.validate_parent()
    print(json.dumps(dict(status=results['status'],finite_programs=24,uniform_price_obstructions=36,
                         total_frozen_files=total,tests=totals,uniform_original_source_bound_proved=False)))


if __name__=='__main__':
    main()
