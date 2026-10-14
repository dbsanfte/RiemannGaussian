"""Publish discovered identity banks, finite bounds and explicit uniform leaves."""
import json
import os
import time
from fractions import Fraction as Q
import run_mobius_annihilator_085 as RUN
from run_fractional_prime_kernel_051 import write


def read(path):return json.loads(path.read_text())


def post_files():
    names=['audit_mobius_annihilator_085.py','MOBIUS_ANNIHILATOR_INDEPENDENT_REVIEW_085.txt',
           'audit_mobius_annihilator_artifacts_085.py','MOBIUS_ANNIHILATOR_ARTIFACT_REVIEW_085.txt',
           'MOBIUS_ANNIHILATOR_UNIFORM_TARGET_085.txt','publish_mobius_annihilator_085.py']
    names += [p.name for pattern in ['mobius_annihilator_independent_audit_085*.json',
                                    'mobius_annihilator_runner_preflight_audit_085*.json']
              for p in sorted(RUN.ROOT.glob(pattern))]
    if len(names)!=len(set(names)):raise ValueError('duplicate085 publication source')
    return names


def test_totals():
    result=dict(distinct_tests=0,test_executions=0,passed_test_executions=0,failed_test_executions=0)
    for name in ['mobius_annihilator_search_085_development.json','mobius_annihilator_checker_085_development.json']:
        d=read(RUN.ROOT/name)
        if d['status']!='PASS':raise ValueError('unfinished085 tests '+name)
        result['distinct_tests']+=d['distinct_tests']
        for a in d['attempts']:
            count=a['tests'];passed=a.get('passed',count if a.get('exit_code')==0 else None)
            if passed is None:raise ValueError('unaccounted085 test attempt')
            result['test_executions']+=count;result['passed_test_executions']+=passed
            result['failed_test_executions']+=count-passed
    return result


def uniform_target(candidate):
    return dict(id=candidate['id']+'_uniform_annihilator_price',source_id=candidate['source_id'],
        program=candidate['program'],outer_certificate=candidate['outer_certificate'],
        learned_symbolic_bank=candidate['banks']['adaptive'],
        conditional_RH_target=RUN.PRIOR.TARGET.compile_target(candidate['program'],RUN.PRIOR.transfer(candidate['source_id'])),
        domain='every integer u>=1 and every integer j>=1, q_j=1+1/j',
        complete_residual='R(u)=P^T(A(u)-O(u)-Gold(u))P; unchanged paid outer block and original Gram removal',
        exact_identity='V_j(u)^T y(u)=0 by complete Mobius divisor convolution and known unit/prime anchoring',
        required_construction='symbolic complete V_j(u), symmetric rational S_j(u), positive factor L_j(u)',
        required_price='B(R(u)+V_j(u)S_j(u)V_j(u)^T+L_j(u)L_j(u)^T)<=C_j*u^(1+1/j)',
        Boolean_price='signed trace plus twice the absolute sum of all off-diagonal entries',
        constants='C_j finite, nonnegative, independent of u; may depend on j',
        full_drift='DeltaE(u)<=Astar*u+the complete residual price; outer term remains paid separately',
        recurrence='E(u)<=r*E(floor(u/2))+(Astar+C_j)*u^(1+1/j), E(0)=0, r=3/2',
        source_transfer='either fixed invertible084 source with every positive j suffices for RH',
        paid_leaves=['complete divisor identity for all u','exact prime/unit projection','unchanged uniform whole outer control',
                     'positive energy/source domination and conditional dilation transfer'],
        unpaid_leaves=[dict(id='symbolic_coefficient_and_positive_factor_construction',status='UNPAID'),
                       dict(id='uniform_complete_price_growth_for_every_j',status='UNPAID')],
        permitted_next_search='new structured identities, partner vectors, scale recurrences and their intermediate lemmas; preserve full signed arithmetic costs',
        finite_fitted_coefficients_do_not_pay_uniform_leaves=True,uniform_remaining_bound_proved=False,RH_proved=False)


def main():
    started=time.monotonic();root,out=RUN.ROOT,RUN.OUT
    if (out/'publication_integrity.json').exists():raise FileExistsError('preserve published085')
    counts=RUN.validate_parent()
    for name in RUN.FILES:
        if (root/name).read_bytes()!=(out/'source_snapshot'/name).read_bytes():raise ValueError('frozen085 source changed '+name)
    report=read(out/'report.json');audit=read(out/'independent_annihilator_artifact_audit_085.json')
    if report['status']!='COMPLETE_ADAPTIVE_ANNIHILATOR_SEARCH':raise ValueError('incomplete085 science')
    if audit['status']!='VERIFIED_ANNIHILATOR_ARTIFACT_BINDING':raise ValueError('independent085 artifact admission required')
    candidates=read(out/'frozen_candidates.json')['candidates'];rows=[];calibration=[];bank_diagnostics=[];quality=[]
    for outcome in report['outcomes']:
        d=read(out/('bound_'+outcome['id']+'.json'))
        row={k:d.get(k)for k in ['id','candidate_id','source_id','family_id','mode','stage','u','status','error',
            'price_over_u','price_over_u2','identity_rank','active_identity_columns','solver_status','solver_seconds',
            'float_objective_over_u','factor_fallback','rejected_square_price','diagnostics','frozen_growth_tests']}
        row['certificate_file']='bound_'+outcome['id']+'.json';rows.append(row)
        if d['status']=='EXACT_ANNIHILATOR_SQUARE_PROPOSAL':
            cert=d['certificate'];admission=d['admission'];price=Q(cert['price'])
            trace_cost=abs(Q(admission['identity_trace']))+Q(admission['factor_trace'])
            quality.append(dict(id=d['id'],stage=d['stage'],u=d['u'],
                max_absolute_signed_coefficient=str(max([abs(Q(v))for r in cert['identity_matrix']for v in r]+[Q(0)])),
                sum_identity_and_factor_trace_magnitudes=str(trace_cost),
                trace_magnitude_over_max_one_absolute_price=str(trace_cost/max(Q(1),abs(price))),
                float_objective_over_u=d['float_objective_over_u'],exact_price_over_u=d['price_over_u'],
                scope='representation and certificate quality diagnostic only; no optimum, obstruction or coefficient-growth theorem'))
    for c in candidates:
        adapt=read(out/('bound_'+c['id']+'_adaptive_1024.json'));base=read(out/('bound_'+c['id']+'_grammar_order_1024.json'))
        old=Q(c['certificate']['price']);a=Q(adapt['certificate']['price'])if adapt['status']=='EXACT_ANNIHILATOR_SQUARE_PROPOSAL'else None
        b=Q(base['certificate']['price'])if base['status']=='EXACT_ANNIHILATOR_SQUARE_PROPOSAL'else None
        calibration.append(dict(id=c['id'],saved084_price_over_u=str(old/1024),
            adaptive_price_over_u=str(a/1024)if a is not None else None,baseline_price_over_u=str(b/1024)if b is not None else None,
            adaptive_improves_saved084=a<old if a is not None else None,
            adaptive_beats_baseline=a<b if a is not None and b is not None else None,
            adaptive_exact_reduction_from_saved084=str(old-a)if a is not None else None))
        selection=read(out/('bank_'+c['id']+'.json'));chosen=selection['choices']['adaptive']
        scores={r['id']:r for r in chosen['scores']};selected=[scores[i]for i in chosen['selected_ids']]
        bank_diagnostics.append(dict(id=c['id'],bank=c['banks']['adaptive'],descriptor_ids=chosen['selected_ids'],
            generated=len(selection['generated']),training_representatives=len(selection['representatives']),
            training_witnesses_violating_bank=[u for i,u in enumerate(chosen['parents'])
                  if any(Q(r['normalized_violation_by_parent'][i])>0 for r in selected)],
            prospective_score_fraction_bits=chosen['prospective_score_fraction_bits'],
            scope='exact violations disqualify these old witnesses as lower bounds for unrestricted signed identity controls; no new dual supplied'))
    tests=test_totals();post=post_files();frozen={name:(root/name).read_bytes()for name in post}
    feedback=dict(schema='adaptive-annihilator-uniform-target-feedback-v1',previous_goal_turn='PROGRESS',
        finite_candidates=[dict(id=c['id'],program=c['program'],bank=c['banks']['adaptive'])for c in candidates],
        executable_uniform_targets=[uniform_target(c)for c in candidates],
        learned_banks=bank_diagnostics,finite_bound_diagnostics=rows,calibration_comparisons=calibration,
        certificate_quality_diagnostics=quality,
        growth_hypotheses_by_j=report['growth_hypotheses_by_j'],
        prior_search_input=str(RUN.PRIOR.OUT/'published_next_search_input.json'),
        new_bound_language='witness-selected symbolic divisor identities; arbitrary symmetric signed VSV^T; positive LL^T completion on the full anchored remainder',
        discovery='detector selects generic rational cutoff formulas from counterexample violations and synthesizes signed coefficients and positive factors',
        proof_rule_origin='divisor convolution, congruence, positive squares and Boolean majorization supplied analytically; exact independent checker admits instantiated bounds',
        known_arithmetic='unit plus every actual prime sign; complete divisor constraints; every unknown squarefree composite and cross pair retained',
        novelty_scope='earlier full divisor Gram controls already existed; this stage adds adaptive parameterized selection and unrestricted signed bank products to the current complete remainder',
        validation_scope='banks/operators frozen, new S and L synthesized at each held-out outcome geometry; not fixed coefficients or a uniform construction',
        preflight_geometry_disclosure='seeded parent values predicted before bank freeze; scientific outcomes held out, no redraw',
        baseline_scope=report['baseline_scope'],
        obstruction_scope='old084 positive-factor lower witnesses and duals cannot exclude this enlarged grammar unless annihilator compatibility is exact',
        next_language_priority='search symbolic coefficient/factor or complete scale-transfer constructions, using the exact unpaid price/correlation estimate as a new target',
        concrete_next_construction=dict(
            grammar='mixed exact-zero products (V W^T+W V^T)/2 with structured arithmetic partner columns W',
            exact_projection_ablation='on exact independent columns let M=(V^T V)^(-1), P=V M V^T, Pi=I-P; replace R by Pi R Pi in the SAME original Boolean coordinates',
            partner_identity='W=-2 R V M+V M V^T R V M gives (V W^T+W V^T)/2=Pi R Pi-R',
            rationale='V S V^T alone cannot cancel generic cross terms between the constrained directions and their orthogonal complement; mixed products can',
            ideal_value_caveat='with unrestricted coefficients both diagonal-majorant SDPs have the same dual: X PSD, diag(X)=1, X V=0. Mixed controls add no arithmetic information or ideal finite SDP improvement by themselves',
            structural_scope='seek finite attainment, simpler exact constructions and a provable coefficient/trace schedule; do not present this alone as new cancellation',
            rank_guard='exact active-column selection, explicit rank-zero case and prospective inverse/coefficient bit gates',
            unpaid='uniform complete price/trace growth; controlling Gram inverse and rank changes when used in a uniform norm proof',
            not_yet_run=True,no_uniform_price_conclusion=True),
        reviewed_auxiliary_lemma=dict(
            form='for N>=2,1<=K=N-L<=N, balanced D_K has norm ||P_anchor^T D_K||_1 <=2 L H_N+sum_(t=N-L+1)^N(tau(t)-1)',
            growth='<=2 L H_N+C_epsilon L N^epsilon for every epsilon>0, with C_epsilon independent of N,L',
            implication='joint identity correction entrywise norm <=sum_(i,j)|S_ij| norm(v_i)_1 norm(v_j)_1; coefficient growth remains explicit',
            scope='reviewed elementary bound on auxiliary identity columns only; not a bound on the complete signed remainder',
            review_file='MOBIUS_ANNIHILATOR_UNIFORM_TARGET_085.txt'),
        next_uniform_mechanism=dict(
            name='paid head with negative semidefinite bulk',
            partition='on COMPLETE RAW squarefree coordinates, head n<=min(N,ceil(u^eta_j)); 0<eta_j<=1/j',
            search_target='W=R_raw+D S D^T, or a checked mixed zero correction; prove W_bulk,bulk<=0 for all u,j',
            completion='Q_raw is minus the complete bulk block, zero elsewhere; only use after its PSD has been proved',
            paid_geometry='balanced floor entries have magnitude<1; fixed source/operator coefficients give a uniform raw entry bound; head pairs cost O(u^(1+eta_j))',
            correction_cost='use complete identity-column norm and explicit coefficient-growth bounds, retaining every head/bulk pair',
            projection='only after the raw partition, apply full known-prime congruence; Q remains PSD',
            applicability_guard='verify balanced old cuts and uniformly bounded weights, plus every proposed correction growth schedule',
            unpaid_leaves=['uniform negative semidefinite bulk theorem','symbolic signed coefficients/partners with a paid growth schedule'],
            scope='reviewed sufficient proof mechanism; not established for any learned bank; a countervector refutes this mechanism only'),
        required_information_diagnostic=dict(
            compatible_dual='X exact rational PSD, diag(X)=1, X V=0; tr(R X) lower-bounds both unrestricted zero-control grammars',
            compatible_Boolean_witness='s_i in {-1,1}, anchor+1, V^T s=0 exactly; s^T R s is a simpler exact lower witness',
            proof_scope='finite grammar obstruction only; approximate compatibility is insufficient',
            response='if a compatible witness excludes a target, add genuinely new arithmetic constraints or change the operator/proof mechanism; coefficient precision cannot resolve it',
            not_yet_supplied=True),
        progress_criterion='uniform stronger exponent, proved complete recurrence or reduction to independently paid estimates; finite constants are secondary',
        candidate_quality_rule='rank exact admitted bounds; preserve a verified incumbent at each geometry; never promote a small floating objective or hide a worse reconstructed price',
        uniform_design_review='MOBIUS_ANNIHILATOR_UNIFORM_TARGET_085.txt',
        forbidden_shortcuts=['infer all-u or all-j bounds from finite samples','recover all unknown signs with the full prefix bank and rename the original scalar as a proof',
            'pointwise-weight an annihilator without a separate convolution identity','price orthonormal nullspace coordinates as Boolean',
            'drop paid outer costs, original negative Gram or prime/composite cross terms','reuse old unconstrained duals for signed identity controls'],
        uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False,hashes_used=False)
    write(out/'published_next_search_input.json',feedback)
    results=dict(status='PUBLISHED_ADAPTIVE_ANNIHILATOR_BOUNDS_AND_UNIFORM_TARGETS',report=report,
        artifact_audit=audit,tests=tests,calibration_comparisons=calibration,learned_banks=bank_diagnostics,
        certificate_quality_diagnostics=quality,
        finite_bound_diagnostics=rows,uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False)
    write(out/'published_results.json',results)
    lines=['CURRENT CONTINUATION: ADAPTIVE EXACT ARITHMETIC IDENTITIES085','',
        'The RH objective remains active and unfinished. Authoritative machine input:',
        'stage085/published_next_search_input.json, beside published_results.json.',
        'No all-scale signed remainder bound or RH proof has been obtained.','',
        'The detector now learns symbolic identities from its earlier bound obstructions.',
        'For each of eight frozen084 operators, it enumerated7740 generic rational',
        'cutoff rules and1184 distinct training cut/balance forms, then selected eight.',
        'Training uses exact normalized violations by saved artificial witnesses,',
        'without querying unknown composite Mobius signs or complete source values.',
        'Root exponents include arbitrary rationals within prospective bit budgets;',
        'the finite enumeration heights12/8 are resource bounds, not a root whitelist.','',
        'For complete exact annihilator columns V, actual V^T y=0. The bound grammar',
        'allows arbitrary symmetric signed S plus positive LL^T, giving',
        ' y^T R y <= B(R+VSV^T+LL^T), B=trace+2sum_abs_offdiagonal.',
        'R=P^T(A-O-Gold)P retains every physical composite and cross term. Paid',
        'outer O is unchanged. Exact independent verification checks every entry.',
        'Earlier divisor-Gram controls are acknowledged; no historical novelty claim.','',
        'All banks/operators froze before calibration and new geometry outcomes.',
        'Preflight predicted the seeded parent VALUES; outcomes remained held out.',
        f"Calibration: {report['calibration_admitted']}/{report['calibration_rows']} admitted, including grammar-order baselines.",
        f"New parents: {report['new_geometry_parents']}; admitted {report['new_auxiliary_admitted']}/{report['new_auxiliary_rows']}.",
        'New S and L were synthesized at each geometry. These are new auxiliary',
        'searches, not an all-scale construction or fixed-factor validation.',
        'Baseline comparison covers calibration only; saved084 used a different',
        'solver budget. All failures, warnings and outcomes remain saved.','',
        'Calibration exact bound/u (decimal display):']
    for c in calibration:
        show=lambda x:'FAILED'if x is None else format(float(Q(x)),'.7g')
        lines.append(c['id']+': saved084='+show(c['saved084_price_over_u'])+', adaptive='+show(c['adaptive_price_over_u'])+', baseline='+show(c['baseline_price_over_u']))
    lines += ['', f"Adaptive banks beat the grammar-order baseline in {sum(c['adaptive_beats_baseline']is True for c in calibration)}/{len(calibration)} calibration cases.",
        'This is mixed evidence; large opposing identity/square traces can give',
        'poor exact prices even when the floating objective looks favorable.',
        'Exact coefficient/trace amplification diagnostics are saved for every',
        'admitted row. Do not promote floating objectives or overwrite worse trials.',
        'Fresh growth tests retain084 constants without fitting: '+str(report['growth_hypotheses_by_j']),
        'Old artificial witnesses which violate V no longer lower-bound this',
        'unrestricted signed grammar. No new085 grammar dual has been supplied.','',
        'The unpaid target is a symbolic construction with, for EVERY j>=1,u>=1,',
        ' B(R+V_j S_j V_j^T+L_j L_j^T)<=C_j*u^(1+1/j), C_j independent of u.',
        'The paid outer term, energy recurrence and fixed-source dilation inverse',
        'then supply the conditional RH route. Finite fits do not pay that leaf.',
        'See MOBIUS_ANNIHILATOR_UNIFORM_TARGET_085.txt for the next proof-search',
        'construction and explicit residual obligations. Preserve all signed costs.','',
        'Concrete next language: mixed zero products (V W^T+W V^T)/2. Unlike',
        'V S V^T alone, these can cancel cross terms between constrained modes',
        'and their complement exactly. With P=V(V^T V)^(-1)V^T on independent',
        'columns, (I-P)R(I-P)-R is such a product. All pricing must still use',
        'the original Boolean coordinates. This extension has not yet been run;',
        'its complete uniform price bound and any inverse-conditioning costs',
        'remain unpaid. Both unrestricted zero-control SDPs have the SAME ideal',
        'finite optimum: their exact dual requires X>=0, diag(X)=1, X V=0.',
        'Mixed controls alone add no arithmetic information. Their purpose is a',
        'finite, structured proof construction. Also search exact compatible duals',
        'or Boolean witnesses, so an information limitation triggers new arithmetic',
        'constraints rather than repeated coefficient or precision tuning.','',
        'An elementary auxiliary lemma controls balanced near-endpoint identity',
        'norms by2*L*H_N+sum_(N-L<t<=N)(tau(t)-1). Its all-scale divisor bound',
        'is proved in the review. This pays an identity-column norm estimate;',
        'it does not pay the complete arithmetic remainder or coefficient growth.','',
        f"Verification: {tests['distinct_tests']} distinct focused tests, {tests['test_executions']} executions, {tests['passed_test_executions']} passed.",
        'Preflight found an empty-matrix shape bug and witness-status mismatch;',
        'both were fixed before science. Initial failed audit and passing follow-up',
        'are retained. Exact scoring/resource/helper guards were strengthened.',
        'Independent saved-artifact audit admitted the complete new experiment.',
        f"Main elapsed {report['elapsed_seconds']:.3f}s; sampled aggregateRSS {report['sampled_aggregate_peak_rss_bytes']}B;",
        f"conservative process-peak sum {report['conservative_process_peak_sum_bytes']}B.",
        'Three workers, one native thread each; limits16GiB and7200 seconds.',
        'Counters cover instrumented geometry/matrix/scoring work, not solver',
        'instructions or symbolic exponent comparisons. No hashes or old reruns.',
        f"All {sum(counts)} previous frozen files, {len(RUN.FILES)} scientific and {len(post)} postrun sources preserved.",
        'Sol6.1 agents performed substantial mathematical and independent reviews.']
    handoff='\n'.join(lines)+'\n';(root/'MOBIUS_ANNIHILATOR_HANDOFF.txt').write_text(handoff)
    (out/'handoff.txt').write_text(handoff)
    old_integrity=read(RUN.PRIOR.OUT/'publication_integrity.json')
    pointers=old_integrity['continuation_pointers_updated']+['MOBIUS_COUPLED_SQUARE_HANDOFF.txt']
    for name in pointers:
        (root/name).write_text('CURRENT CONTINUATION: MOBIUS_ANNIHILATOR_HANDOFF.txt\n\n'
            '085 learns exact arithmetic identity banks from artificial bound obstructions\n'
            'and searches signed controls on the complete remainder. Uniform RH-relevant\n'
            'price growth remains unpaid. See stage085/published_next_search_input.json.\n'
            'Preserve historical evidence; no all-scale proof is claimed.\n')
    (out/'postrun_snapshot').mkdir()
    for name,content in frozen.items():
        (out/'postrun_snapshot'/name).write_bytes(content)
        if (root/name).read_bytes()!=content:raise ValueError('postrun085 source changed '+name)
    RUN.validate_parent();RUN.POOL.stage_check(started,[os.getpid()])
    write(out/'publication_integrity.json',dict(status=results['status'],prior_frozen_counts=counts,pre_run_files=RUN.FILES,
        postrun_files=post,total_frozen_files=sum(counts)+len(RUN.FILES)+len(post),tests=tests,
        continuation_pointers_updated=pointers,historical_handoffs_unchanged=True,
        publication_elapsed_seconds=time.monotonic()-started,source_bytes_preserved=True,hashes_used=False,RH_proved=False))
    print(json.dumps(dict(status=results['status'],calibration_admitted=report['calibration_admitted'],
        fresh_admitted=report['new_auxiliary_admitted'],tests=tests,uniform_remaining_bound_proved=False)))


if __name__=='__main__':main()
