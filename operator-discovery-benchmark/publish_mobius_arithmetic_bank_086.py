"""Publish exact finite arithmetic information gains and unpaid uniform targets."""
import copy
import json
import os
import time
from fractions import Fraction as Q
import run_mobius_arithmetic_bank_retry_086 as LAUNCH
RUN=LAUNCH.RUN
from run_fractional_prime_kernel_051 import write


def read(path):return json.loads(path.read_text())


def development_totals():
    c=read(RUN.ROOT/'mobius_arithmetic_bank_checker_086_development.json')
    w=read(RUN.ROOT/'mobius_bank_witness_086_development.json')
    m=read(RUN.ROOT/'mobius_mixed_zero_development_attempts_086.json')
    if c['status']!='PASS'or w['test_runs'][-1]['status']!='OK'or m['runs'][-1]['status']!='OK':raise ValueError('unfinished086 focused tests')
    rows=w['test_runs']+m['runs']
    result=dict(distinct_focused_tests=c['distinct_tests']+w['test_runs'][-1]['tests']+m['runs'][-1]['tests'],
                focused_method_executions=c['test_method_executions']+sum(r['tests']for r in rows),
                passed_focused_executions=c['passed_executions']+sum(r['passed']for r in rows),
                failed_focused_executions=c['retained_failed_executions']+sum(r['tests']-r['passed']for r in rows),
                retained_loader_errors=c['retained_loader_errors'])
    attempts=[json.loads(line)for line in (RUN.ROOT/'mobius_arithmetic_bank_audit_086_development.jsonl').read_text().splitlines()if line]
    coverage={}
    for attempt in attempts:
        for test in attempt.get('tests',[])+attempt.get('runner_tests',[]):coverage[test['name']]=test['status']
    if not coverage or any(status!='PASS'for status in coverage.values()):raise ValueError('unfinished independent086 prospective audit tests')
    result['prospective_audit_attempts']=len(attempts)
    result['prospective_audit_failed_attempts']=sum(a['status']!='PASS'for a in attempts)
    result['prospective_audit_distinct_checks']=len(coverage)
    result['initial_native_import_premise_was_missing']=True
    launch=read(RUN.ROOT/'mobius_arithmetic_launch_086_development.json')
    if launch['status']!='PASS':raise ValueError('unfinished corrected native launch regression')
    result['corrected_launch_regression']=dict(status=launch['status'],attempts=len(launch['attempts']),
                                               distinct_tests=2,real_tiny_MILP_proposals=12,spawned_workers=3)
    result['earlier_failures_retained']=True
    return result


def uniform_targets(candidates):
    old=read(RUN.PRIOR.OUT/'published_next_search_input.json')['executable_uniform_targets'];by_id={t['id']:t for t in old};targets=[]
    for c in candidates:
        t=copy.deepcopy(by_id[c['id']+'_uniform_annihilator_price'])
        t.update(id=c['id']+'_uniform_arithmetic_bank_price',learned_symbolic_banks=c['banks'])
        t.pop('learned_symbolic_bank',None)
        t.update(exact_identity='V_j(u)^T y(u)=0 by complete divisor convolution and prime-cofactor mu(pm)+mu(m)=0 with p prime,p not dividing m',
            required_construction='symbolic complete typed V_j(u), rational partners W_j(u), positive factor L_j(u)',
            required_price='B(R(u)+(V_j(u)W_j(u)^T+W_j(u)V_j(u)^T)/2+L_j(u)L_j(u)^T)<=C_j*u^(1+1/j)',
            paid_new_leaves=['all-u divisor and prime-cofactor identity rules with complete anchoring'],
            finite_information_gain_scope='exact separating witnesses prove increased bank span only at recorded geometry',
            source_weight_scope='fixed source-weighted rows only use a bounded set of primes; weight-one rows allow growing primes',
            unpaid_leaves=[dict(id='uniform_symbolic_partner_and_positive_factor_construction',status='UNPAID'),
                          dict(id='uniform_complete_price_growth_for_every_j',status='UNPAID')],
            uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False)
        targets.append(t)
    return targets


def main():
    started=time.monotonic();root,out=RUN.ROOT,RUN.OUT
    if (out/'publication_integrity.json').exists():raise FileExistsError('preserve published086')
    counts=RUN.validate_parent()
    for name in RUN.FILES:
        if (root/name).read_bytes()!=(out/'source_snapshot'/name).read_bytes():raise ValueError('changed086 source '+name)
    report=read(out/'report.json');audit=read(out/'independent_arithmetic_bank_artifact_audit_086.json')
    if report['status']!='COMPLETE_COUNTEREXAMPLE_ARITHMETIC_BANK_SEARCH':raise ValueError('incomplete086 experiment')
    if audit['status']!='VERIFIED_ARITHMETIC_BANK_ARTIFACT_BINDING':raise ValueError('independent086 artifact audit required')
    candidates=read(out/'frozen_candidates.json')['candidates'];bounds=[];witnesses=[];comparisons=[];trajectories=[]
    for entry in report['outcomes']:
        r=read(out/('bound_'+entry['id']+'.json'))
        bounds.append(dict(**{k:r.get(k)for k in ('id','candidate_id','mode','stage','u','status','price_over_u',
                                                 'selected_attempt','float_objective_over_u','frozen_growth_tests','error','witness_file')},
                           price=r.get('certificate',{}).get('price'),certificate_file='bound_'+entry['id']+'.json'))
    for path in sorted(out.glob('witness_*.json')):
        r=read(path);ok=RUN.admitted_lower(r)
        witnesses.append(dict(id=r['id'],candidate_id=r['candidate_id'],u=r['u'],status=r['status'],
            bank=r['bank'],admitted=ok,lower_bound=r.get('certificate',{}).get('lower_bound')if r.get('certificate')else None,
            excludes_frozen_target=r.get('excludes_frozen_target')if ok else None,
            certificate_file=path.name,artificial_signs_not_actual_Mobius=True))
    for c in candidates:
        learned=read(out/('bank_'+c['id']+'.json'))
        if learned['status']=='COMPLETE_ARITHMETIC_ENRICHMENT':
            common=[]
            for mode,arm in learned['arms'].items():
                steps=[]
                for step in arm['steps']:
                    selected=step['choice']['selected']
                    steps.append(dict(iteration=step['iteration'],status=step['status'],witness_file=step['witness_file'],
                                      descriptor=selected['descriptor']if selected else None,
                                      selected_score=step['choice']['selected_score']))
                trajectories.append(dict(id=c['id'],mode=mode,bank=arm['bank'],steps=steps,
                    added_count=arm['added_count'],stop_reason=arm['stop_reason'],
                    final_witness_file=arm['final_witness_file'],final_target_excluded=arm['final_target_excluded']))
                if steps:common.append(dict(mode=mode,first_step=steps[0]))
            initial=next(r for r in bounds if r['candidate_id']==c['id']and r['mode']=='initial')
            final=[r for r in bounds if r['candidate_id']==c['id']and r['stage']=='training'and r['mode']!='initial']
            comparisons.append(dict(id=c['id'],initial_price=initial['price'],common_initial_extensions=common,
                final=[dict(mode=r['mode'],price=r['price'],strictly_improves_initial=(Q(r['price'])<Q(initial['price']))if r['price']is not None and initial['price']is not None else None)for r in final],
                scope='same original operator/geometry; exact initial bound retained by zero partners; later enrichment arms may follow different witnesses'))
    tests=development_totals();targets=uniform_targets(candidates)
    active_witness_files={t['final_witness_file']for t in trajectories}
    active_witness_files.update(b['witness_file']for b in bounds if b['stage']=='validation'and b['witness_file'])
    feedback=dict(schema='counterexample-arithmetic-information-feedback-v1',previous_goal_turn='PROGRESS',
        executable_uniform_targets=targets,finite_bound_diagnostics=bounds,compatible_witnesses=witnesses,
        learned_trajectories=trajectories,training_comparisons=comparisons,
        prior_search_input=str(RUN.PRIOR.OUT/'published_next_search_input.json'),
        discovery='the detector searches exact-compatible artificial counterexamples and selects identities that separate them; new upper controls are independently admitted',
        all_scale_proof_rules='complete divisor convolution and prime-cofactor multiplicativity supply typed exact-zero identities; PSD factors and complete Boolean pricing supply the bound rule',
        detector_choices='fractional cutoff formulas, cutoff domains, source/constant weights, current-witness information gain, rational mixed partners and positive factors',
        proof_rule_origin='analytically supplied identity/admission rules; formula selection and finite auxiliaries are searched',
        scientific_scope='all selected identities are valid for all u; their recorded rank gains and bounds are finite. No uniform complete price or signed source bound is proved',
        actual_prime_scope='weight-one prime/cofactor rows include growing actual prime rosters; fixed source-weighted rows use bounded prime rosters',
        zero_control_scope='unchanged-bank mixed controls and unrestricted VSV^T have the same ideal SDP value; only justified added constraints supply new bank information',
        obstruction_scope='an exact compatible artificial lower witness excludes a specified finite C1,j target within this fixed-operator grammar. It does not refute a different constant, asymptotic bound, or RH',
        missing_witness_scope='failure to find a compatible witness proves neither feasibility of the target price nor optimality of an upper certificate',
        launch_correction=dict(aborted_attempt=str(LAUNCH.ABORTED_OUT),
            reason='inherited imports reset environment threads to2; guard declined every initial MILP',
            corrected='enforce environment and actual native pools after full imports and in spawned workers',
            all_failed_artifacts_and_sources_preserved=True,no_fresh_parent_redraw=True,arithmetic_policy_unchanged=True),
        next_search_input=[dict(candidate_id=w['candidate_id'],u=w['u'],bank=w['bank'],witness_file=w['certificate_file'],
            missing_estimate='complete residual price <=C_j*u^(1+1/j), all u and every j',
            action='search an identity, pairing, structured partner or operator change that controls this admitted obstruction and has a symbolic all-scale growth argument')
            for w in witnesses if w['admitted']and w['excludes_frozen_target']and w['certificate_file']in active_witness_files],
        next_input_scope='only terminal training and frozen-bank validation obstructions; earlier eliminated witnesses remain in history',
        unresolved_uniform_leaves=['uniform symbolic partner/factor or complete scale-recurrence construction',
                                  'complete signed price including all prime/composite cross terms',
                                  'constants independent of u for every j, including coefficient and conditioning costs'],
        avoid=['interpreting artificial signs as actual Mobius values','finite fits as all-u or all-j proofs',
               'treating a solver timeout as no compatible witness','dropping signed cross terms or pricing rotated coordinates as Boolean',
               'recovering all unknown signs and renaming the original scalar as a bound'],
        uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False,hashes_used=False)
    results=dict(status='PUBLISHED_COUNTEREXAMPLE_ARITHMETIC_INFORMATION_AND_BOUNDS',report=report,artifact_audit=audit,
                 tests=tests,training_comparisons=comparisons,finite_bound_diagnostics=bounds,
                 compatible_witnesses=witnesses,learned_trajectories=trajectories,
                 uniform_remaining_bound_proved=False,uniform_source_bound_proved=False,RH_proved=False)
    post=['audit_mobius_arithmetic_bank_086.py','mobius_arithmetic_bank_audit_086_development.jsonl',
          'mobius_arithmetic_bank_root_preflight_086.json','audit_mobius_arithmetic_bank_artifacts_086.py',
          'MOBIUS_ARITHMETIC_BANK_ARTIFACT_REVIEW_086.txt','MOBIUS_ARITHMETIC_BANK_PROSPECTIVE_AUDIT_086.txt',
          'MOBIUS_ARITHMETIC_BANK_NATIVE_LAUNCH_REVIEW_086.txt',
          'publish_mobius_arithmetic_bank_086.py']
    frozen={name:(root/name).read_bytes()for name in post}
    write(out/'published_next_search_input.json',feedback);write(out/'published_results.json',results)
    gains=report['information_gains'];admitted=sum(w['admitted']for w in witnesses)
    added=sum(g['added']for g in gains);prime=sum(g['prime_pair_additions']for g in gains)
    lines=['CURRENT CONTINUATION: COUNTEREXAMPLE-GUIDED ARITHMETIC INFORMATION086','',
        'The full RH objective remains active and unfinished. Machine continuation:',
        'stage086/published_next_search_input.json, beside published_results.json.',
        'No all-scale signed remainder/source bound or RH proof has been obtained.','',
        'All eight frozen084 operators and their paid outer bounds are retained.',
        'The detector starts from the eight adaptive085 divisor identities, finds',
        'artificial Boolean witnesses exactly compatible with the CURRENT bank,',
        'then searches18576 rational divisor/prime-cofactor cutoff formulas.',
        'Only an exact witness above the unchanged C1,j31 residual target triggers',
        'an addition. An independently verified nonzero new-column dot proves',
        'finite bank information/rank gain. This is an active obstruction loop,',
        'not an analyst choosing the added formula. All attempts remain saved.','',
        f'Confirmed additions across both training arms: {added}; prime-pair additions: {prime}.',
        f'Compatible lower witnesses independently admitted: {admitted}/{len(witnesses)}.',
        f'Exact mixed upper bounds admitted: {report["upper_admitted"]}/{report["upper_rows"]}.',
        f'New parent(s): {report["validation_parents"]}; fresh upper admissions: {report["validation_upper_admitted"]}/{report["validation_rows"]}.',
        'Training3475 was already observed in085. All banks froze before the',
        'fresh draw and upper outcomes. Fresh W and L are new finite searches.',
        'Both divisor-only and union arms retain all operators, including failures.',
        'The common initial witness is shared; subsequent trajectories may differ.','',
        'New exact arithmetic rule: mu(pm)+mu(m)=0 for p prime, squarefree m,',
        'p not dividing m and pm<=N. Complete weighted aggregates keep every',
        'unit/prime endpoint and composite pair before anchoring. Constant-weight',
        'rows can include growing primes; source-weighted rows use bounded primes.',
        'All identities hold for all u; selected-bank rank gains are only finite.','',
        'For original complete anchored remainder R and annihilator columns V,',
        'Z=(V W^T+W V^T)/2 has actual signed value zero. Rational LL^T is PSD.',
        'B(R+Z+LL^T), signed trace plus absolute off-diagonals, is the exact price.',
        'No coordinate rotation, dropped cross term or numerical PSD admission',
        'is permitted. An exact s with V^T s=0 lower-bounds both unrestricted',
        'signed VSV^T and mixed-zero grammars, for this operator and geometry.',
        'Mixed controls alone have the same ideal SDP optimum as085 for fixed V.','',
        'Every upper search retains its zero-control incumbent; final training',
        'arms also retain the initial certificate through exact zero partners.',
        'Solver failure and inability to find a witness are not proof conclusions.',
        'Exact Boolean infeasibility would contradict the actual Mobius vector',
        'and is reported as an implementation inconsistency, not new mathematics.','',
        'The unpaid target is STILL, for every integer j>=1 and u>=1, a symbolic',
        'V_j,W_j,L_j with complete price <=C_j*u^(1+1/j), C_j independent of u.',
        'Every coefficient, inverse-conditioning and prime/composite cross cost',
        'must be paid. The inherited positive energy, paid outer block, recurrence',
        'and fixed-source inversion then give the conditional RH route. Finite',
        'C1 failures neither refute a larger constant nor refute RH.','',
        'Fresh frozen growth tests: '+str(report['growth_hypotheses_by_j']),
        'Next search consumes saved compatible obstructions and cumulative banks,',
        'seeking structured arithmetic partners, further identities or operator',
        'changes with a provable complete growth/scale argument. No all-sign oracle.','',
        f'Focused tests: {tests["distinct_focused_tests"]} distinct; {tests["focused_method_executions"]} executions,',
        f'{tests["passed_focused_executions"]} passed, {tests["failed_focused_executions"]} earlier fixture errors retained.',
        'Independent prospective faults and complete saved-artifact audit passed.',
        'The first launch was stopped and preserved: historical imports changed',
        'thread flags to2, so every initial witness search correctly declined MILP.',
        'The corrected launch enforces actual native pools and environment after',
        'all imports; three fresh-process worker regression checks passed. No fresh',
        'draw had occurred, and arithmetic policy/seed/budget did not change.',
        f'Main elapsed {report["elapsed_seconds"]:.3f}s; sampled aggregateRSS {report["sampled_aggregate_peak_rss_bytes"]}B;',
        f'conservative process-peak sum {report["conservative_process_peak_sum_bytes"]}B.',
        'Three workers, one native thread each,16GiB aggregate,7200sec per stage.',
        'Work counters include conservative solver proxies, not instruction bounds.',
        f'Preserved {sum(counts)} earlier frozen files plus {len(RUN.FILES)} scientific and {len(post)} postrun sources.',
        'No hashes, old scientific reruns, unknown composite signs or full source values.',
        'Sol6.1 agents supplied substantial backend, mathematical and independent audits.']
    handoff='\n'.join(lines)+'\n';(root/'MOBIUS_ARITHMETIC_BANK_HANDOFF.txt').write_text(handoff);(out/'handoff.txt').write_text(handoff)
    previous=read(RUN.PRIOR.OUT/'publication_integrity.json')
    pointers=previous['continuation_pointers_updated']+['MOBIUS_ANNIHILATOR_HANDOFF.txt']
    for name in pointers:
        (root/name).write_text('CURRENT CONTINUATION: MOBIUS_ARITHMETIC_BANK_HANDOFF.txt\n\n'
            '086 searches compatible arithmetic obstructions, adds exactly separating\n'
            'identities and verifies mixed controls. The all-scale signed price leaf\n'
            'and RH remain unresolved. Read stage086/published_next_search_input.json.\n'
            'Preserve historical evidence and all outcomes.\n')
    (out/'postrun_snapshot').mkdir()
    for name,content in frozen.items():
        (out/'postrun_snapshot'/name).write_bytes(content)
        if (root/name).read_bytes()!=content:raise ValueError('postrun086 source changed '+name)
    RUN.validate_parent();RUN.POOL.stage_check(started,[os.getpid()])
    write(out/'publication_integrity.json',dict(status=results['status'],prior_frozen_counts=counts,
        pre_run_files=RUN.FILES,postrun_files=post,total_frozen_files=sum(counts)+len(RUN.FILES)+len(post),tests=tests,
        continuation_pointers_updated=pointers,historical_handoffs_unchanged=True,
        publication_elapsed_seconds=time.monotonic()-started,source_bytes_preserved=True,hashes_used=False,RH_proved=False))
    print(json.dumps(dict(status=results['status'],additions=added,prime_pair_additions=prime,
                         upper_admitted=report['upper_admitted'],lower_admitted=admitted,uniform_remaining_bound_proved=False)))


if __name__=='__main__':main()
