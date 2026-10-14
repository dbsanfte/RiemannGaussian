"""Compile saved pairing evidence into explicit, unpaid bound obligations.

No new arithmetic sieve, kernel evaluation, candidate search or constant fit.
Intermediate plans use the already saved tokens to expose the two-pass proof.
Float cost attribution is descriptive; admission comes from archived Arb costs.
"""
from collections import Counter
from fractions import Fraction as Q
from math import fsum, isclose, sqrt
import json

import run_mobius_transport_059 as RUN
import mobius_transport_search_059 as SEARCH


def main():
    destination=RUN.OUT/'mechanism_feedback.json'
    if destination.exists(): raise FileExistsError('preserve completed059 feedback')
    meter=SEARCH.Meter(cap=1_000_000_000,seconds=7200)
    def read(name):
        raw=(RUN.OUT/name).read_text();meter.charge(len(raw))
        return json.loads(raw)
    def midpoint(interval):
        meter.charge(512)
        return float((Q(interval['lower'])+Q(interval['upper']))/2)

    RUN.validate_parent()
    for name in RUN.FILES:
        if (RUN.ROOT/name).read_bytes()!=(RUN.OUT/'source_snapshot'/name).read_bytes():
            raise ValueError('frozen059 producer/checker/protocol must be preserved')
    report=read('report.json');grammar=read('grammar.json')['programs']
    selection=read('selected.json');selected=selection['rows'];assessments=read('assessment.json')['rows']
    protocol=read('protocol.json')
    obstruction=read('prime_ratio_obstruction_001/report.json')
    obstructed={r['program_id']:r for r in obstruction['uniformly_obstructed_programs']}
    by_id={row['id']:row for row in grammar}
    claims_by_program={pid:[r['id'] for r in selected if r['program_id']==pid]
                      for pid in sorted({r['program_id'] for r in selected})}
    chosen=next(r for r in selected if r['claim']['beta']=='1/2'
                and r['selection_reason']=='best declared exponent class')
    chosen_status=next(r for r in assessments if r['id']==chosen['id'])
    rows=[];distinct_plans={};float_discrepancy=0.0
    for N in report['final_scales']:
        saved=read('final_'+str(N)+'.json')
        tokens=saved['source']['tokens'];by_d={t['d']:t for t in tokens}
        L1=midpoint(saved['independent']['absolute_sum'])
        profile_optimum=midpoint(saved['independent']['profile_optimum'])
        signed=midpoint(saved['independent']['signed_sum'])
        masks={}
        for profile in ('P','Q','D','S'):
            members=[t for t in tokens if t['profile']==profile]
            prefix=0;maximum=0;flux=[]
            for index,t in enumerate(members):
                prefix+=t['sign'];maximum=max(maximum,abs(prefix))
                following=members[index+1]['magnitude'] if index+1<len(members) else 0.0
                gap=t['magnitude']-following
                if gap < -1e-14: raise ValueError('saved screening kernel violates monotonicity')
                flux.append(abs(prefix)*gap);meter.charge(16)
            masks[profile]={'tokens':len(members),'signed_count':prefix,
                'largest_absolute_prefix_count':maximum,'weighted_prefix_flux_float':fsum(flux)}
        flux=fsum(r['weighted_prefix_flux_float'] for r in masks.values())
        if not isclose(flux,profile_optimum,rel_tol=1e-10,abs_tol=1e-12):
            raise ValueError('saved independent profile optimum disagrees with prefix attribution')
        programs=[]
        for pid,plan,checked in zip(saved['program_ids'],saved['plans'],saved['independent']['rows']):
            policy=by_id[pid]['policy'];cost=midpoint(checked['bound'])
            context=SEARCH.Context()
            if len(policy['steps'])==2:
                first=SEARCH.build_plan(N,tokens,{'steps':policy['steps'][:1]},meter,context)
                if first['pairs']!=plan['pairs'][:len(first['pairs'])]:
                    raise ValueError('recorded final plan must preserve first-pass pairs')
                rescue=plan['pairs'][len(first['pairs']):]
                restored=sorted(sum(rescue,[])+plan['unmatched'])
                if restored!=first['unmatched']: raise ValueError('all residuals accounted for by second pass')
            else:
                first=plan;rescue=[]
            first_cost=SEARCH.plan_cost(tokens,first,meter)
            rescue_saving=2*fsum(min(by_d[a]['magnitude'],by_d[b]['magnitude']) for a,b in rescue)
            first_pair_cost=fsum(abs(by_d[a]['magnitude']-by_d[b]['magnitude']) for a,b in first['pairs'])
            final_leftover_cost=fsum(by_d[d]['magnitude'] for d in plan['unmatched'])
            if not isclose(first_cost-rescue_saving,cost,rel_tol=1e-10,abs_tol=1e-12):
                raise ValueError('complete B_final=B_first-2sum(min paired residuals) accounting')
            meter.charge(32*(len(tokens)+len(rescue)))
            ablation=next(r for r in saved['source_sign_ablation'] if r['program_id']==pid)
            programs.append({'program_id':pid,'family':by_id[pid]['family'],
                'checked_cost':checked['bound'],'cost_midpoint_float':cost,
                'cost_over_sqrtN_float':cost/sqrt(N),'cost_over_L1_float':cost/L1,
                'unmatched_tokens':len(plan['unmatched']),
                'final_unmatched_charge_float':final_leftover_cost,
                'first_pass_pairs':len(first['pairs']),'first_pass_cost_float':first_cost,
                'first_pass_pair_charge_float':first_pair_cost,
                'rescue_pairs':len(rescue),'rescue_saving_float':rescue_saving,
                'rescue_saving_over_first_cost_float':rescue_saving/first_cost if first_cost else 0,
                'absolute_mu_over_actual_mu_cost_float':ablation['absolute_mu_cost_float']/cost,
                'attribution_is_float_only':True,'uniform_growth_bound_proved':False})
            key=(tuple(sorted(tuple(pair) for pair in plan['pairs'])),tuple(plan['unmatched']))
            distinct_plans.setdefault(N,{}).setdefault(key,[]).append(pid)
        float_discrepancy=max(float_discrepancy,max(r['float_absolute_difference_from_checked_midpoint']
                                                   for r in saved['claims']))
        rows.append({'N':N,'token_count':len(tokens),'actual_signed_source_midpoint_float':signed,
            'absolute_sum_midpoint_float':L1,'profile_optimum_midpoint_float':profile_optimum,
            'masked_prefix_descriptors':masks,'programs':programs})

    # A proof graph distinguishes exact argument rules from missing estimates.
    # It contains the signed rescue term, so the next search need not bound
    # its positive and negative parts independently and lose their interaction.
    targets=[]
    for pid in claims_by_program:
        program=by_id[pid]
        if not program['policy']['steps']: continue
        targets.append({'id':'uniform_cost_'+pid,'program':program,
            'source_parameters':selection['source_parameters'],
            'quantity':{'kind':'complete_pairing_cost','positive_pair_charges':'sum_(i,j in pairs) |m_i-m_j|',
                        'residual_charge':'sum_(i in unmatched) m_i'},
            'quantifiers':'for every rational kappa>0, exists finite C_kappa independent of every integer N>=2',
            'bound':'B_policy(N)<=C_kappa*N^(1/2+kappa)',
            'alternative_sufficient_bound':'B_policy(N)<=C*sqrt(N)*(log(2N))^A for fixed finite C,A',
            'paid_argument_rules':['complete_signed_pairing_triangle','priced_residual_rescue_identity'],
            'program_resource_note':'implementation ceilings are finite; any uniform proof must justify the total mathematical policy',
            'uniform_estimate_status':'REFUTED_FOR_THIS_POLICY' if pid in obstructed else 'OPEN',
            'obstruction_certificate':obstructed.get(pid),
            'fitted_constants_are_proved_uniform':False})
    leading=by_id[chosen['program_id']]
    expected={'steps':[SEARCH._scan('profile'),SEARCH._scan()]}
    profile_rescue=leading['policy']==expected
    next_target={'source':'same joined ordinary-mu middle J(N), including d1 and unequal range exits',
        'selected_from_original_frozen_ranking':chosen,'finite_assessment':chosen_status,
        'target_id':'uniform_cost_'+chosen['program_id'],
        'bound_to_discover':'for every kappa>0, B(N)=O_kappa(N^(1/2+kappa)) uniformly in integerN>=2',
        'actual_source_bound_follows':'|J(N)|<=B(N)',
        'uniform_middle_bound_proved':False}
    if profile_rescue:
        next_target.update({'exact_auxiliary':'F(N)=sum_profiles sum_j |S_profile,j|*(m_j-m_(j+1)) - 2*sum_rescue_pairs min(m_i,m_j)',
            'S_profile_j':'actual sum of mu(d)*kernel_sign_N(d) over the first j cofactors in that profile',
            'terminal_convention':'m_(last+1)=0; all unmatched source mass remains priced',
            'rescue_pairs':'second pass of the fixed selected program on the first-pass unmatched tokens',
            'exact_identity':'B_selected(N)=F(N)>=0',
            'equivalent_positive_decomposition':'B_selected=E_committed+B_residual_global',
            'E_committed':'sum of |m_i-m_j| over the first-pass pairs, which later rescue cannot undo',
            'B_residual_global':'complete cost of the global second pass applied only to first-pass leftovers',
            'decomposition_is_a_new_uniform_estimate':False,
            'profile_part_alone_is_sufficient_but_can_lose_cross_profile_cancellation':True,
            'required_new_lemma':'uniform bound on the JOINT weighted prefix flux minus its explicit rescue savings',
            'no_unpaid_leaf_may_be_used_as_a_premise':['the target bound itself','RH','RH-strength Mertens bound',
                'random or independent Mobius signs','a fitted finite exponent or constant']})
    result={'schema':'mobius-transport-mechanism-feedback-v1',
        'phase':'post-run saved-evidence interpretation, without reranking or refitting',
        'previous_goal_turn':'PROGRESS:058 exact operator search produced the signed source and endpoint arguments',
        'current_goal_turn':'PROGRESS:059 searched auxiliary bounds and independently tested fixed claims; uniform cost still open',
        'counts':{k:report[k] for k in ('programs','dominated_programs','numerically_scored_programs',
            'fixed_growth_hypotheses','selected_claims','selected_policies','finite_status_counts')},
        'candidate_claims_grouped_by_policy':claims_by_program,
        'postrun_exact_asymptotic_obstructions':obstruction,
        'finite_successes_are_preserved_even_when_the_uniform_claim_is_refuted':True,
        'finite_identical_plan_groups':{str(N):list(plans.values()) for N,plans in distinct_plans.items()},
        'repeated_exponents_for_one_policy_are_independent_mechanisms':False,
        'no_all_scale_equivalence_inferred_from_finite_plan_equality':True,
        'diagnostics':rows,'largest_float_cost_vs_checked_midpoint_difference':float_discrepancy,
        'proof_rules':[
            {'id':'complete_signed_pairing_triangle','identity':'J=sum signed pair differences + signed unmatched terms',
             'bound':'|J|<=B_policy','proved':True,'uniform_growth_bound_proved':False},
            {'id':'profile_prefix_flux','identity':'B_profile_opt=sum_profiles sum_j |S_j|*(m_j-m_(j+1))',
             'proved':True,'uniform_growth_bound_proved':False},
            {'id':'priced_residual_rescue_identity','identity':'B_final=B_first-2*sum_rescue_pairs min(m_i,m_j)',
             'proof':'for nonnegative u,v, |u-v|=u+v-2min(u,v); first-pass pairs remain fixed and residual coverage is complete',
             'proved':True,'uniform_growth_bound_proved':False}],
        'obligation_graph':{'targets':targets,'leading_target':next_target,
            'paid_endpoint_and_RH_bridge_binding':protocol['source_binding'],
            'cyclic_dependencies_admitted':False,'uniform_cost_leaf_discharged':False},
        'next_search_requirements':[
            'Search arguments controlling the joint prefix-flux and rescue-savings auxiliary, or a cheaper complete signed construction.',
            'Allow exact recurrences, telescoping potentials, floor-mask interval decompositions and actual Mobius divisor correlations.',
            'Introduce a new correlation or growth premise only as an explicit unresolved obligation; never mark it paid by finite tests.',
            'Test scale/parameter quantifiers including moving epsilon and every boundary contribution.',
            'Use the generic same-profile prime-ratio lower bound to reject any proposed square-root route that charges linearly many such edges.',
            'Preserve scope: |mu| ablation is descriptive evidence of sign sensitivity, not proof of the actual-mu uniform bound.',
            'Rank proved exponent/recurrence improvements before numerical constants; do not simply increase a failed fitted C.'],
        'analysis_operations':meter.operations,'fresh_source_tables_evaluated':False,
        'fresh_kernel_integrals_evaluated':False,'original_candidate_search_replayed':False,
        'final_constants_refitted':False,'hashes_used':False,
        'uniform_transport_cost_growth_bound_proved':False,'uniform_full_source_bound_proved':False,
        'RH_proved':False,'RH_refuted':False}
    destination.write_text(json.dumps(result,indent=2)+'\n')
    return result


if __name__=='__main__':
    result=main()
    print(json.dumps({'counts':result['counts'],
        'next_target':result['obligation_graph']['leading_target'],
        'analysis_operations':result['analysis_operations']},indent=2))
