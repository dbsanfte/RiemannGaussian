"""Discover complete profile mass identities before examining saved copy costs.

No new scientific mu tables or kernels are evaluated. Selection uses only
exact proved leftover constants. Paired-copy growth remains a separate leaf.
"""
from fractions import Fraction as Q
from math import fsum
import json
import resource
import time

import mobius_mass_conservation_060 as SEARCH
import check_mobius_mass_conservation_060 as CHECK
import run_mobius_transport_059 as PRIOR
import mine_prime_ratio_obstruction_059 as OBSTRUCTION
from run_fractional_prime_kernel_051 import write,emit,check_receipt

ROOT=PRIOR.ROOT
OUT=PRIOR.OUT/'mass_conservation_followup_001'
FILES=['mobius_mass_conservation_060.py','test_mobius_mass_conservation_060.py',
       'mobius_mass_search_060_development.json',
       'check_mobius_mass_conservation_060.py','test_check_mobius_mass_conservation_060.py',
       'mobius_mass_checker_060_development.json','MOBIUS_MASS_CHECK_SCOPE_060.txt',
       'MOBIUS_MASS_CONSERVATION_REVIEW_060.txt',
       'run_mobius_mass_conservation_060.py','mobius_mass_conservation_protocol_060.txt']
SPEC={'weight_budget':6,'maximum_selected_weights':3,
      'copy_modes':['global','profile_then_global'],
      'rank':['proved_log_degree','proved_leftover_coefficient','total_copies_per_profile_set','lexicographic_weights'],
      'discovery_uses_source_values':False,'new_kernel_evaluation':False}


def validate_parent():
    counts=PRIOR.validate_parent()
    for directory,names in ((PRIOR.OUT/'source_snapshot',PRIOR.FILES),
                            (PRIOR.OUT/'prime_ratio_obstruction_001'/'source_snapshot',OBSTRUCTION.FILES)):
        if sorted(p.name for p in directory.iterdir())!=sorted(names):
            raise ValueError('complete prior source snapshot inventory')
        for name in names:
            if (ROOT/name).read_bytes()!=(directory/name).read_bytes():
                raise ValueError('preserve frozen source '+name)
        counts.append(len(names))
    for name in ('analyze_mobius_transport_059.py','MOBIUS_TRANSPORT_CANDIDATE_REVIEW_059.txt'):
        if (ROOT/name).read_bytes()!=(PRIOR.OUT/name).read_bytes():
            raise ValueError('preserve059 interpretation and stopped review')
    return counts


def audit_copy_coverage(tokens,weights,plan,meter):
    """Replay the concrete combinatorics without using the producer's scan."""
    by_d={t['d']:t for t in tokens}
    expected={(t['d'],j) for t in tokens for j in range(weights[SEARCH.PROFILES.index(t['profile'])])}
    seen=set()
    for pair in plan['pairs']:
        if len(pair)!=2:raise ValueError('binary copied edge')
        a,b=(tuple(k) for k in pair)
        if a==b or a not in expected or b not in expected or a in seen or b in seen:
            raise ValueError('disjoint legal copied edge')
        if by_d[a[0]]['sign']+by_d[b[0]]['sign']!=0:raise ValueError('opposite actual signs')
        seen.update((a,b));meter.charge(20)
    leftovers=[tuple(k) for k in plan['unmatched']]
    for k in leftovers:
        if k not in expected or k in seen:raise ValueError('complete unrepeated residual copies')
        seen.add(k);meter.charge(8)
    if seen!=expected:raise ValueError('every original token copy accounted for')
    if len({by_d[k[0]]['sign'] for k in leftovers})>1:raise ValueError('global residual scan exhausted')
    mass=sum(t['sign']*weights[SEARCH.PROFILES.index(t['profile'])] for t in tokens)
    if plan['copy_count']!=len(expected) or plan['signed_copy_count']!=mass or len(leftovers)!=abs(mass):
        raise ValueError('exact conserved copy count')
    meter.charge(16*len(tokens))
    return {'verified':True,'copy_source_preserved_by_equal_splitting':True,
            'every_copy_accounted_for':True,'opposite_sign_edges':True,
            'complete_global_exhaustion':True,'copy_count':len(expected),
            'signed_copy_count':mass,'uniform_paired_cost_bound_proved':False}


def saved_diagnostics(selected,parameters,meter):
    spec=json.loads((PRIOR.OUT/'final_spec.json').read_text())
    summaries=[]
    for N in spec['scales']:
        old=json.loads((PRIOR.OUT/('final_'+str(N)+'.json')).read_text())
        source=old['source'];independent=old['independent']['tokens']
        if old['N']!=N or source['request']!={'N':N,**parameters}:
            raise ValueError('bind saved complete source parameters')
        fields=('d','profile','sign','kernel_sign','mu')
        if [{k:t[k] for k in fields} for t in source['tokens']]!=independent:
            raise ValueError('saved independent ordinary-mu token metadata')
        tokens=source['tokens'];meter.reserve(1024+len(tokens)*2048)
        meter.charge(32*len(tokens))
        signed_float=fsum(t['sign']*t['magnitude'] for t in tokens)
        absolute_float=fsum(t['magnitude'] for t in tokens)
        rows=[]
        for candidate in selected:
            cert=candidate['certificate'];weights=cert['weights']
            smooth=SEARCH.exact_smooth_mass(cert['identity'],N,meter)
            count=sum(t['sign']*weights[SEARCH.PROFILES.index(t['profile'])] for t in independent)
            meter.charge(16*len(independent))
            if smooth!=count:raise ValueError('complete saved arithmetic mass equals exact smooth count')
            for mode in SPEC['copy_modes']:
                plan=SEARCH.copy_plan(tokens,weights,mode,meter)
                audit=audit_copy_coverage(tokens,weights,plan,meter)
                if len(plan['unmatched'])!=abs(smooth):raise ValueError('smooth count pays every final leftover')
                row={'candidate_id':candidate['id'],'weights':weights,'mode':mode,
                     'N':N,'smooth_mass_exact':str(smooth),'coverage_verification':audit,
                     'plan':plan,'total_cost_float':plan['pair_cost_float']+plan['leftover_cost_float'],
                     'source_signed_sum_float':signed_float,'source_absolute_sum_float':absolute_float,
                     'used_for_selection':False,'new_finite_growth_claim_tested':False,
                     'descriptive_float_only':True,'uniform_paired_cost_bound_proved':False}
                rows.append(row)
                summaries.append({k:v for k,v in row.items() if k!='plan'}|{
                    'pair_cost_float':plan['pair_cost_float'],
                    'leftover_cost_float':plan['leftover_cost_float'],
                    'copy_count':plan['copy_count'],'pairs':len(plan['pairs']),
                    'unmatched':len(plan['unmatched'])})
        write(OUT/('copies_'+str(N)+'.json'),{'N':N,'rows':rows,
            'saved059_tokens_reused':True,'fresh_source_tables_or_kernel_integrals':False})
        emit('mobius_mass_saved_copy_audit',N=N,plans=len(rows))
    return spec['scales'],summaries


def feedback(parameters,selected,parent_feedback):
    leaves=[]
    for candidate in selected:
        for mode in SPEC['copy_modes']:
            leaves.append({'id':candidate['id']+'_'+mode,'weights':candidate['certificate']['weights'],
                'copy_mode':mode,'copy_order':'ascending (cofactor,copy_index); opposite-sign stack',
                'bound_to_discover':'for every rational kappa>0, exists finite C_kappa: E_copy(N)<=C_kappa*N^(1/2+kappa) for every integer N>=2',
                'expression':'E_copy(N)=sum over the fixed plan pairs |m_i/w_profile(i)-m_j/w_profile(j)|',
                'bound_status':'OPEN','remaining_leftovers':'paid separately by the exact linked certificate',
                'paid_leftover_verification':candidate['verification'],
                'whole_middle_implication':'|J(N)|<=E_copy(N)+B_left(N)',
                'unpaid_premises':[],'uniform_paired_cost_bound_proved':False})
    return {'schema':'mobius-mass-conservation-feedback-v1',
        'source_parameters':parameters,'source_binding':'same058 joined middle including all ordinary-mu signs, cofactor1 and range exits',
        'previous_goal_turn':'059 substantive: arithmetic matching search and exact asymptotic rejection',
        'current_goal_turn':'060 substantive: exact positive profile conservation search and uniform final-copy-leftover proof' if selected else '060 exact conservation search completed without a selected positive construction',
        'construction':'split each profile token into its discovered number of equal signed copies, then use a complete opposite-sign plan',
        'source_changed':False,'matching_construction_changed':True,
        'paid_rule':'B_left(N)<=coefficient*(1+log2(4N))^log_degree for every integer N>=2 with fixed parameters and weights',
        'paid_scope':'only final unmatched copies; every global-stage pair is included in the remaining paired cost',
        'known_law_reused':'mu_M*One=indicator of M-smooth integers',
        'new_prime_distribution_theorem_claimed':False,
        'all_scale_bound_discovered_for_a_component':bool(selected),
        'obligation_graph':{'sufficient_alternative_paired_cost_leaves':leaves,
            'one_leaf_suffices':True,'cyclic_dependencies_admitted':False,
            'paid_endpoint_and_RH_bridge_binding':parent_feedback['obligation_graph']['paid_endpoint_and_RH_bridge_binding'],
            'uniform_middle_bound_proved':False},
        'next_search_requirements':[
            'search joint threshold or interval/divisor-tail controls for E_copy, or larger signed groups priced before absolute values',
            'conservation at threshold zero alone does not control other thresholds or truncated prefixes',
            'keep all ordinary prime factors, units, range exits and boundary divisor tails',
            'allow general rational alpha and block powers within explicit resource budgets; rebind endpoint conditions if parameters change',
            'prefer a proved exponent or scale extension over a better finite constant',
            'a complete same-profile lift of the rejected first-prime-ratio rule retains its059 obstruction',
            'do not infer random Mobius signs, RH-strength Mertens bounds, or growth from five descriptive saved cases'],
        'prior_obstructed_programs':[r['program_id'] for r in parent_feedback['postrun_exact_asymptotic_obstructions']['uniformly_obstructed_programs']],
        'historical_finite_claims_unchanged':True,'fresh_source_tables_evaluated':False,
        'fresh_kernel_integrals_evaluated':False,'finite_constants_refitted':False,
        'uniform_paired_cost_bound_proved':False,'uniform_full_source_bound_proved':False,
        'RH_proved':False,'RH_refuted':False}


def main():
    if OUT.exists():raise FileExistsError('do not overwrite or replay completed/failed060 output')
    started=time.monotonic();counts=validate_parent()
    prior_selected=json.loads((PRIOR.OUT/'selected.json').read_text())
    parameters=prior_selected['source_parameters']
    parent_feedback=json.loads((PRIOR.OUT/'mechanism_feedback.json').read_text())
    if parent_feedback['uniform_full_source_bound_proved'] or parent_feedback['RH_proved']:
        raise ValueError('the prior full arithmetic bound is still OPEN')
    # This binds the saved source to the already paid endpoints, without
    # rerunning any058/059 proof, scientific study, or source computation.
    bound_parameters,binding=PRIOR.source_parameters()
    if parameters!=bound_parameters or binding!=parent_feedback['obligation_graph']['paid_endpoint_and_RH_bridge_binding']:
        raise ValueError('full source and endpoint/bridge parameter binding')
    frozen={name:(ROOT/name).read_bytes() for name in FILES}
    development=sum(check_receipt(json.loads(data)) for name,data in frozen.items() if name.endswith('_development.json'))
    OUT.mkdir();(OUT/'source_snapshot').mkdir()
    for name,data in frozen.items():(OUT/'source_snapshot'/name).write_bytes(data)
    meter=SEARCH.Meter(cap=10_000_000_000,seconds=7200);cm=CHECK.Meter()
    try:
        write(OUT/'spec.json',{'spec':SPEC,'parameters':parameters,
            'prior_frozen_counts':counts,'new_frozen_files':len(FILES),
            'frozen_before_scientific_signature_and_weight_search':True,'hashes_used':False,
            'prior_saved_values_are_not_unseen_data':True,'old_suites_or_studies_replayed':False})
        result=SEARCH.discover(parameters,SPEC['weight_budget'],meter)
        basis=[CHECK.verify_identity(cert,cm) for cert in result['basis_identities']]
        verified=[]
        for index,cert in enumerate(result['positive_copy_certificates']):
            verified.append({'id':'mobius_mass_'+str(index).zfill(4),'certificate':cert,
                             'verification':CHECK.verify_copy_bound(cert,cm)})
        discovery_operations=meter.operations
        write(OUT/'discovery.json',result)
        write(OUT/'verification.json',{'basis_identities':basis,'positive_copy_bounds':verified,
            'independent_checker_operations':cm.operations,'paired_cost_growth_proved':False})
        selected=verified[:SPEC['maximum_selected_weights']]
        write(OUT/'selected.json',{'rows':selected,'selected_by':SPEC['rank'],
            'saved_source_tokens_read_before_selection':False,'numerical_cost_used_for_selection':False,
            'all_selected_leftover_bounds_proved':True,'paired_cost_growth_proved':False})
        emit('mobius_mass_exact_search_complete',nullity=result['signature']['nullity'],
             weight_vectors=result['weight_vectors_examined'],positive_certificates=len(verified),selected=len(selected))
        scales,diagnostics=saved_diagnostics(selected,parameters,meter) if selected else ([],[])
        write(OUT/'diagnostics.json',{'rows':diagnostics,'scales':scales,'descriptive_float_only':True,
            'used_for_selection':False,'fresh_source_tables_or_kernel_integrals':False})
        write(OUT/'mechanism_feedback.json',feedback(parameters,selected,parent_feedback))
        validate_parent()
        if any((ROOT/name).read_bytes()!=data for name,data in frozen.items()):
            raise ValueError('preserve the complete frozen060 source')
        report={'status':'UNIFORM_FINAL_COPY_LEFTOVERS_PROVED_PAIRED_COST_OPEN' if selected else 'NO_POSITIVE_COPY_CONSTRUCTION_SELECTED',
            'weight_vectors_examined':result['weight_vectors_examined'],
            'primitive_vectors_examined':result['primitive_vectors_examined'],
            'exact_conservation_dimension':result['signature']['nullity'],
            'independently_verified_basis_identities':len(basis),'positive_copy_certificates':len(verified),
            'selected_weights':[r['certificate']['weights'] for r in selected],
            'saved_scales':scales,'saved_concrete_plans_audited':len(diagnostics),
            'development_operations':development,'discovery_operations':discovery_operations,
            'independent_checker_operations':cm.operations,
            'saved_copy_diagnostic_operations':meter.operations-discovery_operations,
            'operations_are_instrumentation_units_not_cpu_instructions':True,
            'elapsed_seconds':time.monotonic()-started,
            'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            'prospective_algorithm_bytes':meter.peak_bytes_estimate,
            'prior_frozen_counts':counts,'new_frozen_source_count':len(FILES),
            'hashes_used':False,'old_suites_or_studies_replayed':False,
            'fresh_source_tables_or_kernel_integrals':False,'finite_constants_refitted':False,
            'uniform_final_copy_leftover_bound_proved':bool(selected),
            'uniform_paired_cost_bound_proved':False,'uniform_full_source_bound_proved':False,
            'RH_proved':False,'RH_refuted':False}
        write(OUT/'report.json',report)
        emit('mobius_mass_complete',status=report['status'],elapsed_seconds=report['elapsed_seconds'])
        return report
    except BaseException as exc:
        write(OUT/'failure.json',{'type':type(exc).__name__,'message':str(exc),
            'elapsed_seconds':time.monotonic()-started,'producer_operations':meter.operations,
            'independent_checker_operations':cm.operations,'RH_proved':False,'uniform_full_source_bound_proved':False})
        raise


if __name__=='__main__':main()
