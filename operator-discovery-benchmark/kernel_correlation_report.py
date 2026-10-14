"""Strict scoped loader for complete signed Gram and density evidence."""
from pathlib import Path
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    directory=Path(directory).resolve()
    spec,seal,pc,cal,cs,cases,checked,batch,arc,final=(read(directory/n) for n in [
        'protocol.json','seal.json','parameter_cases.json','parameter_calibration.json','calibration_seal.json',
        'final_cases.json','verification.json','candidate_batch.json','archive.json','final_evaluation.json'])
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(directory/'frozen_source'/n)==spec['code_sha256'][n]
    for dep in spec['named_calibration_dependencies']:assert sha(dep['path'])==dep['sha256']
    for n,h in seal['files'].items():assert sha(directory/n)==h
    assert seal['protocol_sha256']==digest(spec) and seal['selection_closed'] and not seal['final_cases_exist_at_seal'] and not seal['parameter_cases_exist_at_seal']
    assert arc['selection_closed'] and not arc['final_data_used']
    assert pc['seal_sha256']==sha(directory/'seal.json') and pc['generated_after_archive_seal'] and pc['no_final_scale_information_present']
    assert cal['parameters_sha256']==digest(pc) and cal['training_only'] and not cal['final_scales_used']
    assert cs['archive_seal_sha256']==sha(directory/'seal.json') and cs['parameter_cases_sha256']==sha(directory/'parameter_cases.json')
    assert cs['parameter_calibration_sha256']==sha(directory/'parameter_calibration.json') and not cs['final_cases_exist_at_calibration_seal']
    assert cases['calibration_seal_sha256']==digest(cs) and cases['generated_after_calibration_seal']
    assert checked['all_passed'] and all(checked['checks'].values()) and checked['protocol_sha256']==digest(spec)
    assert checked['checker_sha256']==sha(BASE/'check_kernel_correlations.py') and checked['final_sha256']==sha(directory/'final_evaluation.json')
    assert checked['replay_sha256']==seal['files'] and not checked['mathematical_audit_imports_production_code']
    assert final['cases_sha256']==digest(cases) and final['calibration_seal_sha256']==digest(cs) and final['seal_sha256']==digest(seal)
    source=Path(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    from mellin_kernel_report import summary as parent_summary
    parent_summary(source)
    assert spec['uniform_RH_sufficient_signed_controls_verified']==checked['uniform_RH_sufficient_signed_controls_verified']==final['uniform_RH_sufficient_signed_controls_verified']==[]
    assert not spec['RH_proved'] and not final['RH_proved'] and spec['not_autonomous_proof_invention']
    assert not spec['new_prime_distribution_estimate_imported'] and not spec['historical_priority_is_acceptance_gate']
    ps={p['id']:p for p in batch['programs']};outcomes={o['candidate_id']:o for o in final['outcomes']};records=[]
    for c in arc['archive']:
        o=outcomes[c['id']];assert not o['uniform_signed_premise_proved']
        records.append({'candidate':c,'program':ps[c['program_id']],'final_outcome':o})
    candidates=[c for c in batch['candidates'] if c['program_id'] in ps]
    counts={kind:sum(p['kind']==kind for p in batch['programs']) for kind in ['energy','density']}
    survivors=[r for r in records if r['candidate']['RH_sufficient_if_uniform'] and r['final_outcome']['finite_points_passed']]
    return {'status':'verified_scoped_signed_Gram_density_search','run_directory':str(directory),
        'program_count':len(batch['programs']),'program_counts_by_kind':counts,
        'growth_hypotheses':len(candidates),'primary_and_ablation_hypotheses':len(batch['candidates']),
        'recovering_energy_programs':sum(p['kind']=='energy' and p['recovery']['all_height_no_common_zero'] for p in batch['programs']),
        'recovering_density_programs':sum(p['kind']=='density' and p['density_recovery']['all_height_recovery'] for p in batch['programs']),
        'recovering_singular_energy_programs':sum(p['kind']=='energy' and p['metric']['rank']==1 and p['recovery']['all_height_no_common_zero'] for p in batch['programs']),
        'indefinite_programs_preserved':sum(not p['metric']['positive_semidefinite'] for p in batch['programs']),
        'records':records,'RH_if_uniform_finite_survivors':survivors,
        'energy_RH_if_uniform_finite_survivors':sum(r['candidate']['kind']=='energy' for r in survivors),
        'density_RH_if_uniform_finite_survivors':sum(r['candidate']['kind']=='density' for r in survivors),
        'negative_controls':final['negative_controls'],
        'false_controls_finite_passes_analytically_rejected':sum(o['finite_points_passed'] for o in final['negative_controls']),
        'ablation_comparison':arc['ablation_comparison'],'independent_native_counts':checked['counts'],
        'reflection_bridge_audit':checked['reflection_bridge_audit'],'verified_checks':len(checked['checks']),
        'complete_infinite_arithmetic_tails_enclosed':True,'constants_in_q_restricted':False,'finite_q_grid_suffices':False,
        'all_real_scale_signed_diagonal_remainder_proved':True,'proved_diagonal_remainder_exponent':'1/2',
        'unproved_RH_density_remainder_exponent':'1/4','proved_full_response_exponent':'1',
        'off_diagonal_RH_uniform_premise_proved':False,'density_quarter_power_uniform_premise_proved':False,
        'new_independent_prime_distribution_estimate':False,'verification_sha256':sha(directory/'verification.json'),
        'named_calibration_dependencies':spec['named_calibration_dependencies'],'machine_formalized':False,
        'not_autonomous_proof_invention':True,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    pointer=BASE/'kernel-correlation-results/latest.json'
    return summary(read(pointer)['run_directory']) if pointer.exists() else {'status':'not_run'}


def text_report(s):
    energy=s['program_counts_by_kind']['energy'];density=s['program_counts_by_kind']['density'];r=s['independent_native_counts'];ac=s['ablation_comparison']
    lines=[
        'Complete signed arithmetic Gram and density search',
        f"Primary programs: {s['program_count']} ({energy} energy, {density} density). Growth hypotheses: {s['growth_hypotheses']}; including ablation: {s['primary_and_ablation_hypotheses']}.",
        f"Independent verification: {s['verified_checks']} checks passed; deterministic isolated replay matched every sealed discovery file.",
        f"All-height recovery: {s['recovering_energy_programs']} energy programs, including {s['recovering_singular_energy_programs']} singular metrics; {s['recovering_density_programs']} density programs. Indefinite leads retained: {s['indefinite_programs_preserved']}.",
        'Proved: E_H=D_H+C_H for the complete infinite actual inverse; |D_H-A_H X|<=V_H sqrt(X) at every real X>0. A_H retains all signed cross-kernel coefficients.',
        'RH targets: C_H<=rho D_H+B_q X^(2*(1/2+epsilon/q^nu))*log(e+X)^d; or |D_H-A_H X|<=C_q X^(1/4+epsilon/q^nu)*log(e+X)^d, with certified recovery. Every q has its own free finite constant.',
        'Density zero bridge: possible zeta(s)/zeta(2s) numerator cancellation forces a multiplicity-preserving zero chain rho -> 1-conjugate(rho)/2. Heights halve and the chain accumulates at nonzero zeta(2/3). No sampled zero list is used.',
        f"Fresh finite RH-if-uniform survivors: {s['energy_RH_if_uniform_finite_survivors']} energy, {s['density_RH_if_uniform_finite_survivors']} density. These are fitted estimates, not all-scale theorems.",
        f"Analytically false controls that nevertheless pass the finite checks: {s['false_controls_finite_passes_analytically_rejected']}. Controls retain the actual diagonal comparator; no counterfeit pair decomposition is claimed.",
        f"Automatic promotions admitted: {ac['admitted_promotions']} / {ac['proposal_slots']} slots. Equal-budget ablation best conditional log costs: primary={ac['best_primary_log_cost']}, ablation={ac['best_ablation_log_cost']}.",
        f"Independent full squarefree atoms: {r['independent_complete_squarefree_atoms']}; full Gram observations: {r['independent_complete_Gram_observations']}; signed comparisons: {r['independent_finite_inequality_comparisons']}; charged observers: {r['independent_fully_charged_observers']}.",
        'The elementary squarefree density remainder is an actual signed all-scale theorem. It supplies no new prime-distribution estimate or RH-strength off-diagonal control. The quarter-power density estimate remains unproved.',
        'Proof and recovery methods were supplied by the programmer; formulas and estimates were selected automatically within a frozen language. Verification is independently coded, not machine formalized.',
        'Uniform RH-sufficient signed controls proved: 0. RH proved: false.',
        '',
        'Selected archive (fresh outcomes refer to fitted constants):']
    for row in s['records']:
        c,p,o=row['candidate'],row['program'],row['final_outcome'];f=c['frontier']
        lines.append(f"{c['id'][:12]} {c['kind']} k,ell,b={p['parameters']} H={p['metric']['entries']} eta={f['limit']} nu={f['approach_power']} d={f['log_power']} rho={c['rho']} recovery={c['RH_sufficient_if_uniform']} fresh_pass={o['finite_points_passed']} max_ratio={o['maximum_ratio']:.6g}")
    return '\n'.join(lines)+'\n'
