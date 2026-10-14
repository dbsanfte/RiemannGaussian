"""Strict scoped loader for complete-tail kernel/frontier evidence."""
from pathlib import Path
from stable_scale_report import BASE,read,sha,digest


def summary(directory):
    directory=Path(directory).resolve()
    spec,seal,cal,pc,cs,checked,batch,arc,cases,final=(read(directory/n) for n in [
        'protocol.json','seal.json','parameter_calibration.json','parameter_cases.json','calibration_seal.json',
        'verification.json','candidate_batch.json','archive.json','final_cases.json','final_evaluation.json'])
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(directory/'frozen_source'/n)==spec['code_sha256'][n]
    for dep in spec['named_calibration_dependencies']:assert sha(dep['path'])==dep['sha256']
    for n,h in seal['files'].items():assert sha(directory/n)==h
    assert seal['protocol_sha256']==digest(spec) and seal['selection_closed'] and not seal['final_cases_exist_at_seal'] and not seal['parameter_cases_exist_at_seal']
    assert arc['selection_closed'] and not arc['final_data_used'] and pc['generated_after_archive_seal'] and pc['no_final_scale_information_present']
    assert cal['parameters_sha256']==digest(pc) and cal['training_only'] and not cal['final_scales_used']
    assert cs['archive_seal_sha256']==sha(directory/'seal.json') and cs['parameter_cases_sha256']==sha(directory/'parameter_cases.json')
    assert cs['parameter_calibration_sha256']==sha(directory/'parameter_calibration.json') and not cs['final_cases_exist_at_calibration_seal']
    assert cases['calibration_seal_sha256']==digest(cs) and cases['generated_after_calibration_seal']
    assert checked['all_passed'] and all(checked['checks'].values()) and checked['protocol_sha256']==digest(spec)
    assert checked['checker_sha256']==sha(BASE/'check_mellin_kernels.py') and checked['final_sha256']==sha(directory/'final_evaluation.json')
    assert checked['replay_sha256']==seal['files']
    assert final['cases_sha256']==digest(cases) and final['calibration_seal_sha256']==digest(cs) and final['seal_sha256']==digest(seal)
    source=Path(spec['source_run'])
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    from mertens_limit_report import summary as parent_summary
    parent_summary(source)
    assert final['uniform_RH_sufficient_signed_controls_verified']==checked['uniform_RH_sufficient_signed_controls_verified']==[]
    assert not final['RH_proved'] and spec['not_autonomous_proof_invention'] and not spec['new_prime_distribution_estimate_imported']
    outcomes={o['candidate_id']:o for o in final['outcomes']};bs={b['id']:b for b in batch['banks']};ps={p['id']:p for p in batch['programs']};records=[]
    for c in arc['archive']:
        b=bs[c['bank_id']];o=outcomes[c['id']];assert not o['uniform_signed_premise_proved']
        records.append({'candidate':c,'bank':b,'programs':[ps[i] for i in b['member_ids']],'final_outcome':o})
    survivors=[r for r in records if r['candidate']['RH_sufficient_if_uniform'] and r['final_outcome']['finite_points_passed']]
    joint=[b for b in batch['banks'] if len(b['member_ids'])>1 and b['recovery_certificate']['all_height_no_common_zero']]
    return {'status':'verified_scoped_complete_tail_kernel_search','run_directory':str(directory),
        'program_count':len(batch['programs']),'bank_count':len(batch['banks']),
        'growth_frontier_hypotheses':sum(c['bank_id'] in bs for c in batch['candidates']),
        'all_primary_and_ablation_hypotheses':len(batch['candidates']),
        'joint_banks_with_all_height_recovery':len(joint),
        'joint_banks_including_individually_uncertified_kernels':sum(b['contains_individually_uncertified_member'] for b in joint),
        'records':records,'RH_if_uniform_finite_survivors':survivors,
        'counterfeit_controls':final['counterfeit_controls'],
        'counterfeit_finite_successes_analytically_rejected':sum(o['finite_points_passed'] for o in final['counterfeit_controls']),
        'ablation_comparison':arc['ablation_comparison'],'independent_native_counts':checked['counts'],
        'named_calibration_dependencies':spec['named_calibration_dependencies'],
        'constants_in_q_restricted':False,'finite_q_grid_suffices':False,
        'complete_infinite_arithmetic_tails_enclosed':True,'proved_growth_exponent':'1',
        'signed_RH_growth_frontier_uniformly_proved':False,
        'automatic_global_attempts_leave_signed_gap':True,'new_independent_prime_distribution_estimate':False,
        'verified_checks':len(checked['checks']),'verification_sha256':sha(directory/'verification.json'),
        'machine_formalized':False,'not_autonomous_proof_invention':True,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False}


def load_latest():
    pointer=BASE/'mellin-kernel-results/latest.json'
    return summary(read(pointer)['run_directory']) if pointer.exists() else {'status':'not_run'}
