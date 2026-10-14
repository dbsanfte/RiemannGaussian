#!/usr/bin/env python3
"""Verify the detector-to-proof cycle and preserve all earlier milestones."""
import hashlib,importlib,json
from pathlib import Path
BASE=Path(__file__).resolve().parent
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    previous_path=BASE/'critical-defect-results/pilot-001/integration_verification.json';previous=read(previous_path);modules=[r['loader'] for r in previous['strict_loaders_checked']]+['divisor_dual_report'];loaded={};records=[]
    for name in modules:
        s=importlib.import_module(name).load_latest();assert s['status']!='not_run' and not s.get('RH_proved',False);loaded[name]=s;checks=s.get('checks');flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({'loader':name,'status':s['status'],'verification_sha256':s.get('verification_sha256'),'checks_passed':sum(checks.values()) if flat else s.get('verified_checks'),'checks_total':len(checks) if flat else s.get('verified_checks')})
    assert len(records)==27;registry=read(BASE/'root-results/candidate_registry.json');s=loaded['divisor_dual_report'];d=Path(s['run_directory']);spec=read(d/'protocol.json');audit=read(d/'verification.json');arc=read(d/'archive.json');queue=read(d/'proof_queue.json')
    from divisor_dual_analytic_report import load_latest as analytical
    a=analytical();ad=Path(a['review_directory']);av=read(ad/'verification.json');ap=read(ad/'protocol.json')
    assert registry['divisor_dual_full_defect_candidates_and_frozen_proof_queue']==s and registry['separate_analytical_review_of_detector_candidates']==a and registry['critical_signed_energy_defect_and_explicit_dense_residual']==loaded['critical_defect_report']
    assert a['source_run']==str(d) and Path(spec['source_run'])==Path(loaded['critical_defect_report']['run_directory'])
    assert registry['verified_arithmetic_consequence_count']==20 and registry['full_coefficient_origin_native_zeta_comparison_groups']==150 and (BASE/'operator_candidates.txt').read_text().splitlines()[0].startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES')
    assert registry['uniform_RH_sufficient_signed_controls_verified']==registry['uniform_sublinear_signed_controls_verified']==[] and not registry['historical_priority_is_acceptance_gate']
    assert s['program_count']==len(read(d/'candidate_batch.json')['programs']) and s['proof_queue_candidates']==len(queue['queue'])==a['candidate_count'] and s['proof_queue_frozen_before_final'] and s['analytical_results_must_not_change_frozen_candidates']
    assert s['fully_charged_whole_signed_defect_retained'] and s['actual_prime_inverse_arithmetic_independently_checked'] and s['adaptive_mask_promotion_exercised'] and s['equal_slot_ablation_preserved']
    assert s['global_generic_energy_power']=='3' and not s['global_critical_matrix_PSD_proved'] and not s['global_full_defect_bound_proved'] and s['negative_matrix_witnesses_are_not_RH_counterexamples'] and not s['new_independent_prime_distribution_estimate']
    assert s['arbitrary_rational_exponents_have_semantics'] and not s['semantic_denominator_cap'] and s['guided_features_and_certificate_methods_supplied'] and not s['machine_formalized'] and not audit['mathematical_audit_imports_production_code']
    assert a['proved_uniform_critical_candidates']==0 and a['disproved_uniform_matrix_candidates']+a['unresolved_uniform_matrix_candidates']==a['candidate_count'] and a['positive_density_uncovered_tail_obstruction_proved'] and a['quadratic_Gram_coefficient_obstruction_proved']
    assert a['exact_actual_signed_nullspace_gap_explicit'] and a['conditional_Schur_buffer_not_arithmetic_proof'] and a['source_candidates_and_selection_unchanged'] and a['polynomial_level_constant_limits_current_grammar'] and not a['global_full_signed_defect_proved'] and not av['mathematical_audit_imports_production_code']
    assert audit['all_passed'] and av['all_passed'] and all(audit['checks'].values()) and all(av['checks'].values()) and len(audit['checks'])==s['verified_checks'] and len(av['checks'])==a['verified_checks']
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n,h in ap['code_sha256'].items():assert sha(BASE/n)==h==sha(ad/'frozen_source'/n)
    assert av['source_queue_sha256']==sha(d/'proof_queue.json')==a['source_queue_sha256']
    milestones=[];paths=[Path(r['path']) for r in previous['prior_integration_milestones_and_snapshots']]+[previous_path]
    for p in paths:
        old=read(p);snapshot=p.parent/'integration_snapshot';checkers=list(snapshot.glob('verify_*_integration.py'));assert len(checkers)==1
        for key,name in [('driver_sha256','run_expanded_probe.py'),('registry_sha256','root-results/candidate_registry.json'),('report_sha256','root-results/report.txt'),('documentation_sha256','SIGNED_ARITHMETIC_CONTROL.md')]:assert sha(snapshot/name)==old[key]
        assert sha(checkers[0])==old['integration_checker_sha256'];milestones.append({'path':str(p),'sha256':sha(p),'exact_five_file_snapshot_preserved':True})
    plots=read(d/'plot_observations.json')
    for key,n in [('source_protocol_sha256','protocol.json'),('source_archive_sha256','archive.json'),('source_queue_sha256','proof_queue.json'),('source_final_sha256','final_evaluation.json'),('source_verification_sha256','verification.json')]:assert plots[key]==sha(d/n)
    assert plots['fully_charged_full_signed_defect_retained'] and not plots['new_case_fit_or_selection'] and not plots['global_critical_matrix_PSD_proved'] and not plots['RH_proved']
    assert 'DETECTOR CANDIDATES AND SEPARATE ANALYTICAL PROOF ATTEMPTS' in (BASE/'root-results/report.txt').read_text() and 'Detector candidates followed by separate analytical proof attempts' in (BASE/'SIGNED_ARITHMETIC_CONTROL.md').read_text()
    result={'status':'integration_verified_research_goal_still_active','objective':registry['objective'],'driver_sha256':sha(BASE/'run_expanded_probe.py'),'registry_sha256':sha(BASE/'root-results/candidate_registry.json'),'report_sha256':sha(BASE/'root-results/report.txt'),'documentation_sha256':sha(BASE/'SIGNED_ARITHMETIC_CONTROL.md'),'integration_checker_sha256':sha(BASE/'verify_divisor_dual_integration.py'),
        'strict_loaders_checked':records,'separate_analytical_extension':{'loader':'divisor_dual_analytic_report','status':a['status'],'verification_sha256':sha(ad/'verification.json'),'checks_passed':len(av['checks']),'checks_total':len(av['checks']),'source_queue_sha256':sha(d/'proof_queue.json')},
        'legacy_catalogue_scoped_counts':{'families':10,'consequences':20,'native_groups':150},'legacy_catalogue_sha256':sha(BASE/'operator_candidates.txt'),'prior_integration_milestones_and_snapshots':milestones,
        'detector_and_proof_scope':{k:s[k] for k in ['program_count','proof_queue_candidates','learned_zero_forcing_masks','fresh_scales','fresh_levels','fresh_matrix_cases','fresh_positive_matrices','fresh_negative_matrix_directions']},
        'analytical_dispositions':{k:a[k] for k in ['candidate_count','proved_uniform_critical_candidates','disproved_uniform_matrix_candidates','unresolved_uniform_matrix_candidates','polynomial_level_constant_limits_current_grammar']},
        'independent_matrix_counts':audit['counts'],'independent_analytical_counts':av['counts'],'this_stage_frozen_source_sha256':{n:sha(BASE/n) for n in spec['this_stage_source_files']},'analytical_extension_source_sha256':ap['code_sha256'],
        'public_contract_checks':{'detector_cases':17,'analytical_cases':6,'detector_source_sha256':sha(BASE/'test_divisor_dual_contracts.py'),'analytical_source_sha256':sha(BASE/'test_divisor_dual_analytic_contracts.py')},
        'standalone_evidence_plot':{'source_sha256':sha(BASE/'plot_divisor_dual.py'),'png_sha256':sha(d/'divisor_dual_evidence.png'),'pdf_sha256':sha(d/'divisor_dual_evidence.pdf'),'observations_sha256':sha(d/'plot_observations.json')},
        'scoped_report_sha256':sha(d/'report.txt'),'analytical_report_sha256':sha(ad/'report.txt'),'source_producer_reruns_for_integration':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False,
        'completion_audit':'Not achieved: exact detector leads and separate analytical proof attempts are implemented; six uniform PSD claims are disproved and six full-nonunit-Gram claims retain an unresolved actual signed nullspace bound. No all-scale critical signed inequality has been proved.'}
    destination=d/'integration_verification.json'
    if destination.exists():raise FileExistsError('Retain the integration milestone')
    destination.write_text(json.dumps(result,indent=2)+'\n');snapshot=d/'integration_snapshot';snapshot.mkdir(exist_ok=False)
    for n in ['run_expanded_probe.py','root-results/candidate_registry.json','root-results/report.txt','SIGNED_ARITHMETIC_CONTROL.md','verify_divisor_dual_integration.py']:
        target=snapshot/n;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((BASE/n).read_bytes())
    print('27 scoped stages plus separate analytical review verified; exact earlier and current integration snapshots retained.')
    print('Detector-selected formulas remain frozen. Six matrix claims disproved, six unresolved; RH-strength signed control is unproved.')


if __name__=='__main__':main()
