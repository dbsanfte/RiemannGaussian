#!/usr/bin/env python3
"""Verify independent constant laws, signed gaps and preserved earlier evidence."""
import hashlib,importlib,json
from pathlib import Path
BASE=Path(__file__).resolve().parent
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    previous_path=BASE/'divisor-dual-results/pilot-001/integration_verification.json';previous=read(previous_path);modules=[r['loader'] for r in previous['strict_loaders_checked']]+['signed_gap_profile_report'];loaded={};records=[]
    for name in modules:
        s=importlib.import_module(name).load_latest();assert s['status']!='not_run' and not s.get('RH_proved',False);loaded[name]=s;checks=s.get('checks');flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({'loader':name,'status':s['status'],'verification_sha256':s.get('verification_sha256'),'checks_passed':sum(checks.values()) if flat else s.get('verified_checks'),'checks_total':len(checks) if flat else s.get('verified_checks')})
    assert len(records)==28;registry=read(BASE/'root-results/candidate_registry.json');s=loaded['signed_gap_profile_report'];d=Path(s['run_directory']);spec=read(d/'protocol.json');v=read(d/'verification.json');av=read(d/'analytical_verification.json');a=read(d/'analytical_review.json');q=read(d/'proof_queue.json');f=read(d/'final_evaluation.json')
    from divisor_dual_analytic_report import load_latest as analytical
    olda=analytical();assert registry['separate_analytical_review_of_detector_candidates']==olda and Path(olda['review_directory'])==Path(spec['source_analytical_review']) and registry['divisor_dual_full_defect_candidates_and_frozen_proof_queue']==loaded['divisor_dual_report'] and Path(spec['source_run'])==Path(loaded['divisor_dual_report']['run_directory'])
    assert registry['independent_constant_profiles_and_actual_signed_nullspace_gap']==s and registry['verified_arithmetic_consequence_count']==20 and registry['full_coefficient_origin_native_zeta_comparison_groups']==150 and (BASE/'operator_candidates.txt').read_text().splitlines()[0].startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES')
    assert registry['uniform_RH_sufficient_signed_controls_verified']==registry['uniform_sublinear_signed_controls_verified']==[] and not registry['historical_priority_is_acceptance_gate']
    assert s['exponent_and_constant_growth_decoupled'] and s['existential_per_level_constants_supported'] and s['unseen_level_constants_are_missing_not_fitted_predictions'] and s['proof_queue_candidates']==len(q['queue'])==len(a['candidate_attempts'])
    assert s['global_binary_prefix_minimum_bound_proved']==a['minimum_proof_certificate']['global_binary_prefix_minimum_bound_proved'] and s['quantitative_tail_obstruction_has_no_position_assumption'] and s['critical_tail_omission_power_ceiling']=='1/2'
    assert s['positive_r_can_still_impose_critical_zero_simplicity'] and s['critical_multiplicity_scope_is_conditional'] and s['global_generic_energy_power']=='3' and not s['global_actual_critical_signed_gap_proved'] and not s['new_independent_prime_distribution_estimate'] and not s['semantic_denominator_cap'] and not s['machine_formalized']
    assert v['all_passed'] and av['all_passed'] and all(v['checks'].values()) and all(av['checks'].values()) and not v['mathematical_audit_imports_production_code'] and not av['mathematical_audit_imports_production_code'] and len(v['checks'])==s['verified_checks'] and len(av['checks'])==s['analytical_verified_checks']
    assert s['fresh_actual_coefficient_cutoff']==f['arithmetic']['cutoff'] and s['fresh_positive_actual_defects']==sum(r['signed_defect']>0 for r in f['arithmetic']['rows']) and s['fresh_missing_constants']>0 and s['fresh_actual_observations']==sum(len(r['observations']) for r in f['program_results'])
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    milestones=[];paths=[Path(r['path']) for r in previous['prior_integration_milestones_and_snapshots']]+[previous_path]
    for p in paths:
        old=read(p);snapshot=p.parent/'integration_snapshot';checkers=list(snapshot.glob('verify_*_integration.py'));assert len(checkers)==1
        for key,name in [('driver_sha256','run_expanded_probe.py'),('registry_sha256','root-results/candidate_registry.json'),('report_sha256','root-results/report.txt'),('documentation_sha256','SIGNED_ARITHMETIC_CONTROL.md')]:assert sha(snapshot/name)==old[key]
        assert sha(checkers[0])==old['integration_checker_sha256'];milestones.append({'path':str(p),'sha256':sha(p),'exact_five_file_snapshot_preserved':True})
    plots=read(d/'plot_observations.json')
    for key,n in [('source_protocol_sha256','protocol.json'),('source_final_sha256','final_evaluation.json'),('source_queue_sha256','proof_queue.json'),('source_verification_sha256','verification.json'),('source_analytical_sha256','analytical_review.json'),('source_analytical_verification_sha256','analytical_verification.json')]:assert plots[key]==sha(d/n)
    assert plots['actual_signed_arithmetic_kept'] and plots['new_constants_not_fit_from_final'] and not plots['new_case_fit_or_selection'] and not plots['global_critical_signed_bound_proved'] and not plots['RH_proved']
    assert 'INDEPENDENT CONSTANT LAWS AND ACTUAL LARGE-SCALE SIGNED GAPS' in (BASE/'root-results/report.txt').read_text() and 'Independent constants and direct tests of the actual signed gap' in (BASE/'SIGNED_ARITHMETIC_CONTROL.md').read_text()
    result={'status':'integration_verified_research_goal_still_active','objective':registry['objective'],'driver_sha256':sha(BASE/'run_expanded_probe.py'),'registry_sha256':sha(BASE/'root-results/candidate_registry.json'),'report_sha256':sha(BASE/'root-results/report.txt'),'documentation_sha256':sha(BASE/'SIGNED_ARITHMETIC_CONTROL.md'),'integration_checker_sha256':sha(BASE/'verify_signed_gap_profile_integration.py'),
        'strict_loaders_checked':records,'preserved_separate_analytical_extension':{'loader':'divisor_dual_analytic_report','status':olda['status'],'verification_sha256':olda['verification_sha256']},
        'legacy_catalogue_scoped_counts':{'families':10,'consequences':20,'native_groups':150},'legacy_catalogue_sha256':sha(BASE/'operator_candidates.txt'),'prior_integration_milestones_and_snapshots':milestones,
        'signed_gap_scope':{k:s[k] for k in ['program_count','exponent_schedule_count','constant_law_count','log_powers','proof_queue_candidates','fresh_scales','fresh_new_levels','fresh_actual_coefficient_cutoff','fresh_actual_observations','fresh_half_gap_passes','fresh_missing_constants','conditional_simplicity_restricting_candidates']},
        'global_combinatorial_bound_terms':s['anonymous_minimum_bound_terms'],'global_combinatorial_bound_not_global_prime_control':True,'independent_arithmetic_counts':v['counts'],'independent_analytical_counts':av['counts'],'this_stage_frozen_source_sha256':{n:sha(BASE/n) for n in spec['this_stage_source_files']},
        'public_contract_checks':{'cases':18,'source_sha256':sha(BASE/'test_signed_gap_profile_contracts.py')},'standalone_evidence_plot':{'source_sha256':sha(BASE/'plot_signed_gap_profiles.py'),'png_sha256':sha(d/'signed_gap_profile_evidence.png'),'pdf_sha256':sha(d/'signed_gap_profile_evidence.pdf'),'observations_sha256':sha(d/'plot_observations.json')},
        'scoped_report_sha256':sha(d/'report.txt'),'source_producer_reruns_for_integration':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False,
        'completion_audit':'Not achieved: flexible constant/exponent programs and large-scale actual arithmetic predictions are verified, and an inferred global binary-prefix estimate is analytically proved. All 48 actual all-scale critical signed half-gap claims remain unresolved; no RH-strength prime control is proved.'}
    destination=d/'integration_verification.json'
    if destination.exists():raise FileExistsError('Retain the integration milestone')
    destination.write_text(json.dumps(result,indent=2)+'\n');snapshot=d/'integration_snapshot';snapshot.mkdir(exist_ok=False)
    for n in ['run_expanded_probe.py','root-results/candidate_registry.json','root-results/report.txt','SIGNED_ARITHMETIC_CONTROL.md','verify_signed_gap_profile_integration.py']:
        target=snapshot/n;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((BASE/n).read_bytes())
    print('28 scoped stages and the separate prior analytical review verified; exact snapshots retained.')
    print('Learned combinatorial estimate proved; all actual all-scale critical signed gaps remain unresolved.')


if __name__=='__main__':main()
