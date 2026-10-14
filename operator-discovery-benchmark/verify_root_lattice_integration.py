#!/usr/bin/env python3
"""Read-only stage loading, proof scope, retained failures and exact snapshots."""
import hashlib,importlib,json
from pathlib import Path

BASE=Path(__file__).resolve().parent
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text())


def main():
    modules=['autonomous_report','compensated_shift_report','signed_control_report','stable_scale_report',
        'signed_mellin_transfer','mellin_search_report','signed_defect_report','fractional_moment_report',
        'fractional_zeta_branch_audit','signed_global_calibration','pole_neutral_report','parameter_jet_report',
        'prime_error_report','prime_discrepancy_report','prime_twist_report','prime_twist_coverage_report',
        'prime_oscillation_report','fractional_remainder_report','mertens_limit_report','mellin_kernel_report',
        'kernel_correlation_report','lattice_synthesis_report','root_lattice_report'];loaded={};records=[]
    for name in modules:
        r=importlib.import_module(name).load_latest();loaded[name]=r;assert r['status']!='not_run' and not r.get('RH_proved',False)
        checks=r.get('checks');flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({'loader':name,'status':r['status'],'verification_sha256':r.get('verification_sha256'),
            'checks_passed':sum(checks.values()) if flat else r.get('verified_checks'),'checks_total':len(checks) if flat else r.get('verified_checks')})
    registry=read(BASE/'root-results/candidate_registry.json');s=loaded['root_lattice_report'];d=Path(s['run_directory'])
    assert len(records)==23 and registry['normalized_root_arithmetic_and_signed_profile_learning']==s
    assert registry['typed_lattice_global_estimate_synthesis_and_fractional_banks']==loaded['lattice_synthesis_report']
    assert registry['verified_arithmetic_consequence_count']==20 and registry['full_coefficient_origin_native_zeta_comparison_groups']==150
    assert (BASE/'operator_candidates.txt').read_text().splitlines()[0].startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES')
    assert registry['uniform_RH_sufficient_signed_controls_verified']==registry['uniform_sublinear_signed_controls_verified']==[] and not registry['historical_priority_is_acceptance_gate']
    assert s['all_infinite_actual_arithmetic_positions_included'] and s['arbitrary_positive_rational_arithmetic_dilations_supported'] and s['arbitrary_positive_rational_smoothing_orders_supported'] and not s['semantic_denominator_cap']
    assert s['actual_weak_ordinary_zeta_exponent']=='1' and s['cofinal_constants_free_for_every_q'] and not s['finite_q_grid_suffices']
    assert s['known_signed_collapse_is_calibration_only'] and not s['proved_actual_rapid_estimates_retain_ordinary_zeta_information']
    assert not s['counterfeit_tails_are_actual_counterexamples'] and not s['new_independent_prime_distribution_estimate'] and not s['machine_formalized']
    spec=read(d/'protocol.json');audit=read(d/'verification.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');assert all(audit['checks'].values()) and len(audit['checks'])==s['verified_checks']
    assert len(batch['programs'])==s['program_count'] and len(arc['archive'])==len(s['records']) and Path(spec['source_run'])==Path(loaded['lattice_synthesis_report']['run_directory'])
    assert not audit['mathematical_audit_imports_production_code'] and not spec['generator_model_literature_network_access'] and spec['not_autonomous_proof_invention']
    assert {'1/2','1/3','1/6'}<=set(s['arithmetic_dilation_factors'])
    for row in s['recovering_records']:
        assert not row['candidate']['uniform_frontier_has_proved_constant_witness'] and row['program']['zero_bridge']['ordinary_zeta_information_preserved']
    for row in s['signed_calibration_records']:
        assert not row['candidate']['RH_sufficient_if_uniform'] and row['candidate']['uniform_frontier_has_proved_constant_witness']
    milestones=[]
    for dirname,checker in [('prime-twist-results/pilot-001','verify_prime_twist_integration.py'),
        ('prime-oscillation-results/audit-001','verify_prime_oscillation_integration.py'),
        ('fractional-remainder-results/pilot-002','verify_fractional_remainder_integration.py'),
        ('mellin-kernel-results/pilot-001','verify_mellin_kernel_integration.py'),
        ('kernel-correlation-results/pilot-002','verify_kernel_correlation_integration.py'),
        ('lattice-synthesis-results/pilot-002','verify_lattice_synthesis_integration.py')]:
        p=BASE/dirname/'integration_verification.json';old=read(p);snapshot=p.parent/'integration_snapshot'
        for key,name in [('driver_sha256','run_expanded_probe.py'),('registry_sha256','root-results/candidate_registry.json'),('report_sha256','root-results/report.txt'),('documentation_sha256','SIGNED_ARITHMETIC_CONTROL.md'),('integration_checker_sha256',checker)]:assert sha(snapshot/name)==old[key]
        milestones.append({'path':str(p),'sha256':sha(p),'exact_five_file_snapshot_preserved':True})
    failures=[]
    for old in spec['retained_failed_runs_are_development']:
        failed=Path(old['run_directory']);assert sha(failed/'failure.json')==old['failure_sha256']
        for n,h in old['retained_files_sha256'].items():assert sha(failed/n)==h
        failedspec=read(failed/'protocol.json');assert failedspec['code_sha256']==old['original_code_sha256']
        for n in failedspec['this_stage_source_files']:assert sha(failed/'frozen_source'/n)==failedspec['code_sha256'][n]
        failures.append({'run_directory':str(failed),'artifacts_and_original_source_preserved':True})
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    observations=read(d/'plot_observations.json')
    for key,name in [('source_protocol_sha256','protocol.json'),('source_archive_sha256','archive.json'),('source_final_sha256','final_evaluation.json'),('source_verification_sha256','verification.json')]:assert observations[key]==sha(d/name)
    assert observations['complete_infinite_arithmetic_values_used'] and observations['scales_normalized_to_ordinary_index']
    assert observations['signed_reference_is_actual_inverse_arithmetic'] and observations['signed_rapid_bound_erases_ordinary_zeta'] and observations['root_dashed_curves_are_fitted_only'] and not observations['RH_proved']
    report=(BASE/'root-results/report.txt').read_text();doc=(BASE/'SIGNED_ARITHMETIC_CONTROL.md').read_text()
    assert 'NORMALIZED ARITHMETIC ROOTS AND SIGNED PROFILE LEARNING' in report and 'Normalized arithmetic roots and signed profile learning' in doc
    result={'status':'integration_verified_research_goal_still_active','objective':registry['objective'],
        'driver_sha256':sha(BASE/'run_expanded_probe.py'),'registry_sha256':sha(BASE/'root-results/candidate_registry.json'),'report_sha256':sha(BASE/'root-results/report.txt'),
        'documentation_sha256':sha(BASE/'SIGNED_ARITHMETIC_CONTROL.md'),'integration_checker_sha256':sha(BASE/'verify_root_lattice_integration.py'),
        'strict_loaders_checked':records,'legacy_catalogue_scoped_counts':{'families':10,'consequences':20,'native_groups':150},'legacy_catalogue_sha256':sha(BASE/'operator_candidates.txt'),
        'prior_integration_milestones_and_snapshots':milestones,'retained_failed_runs_revalidated':failures,
        'root_arithmetic_scope':{k:s[k] for k in ['program_count','semantic_operator_count','growth_hypotheses','primary_and_ablation_hypotheses','parameter_contexts','arithmetic_dilation_factors',
            'recovering_root_programs','zero_erasing_signed_programs','learned_actual_response_programs','anonymous_moment_relation_records','universal_actual_moment_relations',
            'compiled_actual_arithmetic_promotions','proved_signed_actual_rapid_estimates','false_RH_inferences_rejected','ablation_comparison','promotion_improved_best_charged_recovery']},
        'native_check_counts':audit['counts'],'this_stage_frozen_source_sha256':{n:sha(BASE/n) for n in spec['this_stage_source_files']},
        'public_contract_checks':{'cases':14,'source_sha256':sha(BASE/'test_root_lattice_contracts.py')},
        'standalone_evidence_plot':{'source_sha256':sha(BASE/'plot_root_lattices.py'),'png_sha256':sha(d/'root_lattice_evidence.png'),'pdf_sha256':sha(d/'root_lattice_evidence.pdf'),'observations_sha256':sha(d/'plot_observations.json')},
        'scoped_report_sha256':sha(d/'report.txt'),'named_calibration_dependencies':spec['named_calibration_dependencies'],'source_producer_reruns_for_integration':False,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False,
        'completion_audit':'Not achieved: fractional arithmetic roots, actual-response learning and signed profile proof synthesis are verified; known all-scale signed collapse erases ordinary zeta, and recovering critical uniform arithmetic estimates remain unproved.'}
    destination=d/'integration_verification.json'
    if destination.exists():raise FileExistsError('Retain the integration milestone')
    destination.write_text(json.dumps(result,indent=2)+'\n');snapshot=d/'integration_snapshot';snapshot.mkdir(exist_ok=False)
    for name in ['run_expanded_probe.py','root-results/candidate_registry.json','root-results/report.txt','SIGNED_ARITHMETIC_CONTROL.md','verify_root_lattice_integration.py']:
        target=snapshot/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((BASE/name).read_bytes())
    print('23 scoped loaders verified; exact prior and current integration snapshots retained.')
    print('Root arithmetic and signed proof synthesis verified. Recovering critical signed bounds remain open.')


if __name__=='__main__':main()
