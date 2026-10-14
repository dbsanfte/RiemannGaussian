"""Read-only integration audit of twenty-one separately scoped loaders."""
import hashlib,importlib,json
from pathlib import Path

BASE=Path(__file__).resolve().parent


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text())


def main():
    modules=['autonomous_report','compensated_shift_report','signed_control_report',
        'stable_scale_report','signed_mellin_transfer','mellin_search_report','signed_defect_report',
        'fractional_moment_report','fractional_zeta_branch_audit','signed_global_calibration',
        'pole_neutral_report','parameter_jet_report','prime_error_report','prime_discrepancy_report',
        'prime_twist_report','prime_twist_coverage_report','prime_oscillation_report','fractional_remainder_report',
        'mertens_limit_report','mellin_kernel_report','kernel_correlation_report']
    loaded={};records=[]
    for name in modules:
        r=importlib.import_module(name).load_latest();loaded[name]=r
        assert r['status']!='not_run' and not r.get('RH_proved',False)
        checks=r.get('checks');flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({'loader':name,'status':r['status'],'verification_sha256':r.get('verification_sha256'),
            'checks_passed':sum(checks.values()) if flat else r.get('verified_checks'),
            'checks_total':len(checks) if flat else r.get('verified_checks')})
    registry=read(BASE/'root-results/candidate_registry.json');r=loaded['kernel_correlation_report'];d=Path(r['run_directory'])
    assert len(records)==21 and registry['complete_signed_Gram_and_squarefree_density_search']==r
    assert registry['complete_tail_Mellin_kernel_frontier_search']==loaded['mellin_kernel_report']
    assert registry['verified_arithmetic_consequence_count']==20 and registry['full_coefficient_origin_native_zeta_comparison_groups']==150
    assert (BASE/'operator_candidates.txt').read_text().splitlines()[0].startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES')
    assert registry['uniform_RH_sufficient_signed_controls_verified']==registry['uniform_sublinear_signed_controls_verified']==[]
    assert not registry['historical_priority_is_acceptance_gate']
    assert r['complete_infinite_arithmetic_tails_enclosed'] and not r['constants_in_q_restricted'] and not r['finite_q_grid_suffices']
    assert r['all_real_scale_signed_diagonal_remainder_proved'] and r['proved_diagonal_remainder_exponent']=='1/2' and r['unproved_RH_density_remainder_exponent']=='1/4'
    assert r['proved_full_response_exponent']=='1' and not r['off_diagonal_RH_uniform_premise_proved'] and not r['density_quarter_power_uniform_premise_proved']
    assert not r['new_independent_prime_distribution_estimate'] and r['not_autonomous_proof_invention'] and not r['machine_formalized']
    assert r['ablation_comparison']['equal_promotion_slot_budgets'] and r['uniform_RH_sufficient_signed_controls_verified']==[]
    spec=read(d/'protocol.json');audit=read(d/'verification.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json')
    assert all(audit['checks'].values()) and len(audit['checks'])==r['verified_checks'] and audit['replay_sha256']
    assert len(batch['programs'])==r['program_count'] and len(arc['archive'])==len(r['records'])
    assert Path(spec['source_run'])==Path(loaded['mellin_kernel_report']['run_directory'])
    assert not audit['mathematical_audit_imports_production_code'] and audit['reflection_bridge_audit']['actual_zero_input_used'] is False
    milestones=[]
    prior=[('prime-twist-results/pilot-001','verify_prime_twist_integration.py'),
        ('prime-oscillation-results/audit-001','verify_prime_oscillation_integration.py'),
        ('fractional-remainder-results/pilot-002','verify_fractional_remainder_integration.py'),
        ('mellin-kernel-results/pilot-001','verify_mellin_kernel_integration.py')]
    for dirname,checker in prior:
        p=BASE/dirname/'integration_verification.json';old=read(p);snapshot=p.parent/'integration_snapshot'
        mapping={'driver_sha256':'run_expanded_probe.py','registry_sha256':'root-results/candidate_registry.json',
            'report_sha256':'root-results/report.txt','documentation_sha256':'SIGNED_ARITHMETIC_CONTROL.md','integration_checker_sha256':checker}
        for key,name in mapping.items():assert sha(snapshot/name)==old[key]
        milestones.append({'path':str(p),'sha256':sha(p),'exact_five_file_snapshot_preserved':True})
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    for n in spec['this_stage_source_files']:assert sha(d/'frozen_source'/n)==spec['code_sha256'][n]
    retained_failures=[]
    for old in spec['retained_failed_runs_are_development']:
        failed=Path(old['run_directory']);assert sha(failed/'failure.json')==old['failure_sha256']
        for n,h in old['retained_files_sha256'].items():assert sha(failed/n)==h
        failedspec=read(failed/'protocol.json');assert failedspec['code_sha256']==old['original_code_sha256']
        for n in failedspec['this_stage_source_files']:assert sha(failed/'frozen_source'/n)==failedspec['code_sha256'][n]
        assert read(failed/'final_cases.json')['integers']==old['excluded_final_scales']
        assert read(failed/'parameter_cases.json')['fresh_q']==old['excluded_final_q']
        retained_failures.append({'run_directory':str(failed),'artifacts_and_original_source_preserved':True,'old_final_cases_excluded':True})
    observations=read(d/'plot_observations.json')
    for key,name in [('source_protocol_sha256','protocol.json'),('source_archive_sha256','archive.json'),
        ('source_final_sha256','final_evaluation.json'),('source_verification_sha256','verification.json')]:assert observations[key]==sha(d/name)
    assert observations['complete_infinite_arithmetic_values_used'] and observations['density_green_curve_is_proved_global_sqrt_bound']
    assert observations['density_dashed_curve_is_only_fitted'] and observations['observer_panel_is_conditional']
    assert observations['finite_cases_do_not_prove_uniform_growth'] and not observations['RH_proved']
    report=(BASE/'root-results/report.txt').read_text();doc=(BASE/'SIGNED_ARITHMETIC_CONTROL.md').read_text()
    assert 'COMPLETE SIGNED GRAM CORRELATIONS AND SQUAREFREE DENSITY CORRECTIONS' in report
    assert 'Complete signed correlations and squarefree density corrections' in doc
    result={'status':'integration_verified_research_goal_still_active','objective':registry['objective'],
        'driver_sha256':sha(BASE/'run_expanded_probe.py'),'registry_sha256':sha(BASE/'root-results/candidate_registry.json'),
        'report_sha256':sha(BASE/'root-results/report.txt'),'documentation_sha256':sha(BASE/'SIGNED_ARITHMETIC_CONTROL.md'),
        'integration_checker_sha256':sha(BASE/'verify_kernel_correlation_integration.py'),'strict_loaders_checked':records,
        'legacy_catalogue_scoped_counts':{'families':10,'consequences':20,'native_groups':150},
        'legacy_catalogue_sha256':sha(BASE/'operator_candidates.txt'),'prior_integration_milestones_and_snapshots':milestones,
        'retained_failed_runs_revalidated':retained_failures,
        'signed_Gram_density_scope':{k:r[k] for k in ['program_count','program_counts_by_kind','growth_hypotheses','primary_and_ablation_hypotheses',
            'recovering_energy_programs','recovering_density_programs','recovering_singular_energy_programs','indefinite_programs_preserved',
            'false_controls_finite_passes_analytically_rejected','ablation_comparison']},
        'RH_if_uniform_finite_survivors':len(r['RH_if_uniform_finite_survivors']),
        'native_check_counts':audit['counts'],'reflection_bridge_audit':audit['reflection_bridge_audit'],
        'this_stage_frozen_source_sha256':{n:sha(BASE/n) for n in spec['this_stage_source_files']},
        'public_contract_checks':{'cases':13,'source_sha256':sha(BASE/'test_kernel_correlation_contracts.py')},
        'standalone_evidence_plot':{'source_sha256':sha(BASE/'plot_kernel_correlations.py'),
            'png_sha256':sha(d/'kernel_correlation_evidence.png'),'pdf_sha256':sha(d/'kernel_correlation_evidence.pdf'),
            'observations_sha256':sha(d/'plot_observations.json')},
        'scoped_report_sha256':sha(d/'report.txt'),'named_calibration_dependencies':spec['named_calibration_dependencies'],
        'source_producer_reruns_for_integration':False,'historical_priority_is_acceptance_gate':False,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False,
        'completion_audit':'Not achieved: actual signed diagonal corrections have a true all-scale square-root bound and all-height quarter-power recovery, but RH-strength uniform signed correlation and density estimates remain unproved.'}
    destination=d/'integration_verification.json'
    if destination.exists():raise FileExistsError('Retain the integration milestone')
    destination.write_text(json.dumps(result,indent=2)+'\n')
    snapshot=d/'integration_snapshot';snapshot.mkdir(exist_ok=False)
    for name in ['run_expanded_probe.py','root-results/candidate_registry.json','root-results/report.txt','SIGNED_ARITHMETIC_CONTROL.md','verify_kernel_correlation_integration.py']:
        target=snapshot/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((BASE/name).read_bytes())
    print('21 scoped loaders verified; exact 15-, 17-, 19-, 20- and 21-loader snapshots retained.')
    print('All-scale signed diagonal theorem integrated. RH-strength uniform bounds remain open.')


if __name__=='__main__':main()
