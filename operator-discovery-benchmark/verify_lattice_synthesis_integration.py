"""Read-only audit of twenty-two scoped loaders and exact prior snapshots."""
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
        'kernel_correlation_report','lattice_synthesis_report'];loaded={};records=[]
    for name in modules:
        r=importlib.import_module(name).load_latest();loaded[name]=r;assert r['status']!='not_run' and not r.get('RH_proved',False)
        checks=r.get('checks');flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({'loader':name,'status':r['status'],'verification_sha256':r.get('verification_sha256'),
            'checks_passed':sum(checks.values()) if flat else r.get('verified_checks'),'checks_total':len(checks) if flat else r.get('verified_checks')})
    registry=read(BASE/'root-results/candidate_registry.json');s=loaded['lattice_synthesis_report'];d=Path(s['run_directory'])
    assert len(records)==22 and registry['typed_lattice_global_estimate_synthesis_and_fractional_banks']==s
    assert registry['complete_signed_Gram_and_squarefree_density_search']==loaded['kernel_correlation_report']
    assert registry['verified_arithmetic_consequence_count']==20 and registry['full_coefficient_origin_native_zeta_comparison_groups']==150
    assert (BASE/'operator_candidates.txt').read_text().splitlines()[0].startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES')
    assert registry['uniform_RH_sufficient_signed_controls_verified']==registry['uniform_sublinear_signed_controls_verified']==[] and not registry['historical_priority_is_acceptance_gate']
    assert s['all_infinite_actual_arithmetic_positions_included'] and s['arbitrary_rational_arithmetic_dilation_above_one_supported'] and s['arbitrary_positive_rational_root_orders_supported']
    assert s['unit_reference_negative_powers_proved_globally'] and not s['actual_inverse_negative_powers_proved']
    assert s['actual_weak_ordinary_zeta_exponent']=='1' and s['post_rewrite_absolute_norm_cannot_reach_RH_strength'] and not s['barrier_is_counterexample_to_actual_growth']
    assert s['cofinal_constants_free_for_every_q_and_member'] and not s['finite_q_grid_suffices'] and not s['new_independent_prime_distribution_estimate'] and not s['machine_formalized']
    spec=read(d/'protocol.json');audit=read(d/'verification.json');batch=read(d/'candidate_batch.json');arc=read(d/'archive.json');assert all(audit['checks'].values()) and len(audit['checks'])==s['verified_checks']
    assert len(batch['programs'])==s['program_count'] and len(arc['archive'])==len(s['records']) and len(arc['banks'])==s['complementary_RH_banks']
    assert Path(spec['source_run'])==Path(loaded['kernel_correlation_report']['run_directory']) and not audit['mathematical_audit_imports_production_code']
    milestones=[]
    for dirname,checker in [('prime-twist-results/pilot-001','verify_prime_twist_integration.py'),
        ('prime-oscillation-results/audit-001','verify_prime_oscillation_integration.py'),
        ('fractional-remainder-results/pilot-002','verify_fractional_remainder_integration.py'),
        ('mellin-kernel-results/pilot-001','verify_mellin_kernel_integration.py'),
        ('kernel-correlation-results/pilot-002','verify_kernel_correlation_integration.py')]:
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
    assert observations['complete_infinite_arithmetic_values_used'] and observations['reference_curve_is_proved_unit_bound_only'] and observations['actual_solid_curve_is_weak_global_bound']
    assert observations['actual_dashed_curve_is_fitted_only'] and observations['exception_sets_are_conditional_on_unproved_actual_bounds'] and not observations['RH_proved']
    report=(BASE/'root-results/report.txt').read_text();doc=(BASE/'SIGNED_ARITHMETIC_CONTROL.md').read_text();assert 'TYPED LATTICE GLOBAL ESTIMATE SYNTHESIS AND FRACTIONAL DILATION BANKS' in report and 'Typed lattice synthesis and complementary fractional dilations' in doc
    roots=read(d/'fractional_root_calibration.json');assert roots['all_passed'] and roots['phase']=='post_run_generic_semantic_calibration'
    assert roots['source_protocol_sha256']==sha(d/'protocol.json') and roots['source_verification_sha256']==sha(d/'verification.json')
    assert roots['calibrator_sha256']==sha(BASE/'lattice_fractional_root_audit.py') and roots['producer_grammar_sha256']==sha(BASE/'lattice_synthesis_grammar.py') and roots['independent_checker_sha256']==sha(BASE/'check_lattice_synthesis.py')
    assert [r['root_order'] for r in roots['cases']]==[2,3,6,10007] and not roots['selection_or_fitted_constants_changed'] and not roots['new_fresh_discovery_claim']
    assert all(r['complete_independent_arithmetic_passed'] and not r['actual_critical_uniform_estimate_proved'] for r in roots['cases'])
    result={'status':'integration_verified_research_goal_still_active','objective':registry['objective'],
        'driver_sha256':sha(BASE/'run_expanded_probe.py'),'registry_sha256':sha(BASE/'root-results/candidate_registry.json'),'report_sha256':sha(BASE/'root-results/report.txt'),
        'documentation_sha256':sha(BASE/'SIGNED_ARITHMETIC_CONTROL.md'),'integration_checker_sha256':sha(BASE/'verify_lattice_synthesis_integration.py'),
        'strict_loaders_checked':records,'legacy_catalogue_scoped_counts':{'families':10,'consequences':20,'native_groups':150},'legacy_catalogue_sha256':sha(BASE/'operator_candidates.txt'),
        'prior_integration_milestones_and_snapshots':milestones,'retained_failed_runs_revalidated':failures,
        'typed_lattice_scope':{k:s[k] for k in ['program_count','growth_hypotheses','primary_and_ablation_hypotheses','parameter_contexts','fractional_dilation_factors',
            'learned_anonymous_programs','learned_exact_two_pole_annihilators','proved_reference_global_estimates','actual_support_sign_loss_barriers','complementary_RH_banks','complementary_RH_banks_finite_passes','typed_arithmetic_aliases_rejected','ablation_comparison']},
        'native_check_counts':audit['counts'],'this_stage_frozen_source_sha256':{n:sha(BASE/n) for n in spec['this_stage_source_files']},
        'public_contract_checks':{'cases':16,'source_sha256':sha(BASE/'test_lattice_synthesis_contracts.py')},
        'generic_fractional_root_semantic_calibration':{'sha256':sha(d/'fractional_root_calibration.json'),'source_sha256':sha(BASE/'lattice_fractional_root_audit.py'),'root_orders':[2,3,6,10007],'post_run_no_reselection':True,'native_counts':roots['counts']},
        'standalone_evidence_plot':{'source_sha256':sha(BASE/'plot_lattice_synthesis.py'),'png_sha256':sha(d/'lattice_synthesis_evidence.png'),'pdf_sha256':sha(d/'lattice_synthesis_evidence.pdf'),'observations_sha256':sha(d/'plot_observations.json')},
        'scoped_report_sha256':sha(d/'report.txt'),'named_calibration_dependencies':spec['named_calibration_dependencies'],'source_producer_reruns_for_integration':False,
        'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False,
        'completion_audit':'Not achieved: globally certified unit-reference decay and a true actual sign-loss barrier improve estimate discovery and proof scope; actual signed critical uniform estimates for the complementary RH banks remain unproved.'}
    destination=d/'integration_verification.json'
    if destination.exists():raise FileExistsError('Retain the integration milestone')
    destination.write_text(json.dumps(result,indent=2)+'\n');snapshot=d/'integration_snapshot';snapshot.mkdir(exist_ok=False)
    for name in ['run_expanded_probe.py','root-results/candidate_registry.json','root-results/report.txt','SIGNED_ARITHMETIC_CONTROL.md','verify_lattice_synthesis_integration.py']:
        target=snapshot/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((BASE/name).read_bytes())
    print('22 scoped loaders verified; exact prior and current integration snapshots retained.')
    print('Reference global estimates and actual sign-loss barriers verified. Critical signed arithmetic bounds remain open.')


if __name__=='__main__':main()
