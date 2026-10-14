#!/usr/bin/env python3
"""Verify 26 scoped stages, the full-defect gap and exact earlier snapshots."""
import hashlib,importlib,json
from pathlib import Path
BASE=Path(__file__).resolve().parent
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    previous_path=BASE/'branch-center-results/pilot-002/integration_verification.json';previous=read(previous_path);modules=[r['loader'] for r in previous['strict_loaders_checked']]+['critical_defect_report'];loaded={};records=[]
    for name in modules:
        s=importlib.import_module(name).load_latest();assert s['status']!='not_run' and not s.get('RH_proved',False);loaded[name]=s;checks=s.get('checks');flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({'loader':name,'status':s['status'],'verification_sha256':s.get('verification_sha256'),'checks_passed':sum(checks.values()) if flat else s.get('verified_checks'),'checks_total':len(checks) if flat else s.get('verified_checks')})
    assert len(records)==26;registry=read(BASE/'root-results/candidate_registry.json');s=loaded['critical_defect_report'];d=Path(s['run_directory']);spec=read(d/'protocol.json');audit=read(d/'verification.json')
    assert registry['critical_signed_energy_defect_and_explicit_dense_residual']==s and registry['complete_fractional_centers_and_signed_cofinal_parameter_families']==loaded['branch_center_report']
    assert registry['verified_arithmetic_consequence_count']==20 and registry['full_coefficient_origin_native_zeta_comparison_groups']==150
    assert (BASE/'operator_candidates.txt').read_text().splitlines()[0].startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES')
    assert registry['uniform_RH_sufficient_signed_controls_verified']==registry['uniform_sublinear_signed_controls_verified']==[] and not registry['historical_priority_is_acceptance_gate']
    assert s['cofinal_positive_epsilon_recovery_proved'] and s['all_heights_and_offcritical_multiplicities_covered'] and not s['critical_zero_simplicity_required']
    assert s['actual_mobius_arithmetic_retained'] and not s['ordinary_zeta_erased'] and s['uniform_diagonal_defect_power']=='3/2' and s['uniform_primitive_common_factor_component_proved']
    assert s['same_cutoff_in_both_scales_required'] and s['dense_signed_residual_explicitly_retained'] and not s['full_defect_bound_proved'] and s['full_absolute_envelope_power']=='3'
    assert s['arbitrary_rational_exponents_have_semantics'] and not s['semantic_denominator_cap'] and not s['new_independent_prime_distribution_estimate'] and s['guided_mathematical_audit_not_anonymous_operator_invention'] and not s['adaptive_promotion_claimed']
    assert not s['machine_formalized'] and not audit['mathematical_audit_imports_production_code'] and not audit['full_signed_defect_bound_proved'] and len(audit['checks'])==s['verified_checks'] and all(audit['checks'].values())
    assert Path(spec['source_run'])==Path(loaded['branch_center_report']['run_directory'])
    milestones=[];paths=[Path(row['path']) for row in previous['prior_integration_milestones_and_snapshots']]+[previous_path]
    for p in paths:
        old=read(p);snapshot=p.parent/'integration_snapshot';checkers=list(snapshot.glob('verify_*_integration.py'));assert len(checkers)==1
        for key,name in [('driver_sha256','run_expanded_probe.py'),('registry_sha256','root-results/candidate_registry.json'),('report_sha256','root-results/report.txt'),('documentation_sha256','SIGNED_ARITHMETIC_CONTROL.md')]:assert sha(snapshot/name)==old[key]
        assert sha(checkers[0])==old['integration_checker_sha256'];milestones.append({'path':str(p),'sha256':sha(p),'exact_five_file_snapshot_preserved':True})
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    plots=read(d/'plot_observations.json')
    for key,n in [('source_protocol_sha256','protocol.json'),('source_archive_sha256','archive.json'),('source_final_sha256','final_evaluation.json'),('source_verification_sha256','verification.json')]:assert plots[key]==sha(d/n)
    assert plots['signed_actual_arithmetic_used'] and plots['whole_signed_defect_and_dense_residual_retained'] and plots['component_bound_not_full_bound'] and not plots['new_case_fit_or_selection'] and not plots['RH_proved']
    assert 'CRITICAL SIGNED ENERGY DEFECT AND EXPLICIT DENSE RESIDUAL' in (BASE/'root-results/report.txt').read_text() and 'Current bounds strategy: the full signed energy defect' in (BASE/'SIGNED_ARITHMETIC_CONTROL.md').read_text()
    from rational_fractional_contract_report import load_latest
    assert registry['unbounded_rational_fractional_evaluation_contracts']==load_latest()
    result={'status':'integration_verified_research_goal_still_active','objective':registry['objective'],
        'driver_sha256':sha(BASE/'run_expanded_probe.py'),'registry_sha256':sha(BASE/'root-results/candidate_registry.json'),'report_sha256':sha(BASE/'root-results/report.txt'),'documentation_sha256':sha(BASE/'SIGNED_ARITHMETIC_CONTROL.md'),'integration_checker_sha256':sha(BASE/'verify_critical_defect_integration.py'),
        'strict_loaders_checked':records,'legacy_catalogue_scoped_counts':{'families':10,'consequences':20,'native_groups':150},'legacy_catalogue_sha256':sha(BASE/'operator_candidates.txt'),'prior_integration_milestones_and_snapshots':milestones,
        'critical_defect_scope':{k:s[k] for k in ['RH_target','uniform_diagonal_defect_power','cutoff_program_count','selected_cutoff_power','selected_component_power','selected_component_log_loss','dense_signed_residual_explicitly_retained','full_defect_proof_status','fresh_scales','fresh_finite_residual_passes']},
        'native_check_counts':audit['counts'],'this_stage_frozen_source_sha256':{n:sha(BASE/n) for n in spec['this_stage_source_files']},'public_contract_checks':{'cases':15,'source_sha256':sha(BASE/'test_critical_defect_contracts.py')},
        'standalone_evidence_plot':{'source_sha256':sha(BASE/'plot_critical_defects.py'),'png_sha256':sha(d/'critical_defect_evidence.png'),'pdf_sha256':sha(d/'critical_defect_evidence.pdf'),'observations_sha256':sha(d/'plot_observations.json')},
        'scoped_report_sha256':sha(d/'report.txt'),'source_producer_reruns_for_integration':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False,
        'completion_audit':'Not achieved: the diagonal and a growing primitive common-factor part have every-scale bounds, but the dense signed arithmetic residual has no proved cofinal critical upper bound; all four archived finite constants fail fresh scales.'}
    destination=d/'integration_verification.json'
    if destination.exists():raise FileExistsError('Retain the integration milestone')
    destination.write_text(json.dumps(result,indent=2)+'\n');snapshot=d/'integration_snapshot';snapshot.mkdir(exist_ok=False)
    for name in ['run_expanded_probe.py','root-results/candidate_registry.json','root-results/report.txt','SIGNED_ARITHMETIC_CONTROL.md','verify_critical_defect_integration.py']:
        target=snapshot/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((BASE/name).read_bytes())
    print('26 scoped loaders verified; exact previous and current integration snapshots retained.')
    print('Common-factor signed components verified; the full RH inequality remains unproved.')


if __name__=='__main__':main()
