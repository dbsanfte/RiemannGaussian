#!/usr/bin/env python3
"""Verify 25 scoped stages and preserve the exact earlier integration states."""
import hashlib,importlib,json
from pathlib import Path
BASE=Path(__file__).resolve().parent
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    previous_path=BASE/'divisor-preconditioner-results/pilot-001/integration_verification.json';previous=read(previous_path);modules=[r['loader'] for r in previous['strict_loaders_checked']]+['branch_center_report'];loaded={};records=[]
    for name in modules:
        s=importlib.import_module(name).load_latest();assert s['status']!='not_run' and not s.get('RH_proved',False);loaded[name]=s;checks=s.get('checks');flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({'loader':name,'status':s['status'],'verification_sha256':s.get('verification_sha256'),'checks_passed':sum(checks.values()) if flat else s.get('verified_checks'),'checks_total':len(checks) if flat else s.get('verified_checks')})
    assert len(records)==25;registry=read(BASE/'root-results/candidate_registry.json');s=loaded['branch_center_report'];d=Path(s['run_directory']);spec=read(d/'protocol.json');audit=read(d/'verification.json')
    assert registry['complete_fractional_centers_and_signed_cofinal_parameter_families']==s and registry['divisor_preconditioning_with_retained_signed_arithmetic']==loaded['divisor_preconditioner_report']
    assert registry['verified_arithmetic_consequence_count']==20 and registry['full_coefficient_origin_native_zeta_comparison_groups']==150
    assert (BASE/'operator_candidates.txt').read_text().splitlines()[0].startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES')
    assert registry['uniform_RH_sufficient_signed_controls_verified']==registry['uniform_sublinear_signed_controls_verified']==[] and not registry['historical_priority_is_acceptance_gate']
    assert s['actual_mobius_arithmetic_retained'] and not s['ordinary_zeta_erased'] and s['all_real_scale_weak_bounds_proved'] and s['verified_ordinary_power']=='1' and s['verified_log_loss']=='1' and not s['RH_strength']
    assert s['all_rational_roots_in_open_unit_interval_supported'] and not s['semantic_denominator_cap'] and s['complete_fractional_branch_center_proved'] and s['entire_exponent_parameter_recovery_proved'] and s['all_ordinary_heights_and_multiplicities_covered']
    assert s['normalization_full_center_and_interpolation_costs_charged'] and not s['new_independent_prime_distribution_estimate'] and not s['machine_formalized'] and not audit['mathematical_audit_imports_production_code']
    assert Path(spec['source_run'])==Path(loaded['divisor_preconditioner_report']['run_directory']) and len(audit['checks'])==s['verified_checks'] and all(audit['checks'].values())
    milestones=[];paths=[Path(row['path']) for row in previous['prior_integration_milestones_and_snapshots']]+[previous_path]
    for p in paths:
        old=read(p);snapshot=p.parent/'integration_snapshot';checkers=list(snapshot.glob('verify_*_integration.py'));assert len(checkers)==1
        for key,name in [('driver_sha256','run_expanded_probe.py'),('registry_sha256','root-results/candidate_registry.json'),('report_sha256','root-results/report.txt'),('documentation_sha256','SIGNED_ARITHMETIC_CONTROL.md')]:assert sha(snapshot/name)==old[key]
        assert sha(checkers[0])==old['integration_checker_sha256'];milestones.append({'path':str(p),'sha256':sha(p),'exact_five_file_snapshot_preserved':True})
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h
    plots=read(d/'plot_observations.json')
    for key,n in [('source_protocol_sha256','protocol.json'),('source_archive_sha256','archive.json'),('source_final_sha256','final_evaluation.json'),('source_verification_sha256','verification.json')]:assert plots[key]==sha(d/n)
    assert plots['signed_actual_arithmetic_used'] and plots['full_real_cut_centers_used'] and plots['normalizations_charged'] and plots['ordinary_power_is_one'] and plots['conditional_costs_are_finite_only'] and not plots['RH_proved']
    positive=read(d/'positive_gap_observer_audit.json');assert positive['all_passed'] and positive['no_candidate_or_selection_changes'] and positive['no_new_case_or_fit_constant'] and not positive['mathematical_audit_imports_production_code']
    assert sha(BASE/'branch_center_positive_gap_audit.py')==positive['auditor_sha256']
    for n,h in positive['source_sha256'].items():assert sha(d/n)==h
    from rational_fractional_contract_report import load_latest as load_contracts
    contracts=load_contracts();assert contracts['status']!='not_run' and registry['unbounded_rational_fractional_evaluation_contracts']==contracts
    assert contracts['native_unsigned_root_denominator_limit_removed'] and contracts['exact_outward_integer_guard_verified'] and contracts['normalized_tiny_parameter_high_pass_verified'] and contracts['no_search_or_selection_changes']
    assert 'COMPLETE FRACTIONAL CENTERS AND COFINAL SIGNED PARAMETER FAMILIES' in (BASE/'root-results/report.txt').read_text() and 'Complete fractional centers and cofinal signed parameter families' in (BASE/'SIGNED_ARITHMETIC_CONTROL.md').read_text()
    result={'status':'integration_verified_research_goal_still_active','objective':registry['objective'],
        'driver_sha256':sha(BASE/'run_expanded_probe.py'),'registry_sha256':sha(BASE/'root-results/candidate_registry.json'),'report_sha256':sha(BASE/'root-results/report.txt'),'documentation_sha256':sha(BASE/'SIGNED_ARITHMETIC_CONTROL.md'),'integration_checker_sha256':sha(BASE/'verify_branch_center_integration.py'),
        'strict_loaders_checked':records,'legacy_catalogue_scoped_counts':{'families':10,'consequences':20,'native_groups':150},'legacy_catalogue_sha256':sha(BASE/'operator_candidates.txt'),'prior_integration_milestones_and_snapshots':milestones,
        'branch_center_scope':{k:s[k] for k in ['base_roots','program_count','anonymous_learned_combinations','parameter_moment_promotions','nonzero_cofinal_recovery_certificates','zero_sum_weight_recovering_families','maximum_first_nonzero_moment_order','growth_hypotheses','archived_estimates','fresh_RH_if_uniform_finite_passes','ablation_comparison','leading_only_branch_obstructions']},
        'native_check_counts':audit['counts'],'this_stage_frozen_source_sha256':{n:sha(BASE/n) for n in spec['this_stage_source_files']},'public_contract_checks':{'cases':16,'source_sha256':sha(BASE/'test_branch_center_contracts.py')},
        'positive_gap_post_run_audit':{'auditor_sha256':positive['auditor_sha256'],'artifact_sha256':sha(d/'positive_gap_observer_audit.json'),'native_counts':positive['native_counts']},
        'arbitrary_denominator_contract_audit':contracts,'arbitrary_denominator_contract_loader_sha256':sha(BASE/'rational_fractional_contract_report.py'),
        'standalone_evidence_plot':{'source_sha256':sha(BASE/'plot_branch_centers.py'),'png_sha256':sha(d/'branch_center_evidence.png'),'pdf_sha256':sha(d/'branch_center_evidence.pdf'),'observations_sha256':sha(d/'plot_observations.json')},
        'scoped_report_sha256':sha(d/'report.txt'),'source_producer_reruns_for_integration':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False,
        'completion_audit':'Not achieved: complete fractional centers and cofinal ordinary-zero recovery are verified, including signed high-pass parameter families, but the proved actual signed global power is one; critical signed premises remain unproved.'}
    destination=d/'integration_verification.json'
    if destination.exists():raise FileExistsError('Retain the integration milestone')
    destination.write_text(json.dumps(result,indent=2)+'\n');snapshot=d/'integration_snapshot';snapshot.mkdir(exist_ok=False)
    for name in ['run_expanded_probe.py','root-results/candidate_registry.json','root-results/report.txt','SIGNED_ARITHMETIC_CONTROL.md','verify_branch_center_integration.py']:
        target=snapshot/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((BASE/name).read_bytes())
    print('25 scoped loaders verified; exact previous and current integration snapshots retained.')
    print('Complete centers and ordinary-zero recovery verified; RH-strength signed estimates remain open.')


if __name__=='__main__':main()
