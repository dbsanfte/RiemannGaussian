#!/usr/bin/env python3
"""Verify the 24-stage integration and retain exact historical snapshots."""
import hashlib,importlib,json
from pathlib import Path
BASE=Path(__file__).resolve().parent
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    previous_path=BASE/'root-lattice-results/pilot-002/integration_verification.json';previous=read(previous_path);modules=[r['loader'] for r in previous['strict_loaders_checked']]+['divisor_preconditioner_report'];loaded={};records=[]
    for name in modules:
        s=importlib.import_module(name).load_latest();assert s['status']!='not_run' and not s.get('RH_proved',False);loaded[name]=s;checks=s.get('checks');flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({'loader':name,'status':s['status'],'verification_sha256':s.get('verification_sha256'),'checks_passed':sum(checks.values()) if flat else s.get('verified_checks'),'checks_total':len(checks) if flat else s.get('verified_checks')})
    assert len(records)==24;registry=read(BASE/'root-results/candidate_registry.json');s=loaded['divisor_preconditioner_report'];d=Path(s['run_directory']);spec=read(d/'protocol.json');audit=read(d/'verification.json')
    assert registry['divisor_preconditioning_with_retained_signed_arithmetic']==s and registry['normalized_root_arithmetic_and_signed_profile_learning']==loaded['root_lattice_report']
    assert registry['verified_arithmetic_consequence_count']==20 and registry['full_coefficient_origin_native_zeta_comparison_groups']==150
    assert (BASE/'operator_candidates.txt').read_text().splitlines()[0].startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES')
    assert registry['uniform_RH_sufficient_signed_controls_verified']==registry['uniform_sublinear_signed_controls_verified']==[] and not registry['historical_priority_is_acceptance_gate']
    assert s['actual_mobius_remainder_retained'] and not s['ordinary_zeta_erased'] and s['all_real_scales_integer_signed_bounds_proved'] and s['verified_ordinary_power']=='1' and s['verified_integer_log_loss']=='0' and not s['RH_strength']
    assert s['all_positive_rational_log_orders_supported'] and not s['semantic_denominator_cap'] and s['actual_prime_factor_support_information_for_every_integer']
    assert s['first_jet_zero_recovery_proved'] and s['higher_jet_zero_recovery_unproved'] and s['fractional_critical_centers_and_zero_recovery_unproved'] and s['known_Selberg_and_generalized_von_Mangoldt_is_calibration']
    assert not s['new_independent_prime_distribution_estimate'] and not s['machine_formalized'] and not audit['mathematical_audit_imports_production_code']
    assert Path(spec['source_run'])==Path(loaded['root_lattice_report']['run_directory']) and len(audit['checks'])==s['verified_checks'] and all(audit['checks'].values())
    milestones=[]
    paths=[Path(row['path']) for row in previous['prior_integration_milestones_and_snapshots']]+[previous_path]
    for p in paths:
        old=read(p);snapshot=p.parent/'integration_snapshot';checkers=list(snapshot.glob('verify_*_integration.py'));assert len(checkers)==1
        for key,name in [('driver_sha256','run_expanded_probe.py'),('registry_sha256','root-results/candidate_registry.json'),('report_sha256','root-results/report.txt'),('documentation_sha256','SIGNED_ARITHMETIC_CONTROL.md')]:assert sha(snapshot/name)==old[key]
        assert sha(checkers[0])==old['integration_checker_sha256'];milestones.append({'path':str(p),'sha256':sha(p),'exact_five_file_snapshot_preserved':True})
    for n,value in spec['code_sha256'].items():assert sha(BASE/n)==value
    plots=read(d/'plot_observations.json')
    for key,n in [('source_protocol_sha256','protocol.json'),('source_archive_sha256','archive.json'),('source_final_sha256','final_evaluation.json'),('source_verification_sha256','verification.json')]:assert plots[key]==sha(d/n)
    assert plots['complete_actual_point_sums_used'] and plots['signed_remainder_retains_actual_arithmetic'] and plots['ordinary_power_is_one'] and plots['fractional_signs_are_generic_universal_geometry'] and not plots['RH_proved']
    assert 'DIVISOR PRECONDITIONING WITH RETAINED SIGNED ARITHMETIC' in (BASE/'root-results/report.txt').read_text() and 'Divisor preconditioning with the signed remainder retained' in (BASE/'SIGNED_ARITHMETIC_CONTROL.md').read_text()
    result={'status':'integration_verified_research_goal_still_active','objective':registry['objective'],
        'driver_sha256':sha(BASE/'run_expanded_probe.py'),'registry_sha256':sha(BASE/'root-results/candidate_registry.json'),'report_sha256':sha(BASE/'root-results/report.txt'),'documentation_sha256':sha(BASE/'SIGNED_ARITHMETIC_CONTROL.md'),'integration_checker_sha256':sha(BASE/'verify_divisor_preconditioner_integration.py'),
        'strict_loaders_checked':records,'legacy_catalogue_scoped_counts':{'families':10,'consequences':20,'native_groups':150},'legacy_catalogue_sha256':sha(BASE/'operator_candidates.txt'),'prior_integration_milestones_and_snapshots':milestones,
        'divisor_preconditioner_scope':{k:s[k] for k in ['logarithmic_orders','integer_global_signed_certificates','anonymous_learned_preconditioner_proposals','completed_new_candidate_promotions','learned_universal_bell_relations','all_index_fractional_and_integer_sign_certificates','anonymous_universal_sign_signatures','ablation_comparison','completed_log_loss_improvements']},
        'native_check_counts':audit['counts'],'this_stage_frozen_source_sha256':{n:sha(BASE/n) for n in spec['this_stage_source_files']},'public_contract_checks':{'cases':13,'source_sha256':sha(BASE/'test_divisor_preconditioner_contracts.py')},
        'standalone_evidence_plot':{'source_sha256':sha(BASE/'plot_divisor_preconditioners.py'),'png_sha256':sha(d/'divisor_preconditioner_evidence.png'),'pdf_sha256':sha(d/'divisor_preconditioner_evidence.pdf'),'observations_sha256':sha(d/'plot_observations.json')},
        'scoped_report_sha256':sha(d/'report.txt'),'named_calibration_dependencies':spec['named_calibration_dependencies'],'source_producer_reruns_for_integration':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False,
        'completion_audit':'Not achieved: actual prime-coupled signed errors are certified globally with the Mobius remainder retained, but their ordinary power is one; the recovering critical first-jet signed estimate and fractional centers/recovery remain unproved.'}
    destination=d/'integration_verification.json'
    if destination.exists():raise FileExistsError('Retain the integration milestone')
    destination.write_text(json.dumps(result,indent=2)+'\n');snapshot=d/'integration_snapshot';snapshot.mkdir(exist_ok=False)
    for name in ['run_expanded_probe.py','root-results/candidate_registry.json','root-results/report.txt','SIGNED_ARITHMETIC_CONTROL.md','verify_divisor_preconditioner_integration.py']:
        target=snapshot/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((BASE/name).read_bytes())
    print('24 scoped loaders verified; exact prior and current integration snapshots retained.')
    print('Every-scale signed arithmetic bounds retain the remainder. RH-strength controls remain open.')


if __name__=='__main__':main()
