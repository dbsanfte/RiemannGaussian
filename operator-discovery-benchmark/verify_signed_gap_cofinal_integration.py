#!/usr/bin/env python3
"""Verify actual cofinal refutations without rewriting earlier numerical results."""
import hashlib,importlib,json
from pathlib import Path
BASE=Path(__file__).resolve().parent
def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def main():
    previous_path=BASE/'signed-gap-profile-results/pilot-001/integration_verification.json';previous=read(previous_path);loaded={};records=[]
    for old in previous['strict_loaders_checked']:
        name=old['loader'];s=importlib.import_module(name).load_latest();assert s['status']!='not_run' and not s.get('RH_proved',False);loaded[name]=s;checks=s.get('checks');flat=bool(checks) and all(type(v)is bool for v in checks.values())
        if flat:assert all(checks.values())
        records.append({'loader':name,'status':s['status'],'verification_sha256':s.get('verification_sha256'),'checks_passed':sum(checks.values()) if flat else s.get('verified_checks'),'checks_total':len(checks) if flat else s.get('verified_checks')})
    assert len(records)==28
    from divisor_dual_analytic_report import load_latest as prior_analytical
    from signed_gap_cofinal_report import load_latest as cofinal
    olda=prior_analytical();s=cofinal();d=Path(s['audit_directory']);source=Path(s['source_run']);spec=read(d/'protocol.json');a=read(d/'audit.json');v=read(d/'verification.json');registry=read(BASE/'root-results/candidate_registry.json')
    assert registry['cofinal_actual_arithmetic_counterexamples_to_fitted_gap_candidates']==s and registry['independent_constant_profiles_and_actual_signed_nullspace_gap']==loaded['signed_gap_profile_report'] and registry['separate_analytical_review_of_detector_candidates']==olda
    assert source==Path(loaded['signed_gap_profile_report']['run_directory']) and s['candidate_count']==loaded['signed_gap_profile_report']['proof_queue_candidates'] and s['disproved_uniform_actual_half_gap_candidates']+s['unresolved_actual_half_gap_candidates']==s['candidate_count']
    assert s['disproved_uniform_actual_half_gap_candidates']==sum(r['persistent_half_gap_witness'] is not None for r in a['attempts']) and s['disproved_complete_dual_PSD_candidates']==sum(r['persistent_nullspace_witness'] is not None for r in a['attempts']) and s['disproved_fully_charged_global_defect_candidates']==sum(r['persistent_fully_charged_witness'] is not None for r in a['attempts'])
    assert s['original_formulas_fits_and_finite_passes_unchanged'] and s['actual_prime_inverse_counterexamples'] and s['parameter_start_cannot_remove_witnesses'] and s['unbounded_and_existential_families_remain_unresolved'] and s['not_RH_counterexamples'] and not s['global_actual_critical_signed_gap_proved'] and not s['machine_formalized']
    assert v['all_passed'] and all(v['checks'].values()) and len(v['checks'])==s['verified_checks'] and not v['mathematical_audit_imports_production_code']
    for n,h in spec['source_sha256'].items():assert sha(source/n)==h
    for n,h in spec['code_sha256'].items():assert sha(BASE/n)==h==sha(d/'frozen_source'/n)
    assert registry['verified_arithmetic_consequence_count']==20 and registry['full_coefficient_origin_native_zeta_comparison_groups']==150 and (BASE/'operator_candidates.txt').read_text().splitlines()[0].startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES')
    assert registry['uniform_RH_sufficient_signed_controls_verified']==registry['uniform_sublinear_signed_controls_verified']==[] and not registry['historical_priority_is_acceptance_gate']
    milestones=[];paths=[Path(r['path']) for r in previous['prior_integration_milestones_and_snapshots']]+[previous_path]
    for p in paths:
        old=read(p);snapshot=p.parent/'integration_snapshot';checkers=list(snapshot.glob('verify_*_integration.py'));assert len(checkers)==1
        for key,name in [('driver_sha256','run_expanded_probe.py'),('registry_sha256','root-results/candidate_registry.json'),('report_sha256','root-results/report.txt'),('documentation_sha256','SIGNED_ARITHMETIC_CONTROL.md')]:assert sha(snapshot/name)==old[key]
        assert sha(checkers[0])==old['integration_checker_sha256'];milestones.append({'path':str(p),'sha256':sha(p),'exact_five_file_snapshot_preserved':True})
    assert 'COFINAL ACTUAL-ARITHMETIC COUNTEREXAMPLES TO FITTED GAP CANDIDATES' in (BASE/'root-results/report.txt').read_text() and 'Cofinal endpoint tests can refute an actual fitted arithmetic bound' in (BASE/'SIGNED_ARITHMETIC_CONTROL.md').read_text()
    assert '--signed-gap-cofinal-only' in (BASE/'run_expanded_probe.py').read_text() and 'signed_gap_cofinal_audit.py' in (BASE/'run_expanded_probe.py').read_text()
    result={'status':'integration_verified_research_goal_still_active','objective':registry['objective'],'driver_sha256':sha(BASE/'run_expanded_probe.py'),'registry_sha256':sha(BASE/'root-results/candidate_registry.json'),'report_sha256':sha(BASE/'root-results/report.txt'),'documentation_sha256':sha(BASE/'SIGNED_ARITHMETIC_CONTROL.md'),'integration_checker_sha256':sha(BASE/'verify_signed_gap_cofinal_integration.py'),
        'strict_loaders_checked':records,'preserved_prior_analytical_extension':{'loader':'divisor_dual_analytic_report','status':olda['status'],'verification_sha256':olda['verification_sha256']},
        'separate_cofinal_extension':{'loader':'signed_gap_cofinal_report','status':s['status'],'verification_sha256':s['verification_sha256'],'checks_passed':len(v['checks']),'checks_total':len(v['checks'])},
        'legacy_catalogue_scoped_counts':{'families':10,'consequences':20,'native_groups':150},'legacy_catalogue_sha256':sha(BASE/'operator_candidates.txt'),'prior_integration_milestones_and_snapshots':milestones,
        'cofinal_actual_arithmetic_dispositions':{k:s[k] for k in ['candidate_count','disproved_uniform_actual_half_gap_candidates','disproved_complete_dual_PSD_candidates','disproved_fully_charged_global_defect_candidates','unresolved_actual_half_gap_candidates','refuted_candidate_ids']},
        'independent_actual_arithmetic_counts':v['counts'],'this_extension_frozen_source_sha256':spec['code_sha256'],'public_contract_checks':{'cases':6,'source_sha256':sha(BASE/'test_signed_gap_cofinal_contracts.py')},'scoped_report_sha256':sha(d/'report.txt'),
        'original_finite_outcomes_and_formulas_unchanged':True,'original_producer_reruns_for_integration':False,'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False,
        'completion_audit':'Not achieved: exact actual arithmetic refutes three frozen cofinal half-gap claims and three dual-PSD claims, including two fully charged bounds. Forty-five source half-gap claims remain unresolved; no all-scale critical signed control has been proved.'}
    destination=d/'integration_verification.json'
    if destination.exists():raise FileExistsError('Retain the integration milestone')
    destination.write_text(json.dumps(result,indent=2)+'\n');snapshot=d/'integration_snapshot';snapshot.mkdir(exist_ok=False)
    for n in ['run_expanded_probe.py','root-results/candidate_registry.json','root-results/report.txt','SIGNED_ARITHMETIC_CONTROL.md','verify_signed_gap_cofinal_integration.py']:
        target=snapshot/n;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((BASE/n).read_bytes())
    print('28 scoped stages, prior analytical review and cofinal extension verified; exact snapshots retained.')
    print('Three actual cofinal half-gap claims refuted; 45 unresolved. RH-strength global signed control remains unproved.')


if __name__=='__main__':main()
