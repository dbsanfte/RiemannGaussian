#!/usr/bin/env python3
"""Preserve exact past milestones while integrating new scoped arithmetic work."""
import importlib
import json
import hashlib
from pathlib import Path
from detector_workflow_guard import require_verified_runtime

BASE=Path(__file__).resolve().parent

def read(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def require(value,message):
    if not value:raise ValueError(message)


def main():
    require_verified_runtime()
    previous_path=BASE/'workflow-audit-results/audit-001/integration_verification.json'
    previous=read(previous_path);records=[]
    for old in previous['strict_loaders_checked']:
        s=importlib.import_module(old['loader']).load_latest()
        require(s['status']!='not_run' and not s.get('RH_proved',False),'prior stage missing or overclaims')
        records.append({**old,'status':s['status'],'verification_sha256':s.get('verification_sha256')})
    require(len(records)==30,'unexpected prior stage coverage')
    extensions=[]
    for item in previous['preserved_extensions']:
        s=importlib.import_module(item['loader']).load_latest()
        require(s['verification_sha256']==item['verification_sha256'],'prior analytical extension changed')
        extensions.append(item)
    from signed_arithmetic_review_report import load_latest as load_review
    review=load_review()
    require(review['status']!='not_run' and not review['RH_proved'],'new analytical review missing or overclaimed')
    extensions.append({'loader':'signed_arithmetic_review_report','status':review['status'],'verification_sha256':review['verification_sha256']})
    from signed_arithmetic_report import load_latest
    s=load_latest();d=Path(s['run_directory']);v=read(d/'verification.json');p=read(d/'protocol.json')
    registry=read(BASE/'root-results/candidate_registry.json')
    require(registry['typed_signed_arithmetic_and_complete_scale_stencils']==s,'new registry scope mismatch')
    require(registry['parallel_signed_arithmetic_reviews_and_dense_residual_reduction']==review,'review scope mismatch')
    require(review['reviewed_candidates']==s['proof_queue_candidates'],'review coverage mismatch')
    require(v['all_passed'],'new checks incomplete')
    require(not s['actual_all_scale_signed_bound_proved'] and not s['RH_proved'],'full control not proved')
    require(registry['uniform_RH_sufficient_signed_controls_verified']==[] and registry['uniform_sublinear_signed_controls_verified']==[],'unverified global control promoted')
    require(registry['verified_arithmetic_consequence_count']==20 and registry['full_coefficient_origin_native_zeta_comparison_groups']==150,'legacy counts changed')
    require((BASE/'operator_candidates.txt').read_text().startswith('TEN MATHEMATICALLY VERIFIED CANDIDATE FAMILIES'),'legacy catalogue changed')
    require('TYPED SIGNED ARITHMETIC AND COMPLETE SCALE STENCILS' in (BASE/'root-results/report.txt').read_text(),'root report missing new scope')
    require('Typed signed arithmetic preserves coupled cancellation' in (BASE/'SIGNED_ARITHMETIC_CONTROL.md').read_text(),'documentation missing')
    milestones=[]
    for path in [Path(r['path']) for r in previous['prior_integration_milestones_and_snapshots']]+[previous_path]:
        old=read(path);snap=path.parent/'integration_snapshot';checkers=list(snap.glob('verify_*_integration.py'))
        require(len(checkers)==1,'historical checker absent')
        for key,name in [('driver_sha256','run_expanded_probe.py'),('registry_sha256','root-results/candidate_registry.json'),('report_sha256','root-results/report.txt'),('documentation_sha256','SIGNED_ARITHMETIC_CONTROL.md')]:
            require(sha(snap/name)==old[key],'historical snapshot changed')
        require(sha(checkers[0])==old['integration_checker_sha256'],'historical checker changed')
        milestones.append({'path':str(path),'sha256':sha(path),'exact_five_file_snapshot_preserved':True})
    records.append({'loader':'signed_arithmetic_report','status':s['status'],'verification_sha256':s['verification_sha256'],'checks_passed':v['checks_passed'],'checks_total':v['checks_passed']})
    result={'status':'integration_verified_research_goal_still_active','objective':registry['objective'],
            'driver_sha256':sha(BASE/'run_expanded_probe.py'),'registry_sha256':sha(BASE/'root-results/candidate_registry.json'),
            'report_sha256':sha(BASE/'root-results/report.txt'),'documentation_sha256':sha(BASE/'SIGNED_ARITHMETIC_CONTROL.md'),
            'integration_checker_sha256':sha(BASE/'verify_signed_arithmetic_integration.py'),
            'strict_loaders_checked':records,'preserved_extensions':extensions,
            'legacy_catalogue_scoped_counts':{'families':10,'consequences':20,'native_groups':150},
            'legacy_catalogue_sha256':sha(BASE/'operator_candidates.txt'),
            'prior_integration_milestones_and_snapshots':milestones,'this_extension_frozen_source_sha256':p['code_sha256'],
            'scoped_report_sha256':sha(d/'report.txt'),'original_producer_reruns_for_integration':False,
            'original_finite_outcomes_and_formulas_unchanged':True,'machine_formalized':False,
            'uniform_RH_sufficient_signed_controls_verified':[],'RH_proved':False,
            'completion_audit':'Not achieved: exact actual component cancellation and frozen full-signed candidates are verified. No complete all-scale signed residual estimate establishes RH.'}
    destination=d/'integration_verification.json';require(not destination.exists(),'successful milestone immutable')
    snap=d/'integration_snapshot';snap.mkdir(exist_ok=False)
    for name in ['run_expanded_probe.py','root-results/candidate_registry.json','root-results/report.txt','SIGNED_ARITHMETIC_CONTROL.md','verify_signed_arithmetic_integration.py']:
        target=snap/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes((BASE/name).read_bytes())
    destination.write_text(json.dumps(result,indent=2)+'\n')
    print('31 scoped stages and five analytical extensions integrated; 16 historical five-file snapshots preserved.')
    print('Full actual signed RH inequality remains unproved.')

if __name__=='__main__':main()
