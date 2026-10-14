"""Publication005 admission and integrity loader; publication is explicit only."""
import argparse
import ast
import hashlib
import json
import re
import subprocess
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT=Path(__file__).resolve().parent
BASE=ROOT/'cancellation-arithmetic-results'
FLAGS=dict(global_bound_proved=False,RH_proved=False)


def read(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(p,value):
 with p.open('x')as f:json.dump(value,f,sort_keys=True,indent=2,allow_nan=False);f.write('\n')
def require(condition,message):
 if not condition:raise ValueError(message)
def manifest(p,root,expected=None):
 m=read(p)
 if expected is not None:require(len(m['files'])==expected,'prior manifest count')
 for n,h in m['files'].items():require(sha(root/n)==h,'manifest binding '+n)
 return m

def source_closure(names):
 pending=list(names);seen=set()
 while pending:
  name=pending.pop();p=ROOT/(name+'.py')
  if name in seen or not p.is_file():continue
  seen.add(name)
  for node in ast.walk(ast.parse(p.read_text())):
   if isinstance(node,ast.Import):pending.extend(a.name.split('.')[0]for a in node.names)
   elif isinstance(node,ast.ImportFrom)and node.module:pending.append(node.module.split('.')[0])
 return sorted(n+'.py'for n in seen)


def bindings(d):
 review=read(d/'independent_verification.json');require(review.get('all_passed')is True,'independent admission '+d.name)
 for n,h in review['input_sha256'].items():require(sha(d/n)==h,'independent input '+d.name+'/'+n)
 sources=read(d/'source_seal.json')
 for n,h in sources.items():require(sha(ROOT/n)==h and sha(d/'frozen_source'/n)==h,'sealed source '+n)
 if (d/'input.json').is_file():
  for n,h in read(d/'input.json')['input_sha256'].items():require(sha(ROOT/n)==h,'prior input '+n)
 if (d/'receipt.json').is_file():
  receipt=read(d/'receipt.json')
  for n,h in receipt['files_sha256'].items():require(sha(d/n)==h,'terminal artifact '+d.name+'/'+n)
  require(receipt['source_count']==len(sources),'terminal source count')
 return review


def load_inputs():
 old=BASE/'publication-004';resource=ROOT/'detector-performance-results/publication-001'
 manifest(old/'manifest.json',ROOT,343);manifest(resource/'manifest.json',ROOT,244)
 stage=BASE/'cell-shared-gram-probe-001';native=BASE/'cell-shared-gram-native-replay-001';joint=BASE/'cell-joint-gram-probe-001'
 stage_review=bindings(stage);native_review=bindings(native);joint_review=bindings(joint)
 import check_cell_gram_search as C
 import run_shared_gram_native_replay as N
 import cancellation_cell_joint_gram_probe as J
 protocol=read(stage/'protocol.json');source=read(stage/'source_seal.json')
 require(set(source)==set(C.source_names()),'whole stage source closure')
 require(read(stage/'seal.json')==dict(protocol_sha256=sha(stage/'protocol.json'),source_seal_sha256=sha(stage/'source_seal.json'),input_sha256=sha(stage/'input.json')),'stage seal')
 require(protocol['programs']==C.PROGRAMS and protocol['limits']==C.LIMITS and protocol['solver_limits']==C.SOLVER_LIMITS and protocol['dual_limits']==C.DUAL_LIMITS and protocol['gram_specs']==C.B.gram_specs() and protocol['gram_groups']==C.B.group_descriptors(),'known exact stage cone')
 require(stage_review['training_statuses']==['uncertified','missing_resource'] and stage_review['followup_statuses']==['missing_resource'] and stage_review['transfer_certificates_verified']==0 and stage_review['frozen_weights_and_Gram_transfer_verified']is False,'retained stage outcomes')
 tests=read(stage/'tests.json');require(tests['returncode']==0 and re.search(r'Ran 34 tests in .*\n\s*OK\s*$',tests['stdout']+tests['stderr']),'34 frozen stage calibrations')
 N.validate(native)
 result=read(native/'result.json');dual=result['synthesis'];saved=read(native/'support.json')['indices'];original=read(stage/'jobs/dual-000.json')
 require(result['status']=='exact_separator' and dual['certified']is True and dual['independent_check']['verified']is True and native_review['status']=='exact_separator' and native_review['full_20group_independent_check']['verified']is True,'independently admitted full20 separator')
 require(saved==original['synthesis']['proposal_diagnostics']['support']==dual['saved_support'] and len(saved)==584,'same saved support')
 require(result['case_hashes']==original['case_hashes'] and result['gram_block_hashes']==original['gram_block_hashes'] and result['gram_archive_hashes']==original['gram_archive_hashes'] and len(dual['gram_duals'])==20,'same declared complete cone')
 require(dual['constant_coordinates']==['0']*5 and dual['lhs_dot_y']=='-1','zero constant scalar-budget scope')
 policy=read(native/'computational_policy_review.json')
 require(policy['result_sha256']==sha(native/'result.json') and policy['protocol_sha256']==sha(native/'protocol.json') and policy['support_sha256']==sha(native/'support.json') and policy['terminal_receipt_sha256']==sha(native/'receipt.json'),'policy evidence bindings')
 require(policy['rref_work_proxy']==1262*584**2==430412672 and policy['equation_build_work_proxy']==1262*8113 and policy['archived_replay_work_ceiling']==2000000000 and policy['future_policy_work_ceiling']==450000000 and policy['future_450m_passes_same_deterministic_work_preflight']is True,'historical versus future work policy')
 js=read(joint/'source_seal.json');jp=read(joint/'protocol.json');jr=read(joint/'results.json');directions=read(joint/'simple_directions.json')
 require(set(js)==set(J.source_names()) and read(joint/'seal.json')==dict(protocol_sha256=sha(joint/'protocol.json'),source_seal_sha256=sha(joint/'source_seal.json')),'joint sealed closure')
 require(jp['spec']==J.SPEC and jp['parent_protocol_sha256']==sha(stage/'protocol.json'),'joint preregistered complete program')
 for n,h in jr['input_sha256'].items():require(sha(ROOT/n)==h,'joint original witness input')
 require(directions['source_results_sha256']==sha(joint/'results.json') and joint_review['missing_coordinates']==0 and joint_review['negative_quadratic_directions_verified']is True,'joint independent complete diagnostic')
 require(set(jr['regions'])=={'parent','child'} and set(directions['directions'])=={'parent','child'},'both joint regions')
 for name,row in jr['regions'].items():
  require(row['status']=='witness_invalid_for_joint_cone' and len(row['matrix'])==10 and all(len(r)==10 for r in row['matrix']) and F(row['quadratic_value'])<0,'complete joint negative direction')
  require(F(directions['directions'][name]['quadratic_value'])<0,'simple direction negative')
 require(jr['larger_cone_feasibility_proved']is False,'no enlarged feasibility promotion')
 root_review=read(joint/'root_direction_verification.json')
 require(root_review.get('all_passed')is True and root_review['original_dual_sha256']==sha(native/'result.json') and root_review['verifier_sha256']==sha(ROOT/'check_cell_joint_gram_directions.py'),'root direct-source direction admission')
 for n,h in root_review['input_sha256'].items():require(sha(joint/n)==h,'root direction input '+n)
 from check_cell_joint_gram_directions import verify
 require(verify(joint)==root_review,'root complete direct-source direction replay')
 test=subprocess.run([sys.executable,'-B','-m','unittest','test_cancellation_shared_gram_replay'],cwd=ROOT,capture_output=True,text=True,timeout=30)
 require(test.returncode==0 and re.search(r'Ran 4 tests in .*\n\s*OK\s*$',test.stdout+test.stderr),'four future-policy toy calibrations')
 return dict(old=old,resource=resource,stage=stage,native=native,joint=joint,stage_review=stage_review,native_review=native_review,joint_review=joint_review,policy=policy,policy_tests=dict(returncode=test.returncode,stdout=test.stdout,stderr=test.stderr))


def publish():
 inputs=load_inputs();out=BASE/'publication-005';require(not out.exists(),'exclusive publication005')
 notes=['publish_cancellation_shared_gram.py','SHARED_GRAM_SEARCH_HANDOFF.txt','cancellation_shared_gram_resource_review.txt','check_cell_joint_gram_directions.py']
 files={ROOT/n for n in notes}
 for k in ['stage','native','joint']:
  d=inputs[k];files.update(p for p in d.rglob('*')if p.is_file()and '__pycache__'not in p.parts)
  files.update(ROOT/n for n in read(d/'source_seal.json'))
 files.update(ROOT/n for n in source_closure(['cancellation_shared_gram_replay','test_cancellation_shared_gram_replay']))
 for k in ['old','resource']:files.update([inputs[k]/'manifest.json',inputs[k]/'report.json'])
 hashes={str(p.relative_to(ROOT)):sha(p)for p in sorted(files)}
 report=dict(schema=5,prior_research_publication='publication-004',previous_research_manifest_sha256=sha(inputs['old']/'manifest.json'),previous_research_bound_files=343,previous_resource_manifest_sha256=sha(inputs['resource']/'manifest.json'),previous_resource_bound_files=244,
  failed_stage=dict(independent_receipt_sha256=sha(inputs['stage']/'independent_verification.json'),tests_passed=34,training_statuses=inputs['stage_review']['training_statuses'],followup_statuses=inputs['stage_review']['followup_statuses'],transfer_certificates_verified=0,all_original_failures_preserved=True),
  exact_recovery=dict(independent_receipt_sha256=sha(inputs['native']/'independent_verification.json'),result_sha256=sha(inputs['native']/'result.json'),same_saved_support_count=584,new_floating_search=False,full_Gram_groups=20,constant_coordinates=['0']*5,scope='arbitrary scalar C_q budgets by constant-coordinate shifts within the exact fixed20group shared gamma-zero cone; no actual arithmetic bound refutation'),
  resource_policy=dict(archived_replay_max_work=2000000000,future_default_max_work=450000000,required_rref_work_proxy=430412672,equation_build_work_proxy=10238606,future_policy_tests_passed=4,real_450m_arithmetic_rerun_performed=False,review_sha256=sha(inputs['native']/'computational_policy_review.json')),
  joint_diagnostic=dict(independent_receipt_sha256=sha(inputs['joint']/'independent_verification.json'),root_direction_receipt_sha256=sha(inputs['joint']/'root_direction_verification.json'),root_direction_verifier_sha256=sha(ROOT/'check_cell_joint_gram_directions.py'),regions=2,atoms_per_region=10,missing_coordinates=0,both_region_matrices_non_PSD=True,original_witness_separates_joint_cone=False,larger_cone_feasibility_proved=False),
  scope='finite shared identities and independently verified separators and post-search diagnostics; gamma-zero gate necessary for fixed all-scale critical templates at q>1 only under the existing scalar-asymptotic assumptions',
  next_action='preregister full10atom joint divisor Grams mixing original prefix with all9complete divisor channels, retain legacy5atom Grams and charge every scalar budget, then conduct a new exact independently audited search',**FLAGS)
 out.mkdir();(out/'frozen_source').mkdir()
 for n in ['publish_cancellation_shared_gram.py','cancellation_shared_gram_replay.py','test_cancellation_shared_gram_replay.py','check_cell_joint_gram_directions.py']:
  p=out/'frozen_source'/n;p.write_bytes((ROOT/n).read_bytes());hashes[str(p.relative_to(ROOT))]=sha(p)
 p=out/'SHARED_GRAM_SEARCH_HANDOFF.txt';p.write_bytes((ROOT/p.name).read_bytes());hashes[str(p.relative_to(ROOT))]=sha(p)
 write(out/'future_policy_tests.json',inputs['policy_tests']);hashes[str((out/'future_policy_tests.json').relative_to(ROOT))]=sha(out/'future_policy_tests.json')
 write(out/'report.json',report);hashes[str((out/'report.json').relative_to(ROOT))]=sha(out/'report.json')
 write(out/'manifest.json',dict(schema=1,files=hashes,**FLAGS));manifest(out/'manifest.json',ROOT)
 load_inputs();manifest(out/'manifest.json',ROOT)
 pointer=dict(publication='publication-005',report_sha256=sha(out/'report.json'),manifest_sha256=sha(out/'manifest.json'),**FLAGS)
 write(BASE/'latest-005.tmp',pointer);(BASE/'latest-005.tmp').replace(BASE/'latest.json')
 return dict(publication='publication-005',bound_files=len(hashes),**FLAGS)


if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('action',choices=['validate','publish']);args=parser.parse_args()
 if args.action=='publish':print(json.dumps(publish()))
 else:
  load_inputs();print(json.dumps(dict(all_passed=True,publication_written=False,**FLAGS)))
