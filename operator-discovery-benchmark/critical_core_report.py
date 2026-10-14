#!/usr/bin/env python3
"""Posthoc exact reporting; imports no arithmetic producer or search implementation."""
import argparse,hashlib,json
from fractions import Fraction as F
from pathlib import Path

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def rank(a):
 a=[list(map(F,r)) for r in a];row=0
 for col in range(len(a[0]) if a else 0):
  pivot=next((i for i in range(row,len(a)) if a[i][col]),None)
  if pivot is None:continue
  a[row],a[pivot]=a[pivot],a[row];v=a[row][col];a[row]=[x/v for x in a[row]]
  for i in range(row+1,len(a)):
   v=a[i][col]
   if v:a[i]=[x-v*y for x,y in zip(a[i],a[row])]
  row+=1
 return row

def matrix(row):
 d=row['correction_denominators'];base=row['gram_base_denominator']
 return [[F(v,base*d[i]*d[j]) for j,v in enumerate(r)] for i,r in enumerate(row['gram_numerators'])]
def decomposition(program,row,features):
 weights={t['feature']['feature_id']:F(t['weight']) for t in program['corrections']}
 w=[weights.get(f['feature_id'],F(0)) for f in features];m=matrix(row)
 cross=2*sum((w[i]*m[0][i+1] for i in range(len(w))),F(0))
 eb=sum((w[i]*w[j]*m[i+1][j+1] for i in range(len(w)) for j in range(len(w))),F(0))
 eh=m[0][0]+cross+eb
 if eb<0 or eh<0:raise ValueError('negative squared energy')
 return dict(X=row['X'],E_G=str(m[0][0]),signed_cross=str(cross),E_B=str(eb),E_H=str(eh),full_energy_identity_verified=True,E_H_over_E_G=None if m[0][0]==0 else str(eh/m[0][0]),finite_energy_improvement=eh<m[0][0])
def counts(score):return {mode:{k:v for k,v in data.items() if k!='observations'} for mode,data in score['modes'].items()}
def failures(score):
 return {mode:[dict(X=o['X'],q=o['level'],observed=o['observed'],bound=o['bound'],margin=o['margin'],dyadic_vs_offdomain='dyadic' if o['X']>0 and o['X']&(o['X']-1)==0 else 'offdomain',global_claim_refuted=False) for o in data['observations'] if o['finite_pass'] is False] for mode,data in score['modes'].items()}
def alias_key(f):
 h=f['core_depth'];theta=F(f['theta'])
 return (h,'saturated' if theta>=F(1,2*(h+1)) else str(theta))
def build_report(run):
 d=Path(run);verification=read(d/'verification.json')
 if verification.get('all_passed') is not True:raise ValueError('independent verification must pass')
 for name,h in verification['input_sha256'].items():
  if sha(d/name)!=h:raise ValueError('verified input changed: '+name)
 for name,h in verification['code_sha256'].items():
  if sha(d/'frozen_source'/name)!=h:raise ValueError('frozen source changed: '+name)
 spec=read(d/'protocol.json');features=spec['features'];batch=read(d/'candidate_batch.json');queue=read(d/'proof_queue.json')['queue'];validation=read(d/'validation.json');final=read(d/'final_evaluation.json')
 datasets={'training':read(d/'training.json'),'validation':read(d/'validation_data.json'),'final':final['data']}
 coverage={};ranks={}
 for label,data in datasets.items():
  value=data['profile']['value'];sources=value['source_profiles'];fc=[]
  for f in features:
   records=[r for r in sources if r['feature_id']==f['feature_id']]
   fc.append(dict(feature=f,unit_core_count=sum(r['class_counts'][1] for r in records),nonunit_count=sum(r['class_counts'][2] for r in records),first_unit_activation=min((r['X'] for r in records if r['class_counts'][1]),default=None),first_nonunit_activation=min((r['X'] for r in records if r['class_counts'][2]),default=None),counts_are_across_distinct_source_profiles_not_unique_integers=True))
  coverage[label]=fc;ranks[label]={}
  for target in spec['targets']:
   tid=digest(target);rows=[r for r in value['rows'] if r['target_id']==tid and r['X'] in data['base_scales']]
   pooled=[[sum((matrix(r)[i+1][j+1] for r in rows),F(0)) for j in range(len(features))] for i in range(len(features))]
   ranks[label][tid]=dict(exact_pooled_correction_gram_rank=rank(pooled),base_scales=data['base_scales'],source_independence_claim=False)
 validation_scores={r['program_id']:r['score'] for r in validation['results']};final_scores={r['program_id']:r['score'] for r in final['results']};selected=[]
 for q in queue:
  p=q['exact_program'];pid=q['program_id'];tid=digest(p['target']);rows=[r for r in final['data']['profile']['value']['rows'] if r['target_id']==tid and r['X'] in final['data']['base_scales']]
  energies=[decomposition(p,r,features) for r in rows]
  observed={o['X']:F(o['observed']) for o in final_scores[pid]['modes']['direct']['observations'] if o['observed'] is not None}
  if any(e['X'] not in observed or F(e['E_H'])!=observed[e['X']] for e in energies):raise ValueError('stored full energy disagreement')
  groups={}
  for t in p['corrections']:
   key=str(alias_key(t['feature']));groups[key]=groups.get(key,F(0))+F(t['weight'])
  pure=all(v==0 for v in groups.values())
  dormant=[f['feature_id'] for f in features if all(next(r for r in coverage[k] if r['feature']['feature_id']==f['feature_id'])['nonunit_count']==0 for k in coverage)]
  selected.append(dict(program_id=pid,program=p,validation_counts=counts(validation_scores[pid]),final_counts=counts(final_scores[pid]),stored_failure_witnesses={'validation':failures(validation_scores[pid]),'final':failures(final_scores[pid])},global_claim_not_refuted_by_finite_failure=True,final_energy_decomposition=energies,nonunit_alias_weight_sums={k:str(v) for k,v in groups.items()},globally_nonunit_cancelled_by_proved_aliases=pure,finite_dormant_feature_ids=dormant,unit_gain_attribution_available=False))
 factories=batch['factories'];archive_counts=[]
 for factory in factories:
  archive=factory['proposal_archive']
  archive_counts.append(dict(target_id=factory['target_id'],proposals=len(archive),unique_candidates=len(factory['candidates']),aliases=sum(a.get('alias_of') is not None for a in archive),discarded=sum(bool(a.get('discarded')) for a in archive),missing_proposals=sum(a.get('program_id') is None for a in archive)))
 for name,h in verification['input_sha256'].items():
  if sha(d/name)!=h:raise ValueError('verified input changed during reporting: '+name)
 for name,h in verification['code_sha256'].items():
  if sha(d/'frozen_source'/name)!=h:raise ValueError('frozen source changed during reporting: '+name)
 if read(d/'verification.json')!=verification:raise ValueError('verification changed during reporting')
 return dict(schema=1,verified_aggregate_final_counts=verification['final_counts'],hashes_rechecked_at_end=True,global_claim_not_refuted_by_finite_failure=True,verification_sha256=sha(d/'verification.json'),verified_input_sha256=verification['input_sha256'],proposal_counts=archive_counts,selected_programs=selected,feature_coverage=coverage,pooled_correction_gram_ranks=ranks,h5_nonunit_absent=all(r['nonunit_count']==0 for rows in coverage.values() for r in rows if r['feature']['core_depth']==5),limitations=['Historical actual coefficient overlap; no unseen-prime holdout.','Uniform correction theorem and target pole bridge supplied before search; full H energy bound remains unproved.','Exact Gram rank measures these finite functions, not arithmetic source independence.','Unit-core and nonunit charge attribution requires additional unit/nonunit Gram matrices; full cross terms alone do not allocate gain.','Finite dormant features need not remain dormant at larger scales.'],global_bound_proved=False,RH_proved=False)
def main():
 parser=argparse.ArgumentParser();parser.add_argument('run');args=parser.parse_args();d=Path(args.run)
 if any((d/n).exists() for n in ('report.json','report.txt')):raise FileExistsError('fresh report paths required')
 report=build_report(d)
 with (d/'report.json').open('x') as f:json.dump(report,f,sort_keys=True,indent=2);f.write('\n')
 with (d/'report.txt').open('x') as f:
  f.write('Independent verification passed and hashes were rechecked.\n')
  f.write('Selected programs: '+str(len(report['selected_programs']))+'; h5 nonunit absent: '+str(report['h5_nonunit_absent'])+'\n')
  f.write('Verified aggregate final counts: '+json.dumps(report['verified_aggregate_final_counts'],sort_keys=True)+'\n')
  for p in report['selected_programs']:
   f.write(p['program_id']+' '+json.dumps(p['final_counts'],sort_keys=True)+'\n')
   for e in p['final_energy_decomposition']:f.write('  X='+str(e['X'])+' exact E_H/E_G='+str(e['E_H_over_E_G'])+' improvement='+str(e['finite_energy_improvement'])+'\n')
   f.write('  Stored failure witnesses: '+json.dumps(p['stored_failure_witnesses'],sort_keys=True)+'\n')
  f.write('Finite stored-constant failures do not refute the existential cofinal claim.\n')
  f.write('\n'+'\n'.join(report['limitations'])+'\nNo all-scale bound or RH proof is asserted.\n')
if __name__=='__main__':main()
