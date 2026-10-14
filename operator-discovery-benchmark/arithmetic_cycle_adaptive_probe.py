"""Sealed bounded adaptive cone calibration, not a uniform arithmetic proof."""
import argparse,json
from pathlib import Path
import arithmetic_cycle_separation_probe as P
import arithmetic_cycle_synthesis as S
import check_arithmetic_cycle_certificate as checker
ROOT=Path(__file__).resolve().parent
CODE=['arithmetic_cycle_adaptive_probe.py','arithmetic_cycle_separation_probe.py','arithmetic_cycle_language.py','arithmetic_cycle_synthesis.py','check_arithmetic_cycle_certificate.py']
LIMITS=dict(max_columns=1024,max_monomials=10000,max_operations=200000000,max_coefficient_bits=2048,max_denominator=1000000,time_limit=10)
def freeze(directory):
 directory=Path(directory)
 if directory.exists():raise ValueError('new unique probe directory required')
 dev=json.loads((P.PILOT/'development.json').read_text());selected=[a for a in dev['attempts'] if a['case']==dict(target='mu',X=2,q=2,C=1,mode=a['case']['mode'])]
 if len(selected)!=2:raise ValueError('exact initial cases unavailable')
 directory.mkdir(parents=True);(directory/'frozen_source').mkdir();hashes={}
 for name in CODE:(directory/'frozen_source'/name).write_bytes((ROOT/name).read_bytes());hashes[name]=P.hashfile(ROOT/name)
 spec=dict(schema=1,cases=[a['case'] for a in selected],initial_template_sha256=[P.digest(a['template']) for a in selected],development_sha256=P.hashfile(P.PILOT/'development.json'),max_promotions=16,limits=LIMITS,enumeration='same original679 candidates; absent dual coordinates explicit; first witness by degree/terms/indexsum/canonical payload',posthoc=True,no_actual_coefficient_response=True,scope='development-conditioned adaptive finite certificate feasibility, not uniform operator discovery')
 P.write(directory/'spec.json',spec);P.write(directory/'seal.json',dict(spec_sha256=P.hashfile(directory/'spec.json'),source_hashes=hashes));return directory
def run(directory):
 directory=Path(directory);spec=json.loads((directory/'spec.json').read_text());seal=json.loads((directory/'seal.json').read_text());assert P.hashfile(directory/'spec.json')==seal['spec_sha256'] and P.hashfile(P.PILOT/'development.json')==spec['development_sha256']
 for name,h in seal['source_hashes'].items():assert P.hashfile(ROOT/name)==h==P.hashfile(directory/'frozen_source'/name)
 dev=json.loads((P.PILOT/'development.json').read_text());trajectories=[]
 for case,initial_hash in zip(spec['cases'],spec['initial_template_sha256']):
  original=next(a['template'] for a in dev['attempts'] if a['case']==case);assert P.digest(original)==initial_hash;current=json.loads(json.dumps(original));iterations=[];stop=None
  for step in range(spec['max_promotions']):
   before=P.digest(current);dual=P.dual(current);iteration=dict(step=step,current_template_sha256=before,dual=dual,extension_tests=[],ranked_witnesses=[],chosen=None,next_template_sha256=None,resynthesis=None,independent_check=None)
   if not dual['certified']:stop='no_exact_separator';iterations.append(iteration);break
   from fractions import Fraction as F
   y={tuple(m):F(v) for m,v in zip(dual['monomials'],dual['weights'])};tests,ranked=P.candidate_extensions(original,y,spec);iteration.update(extension_tests=tests,ranked_witnesses=ranked)
   if not ranked:stop='no_supported_witness';iterations.append(iteration);break
   chosen=ranked[0];iteration['chosen']=chosen
   if chosen['kind']=='square':current['square_basis'].append(chosen['payload']['poly'])
   else:current['relation_columns'].append([chosen['payload']])
   iteration['next_template_sha256']=P.digest(current);result=S.synthesize('mu',7,current['lhs'],current['square_basis'],current['relation_columns'],**spec['limits']);iteration['resynthesis']=result
   if result['status']=='finite_certificate':iteration['independent_check']=checker.verify_defect_certificate(result['certificate'],2,'8');stop='finite_certificate'
   elif result['status']=='missing_resource':stop='missing_resource'
   iterations.append(iteration);print(case['mode']+' step'+str(step+1)+' '+result['status'],flush=True)
   if stop:break
  if stop is None:stop='promotion_limit'
  trajectories.append(dict(case=case,initial_template_sha256=initial_hash,iterations=iterations,stop_reason=stop,promotions=sum(i['chosen'] is not None for i in iterations),final_template=current,final_template_sha256=P.digest(current),global_bound_proved=False));P.write(directory/(case['mode']+'-trajectory.json'),trajectories[-1])
 for name,h in seal['source_hashes'].items():assert P.hashfile(ROOT/name)==h==P.hashfile(directory/'frozen_source'/name)
 P.write(directory/'results.json',dict(schema=1,trajectories=trajectories,seal_sha256=P.hashfile(directory/'seal.json'),trajectory_hashes={t['case']['mode']:P.hashfile(directory/(t['case']['mode']+'-trajectory.json')) for t in trajectories},posthoc=True,global_bound_proved=False,RH_proved=False));return trajectories
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('command',choices=['freeze','run']);p.add_argument('directory');a=p.parse_args();freeze(a.directory) if a.command=='freeze' else run(a.directory)
