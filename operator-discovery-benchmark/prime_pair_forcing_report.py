#!/usr/bin/env python3
"""Posthoc verified prime-pair report. Only standard-library imports."""
import argparse,hashlib,json
from fractions import Fraction as F
from pathlib import Path

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_text())
def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def bindings(d,v):
 for n,h in v['input_sha256'].items():
  if sha(d/n)!=h:raise ValueError('verified input changed: '+n)
 for n,h in v['code_sha256'].items():
  if sha(d/'frozen_source'/n)!=h:raise ValueError('frozen code changed: '+n)
def failures(score):
 return [dict(X=o['X'],q=o['level'],lower=o['lower'],upper=o['upper'],bound=o['bound'],lower_margin=o['lower_margin'],upper_margin=o['upper_margin'],domain='dyadic' if o['X']>0 and o['X']&(o['X']-1)==0 else 'odd_or_other_offdomain',global_claim_refuted=False) for o in score['observations'] if o['status']=='fail']
def coverage(hist,B):
 out={}
 for label,items in [('full',list(hist.values())),('retained',[v for h,v in hist.items() if int(h)<=B]),('complement',[v for h,v in hist.items() if int(h)>B])]:
  total=sum(v['triples'] for v in items);zero=sum(v['zero_terms'] for v in items)
  out[label]=dict(triples=total,zero_terms=zero,active_nonzero_terms=total-zero)
 if any(out['full'][k]!=out['retained'][k]+out['complement'][k] for k in out['full']):raise ValueError('coverage partition mismatch')
 return out

def block(row,hist):
 X=row['X'];D=row['D'];s=F(row['exact_full_S']);energy=row['original_energy'];cert=row['component_certificate']
 if row['Delta']!=energy['A_2X']-4*energy['A_X'] or F(row['Delta'])!=row['J1']-2*row['kappa']*s:raise ValueError('full arithmetic identity mismatch')
 if not F(row['S']['lo'],D)<=s<=F(row['S']['hi'],D):raise ValueError('full interval excludes exact identity')
 if any(row['S'][side]!=row['prefix'][side]+row['remainder'][side] for side in ('lo','hi')):raise ValueError('split endpoint mismatch')
 if digest(hist)!=row['histogram_sha256']:raise ValueError('histogram changed')
 cost=F(cert['scalar'])*(2+X.bit_length())**cert['log_4X_power'] if cert['cofinal_critical_component_bound'] else None
 return dict(X=X,B=row['B'],target=row['target'],original_target_diagnostics=dict(Delta=row['Delta'],A_X=energy['A_X'],A_2X=energy['A_2X'],normalized_energy=str(F(energy['A_X'],X*X)),normalized_innovation=str(F(row['Delta'],4*X*X)),diagnostic_only=True),forcing=dict(exact_full_S=str(s),interval_denominator=D,full_S_ticks=row['S'],retained_prefix_ticks=row['prefix'],complement_remainder_ticks=row['remainder'],normalized_negative_remainder=row['normalized_negative_remainder'],identity_verified=True),coverage=coverage(hist,row['B']),supplied_uniform_prefix_certificate=cert,coarse_uniform_normalized_prefix_cost=None if cost is None else str(cost),coarse_cost_rule='scalar*(2+bit_length(X))^degree; 1+log(4X)<=2+bit_length(X)',unknown_remainder_law_proved=False)

def build_report(run):
 d=Path(run)
 if not (d/'seal.json').exists():raise ValueError('candidate seal required before reporting')
 v=read(d/'verification.json');vh=sha(d/'verification.json')
 if v.get('all_passed') is not True:raise ValueError('independent verification must pass')
 bindings(d,v)
 batch=read(d/'candidate_batch.json');queue=read(d/'proof_queue.json')['queue'];validation=read(d/'validation.json');final=read(d/'final_evaluation.json');spec=read(d/'protocol.json')
 factories=batch['factories'];attempts=[]
 for f in factories:
  if len(f['proposal_archive'])!=14:raise ValueError('full fourteen-program archive required')
  attempts.append(dict(target=f['target'],attempts=len(f['proposal_archive']),admitted=sum(c['conditional_auxiliary']['auxiliary_bound_admitted'] for c in f['candidates']),exploratory=sum(not c['conditional_auxiliary']['auxiliary_bound_admitted'] for c in f['candidates']),programs=[dict(program_id=c['program_id'],exact_program=c['program'],conditional_auxiliary=c['conditional_auxiliary'],training_counts={k:x for k,x in c['training_score'].items() if k!='observations'}) for c in f['candidates']]))
 validation_scores={r['program_id']:r['score'] for r in validation['results']};final_scores={r['program_id']:r['score'] for r in final['results']}
 profile=final['data']['profile'];selected=[]
 for q in queue:
  pid=q['program_id'];p=q['exact_program'];rows=[r for r in profile['value']['rows'] if r['target']==p['target'] and r['cutoff']==p['cutoff']]
  selected.append(dict(program_id=pid,exact_program=p,selection_origins=q['selection_origins'],final_interval_score=final_scores[pid],validation_stored_failure_witnesses=failures(validation_scores[pid]),final_stored_failure_witnesses=failures(final_scores[pid]),blocks=[block(r,profile['value']['histograms'][r['histogram_id']]) for r in rows],global_claim_not_refuted_by_finite_failure=True))
 report=dict(schema=1,verification_sha256=vh,verified_input_sha256=v['input_sha256'],attempts=attempts,total_attempts=sum(x['attempts'] for x in attempts),selected_programs=selected,verified_final_counts=v['final_counts'],full_identity='Delta_f(X)=J_X(1)-2*kappa*(S_B(X)+R_B(X)); J_X(1)=-2X',required_direction='Lower bound R_B >= -Cq X^2 ceil(X^(1/q)); equivalent upper bound on -R_B. The known absolute S_B bound is an additional recovery charge.',limitations=['Stored constants only; their finite failures do not refute existential constants or unknown q0.','Missing unknown levels and unresolved intervals are reported separately; neither counts as a pass.','Complete actual coefficients overlap historical stages; no unseen-prime holdout.','Exact forcing identity, core partition, interval rules and uniform auxiliary theorem were supplied; numerical search learned only cutoff choices and finite constants.','Original target energies/defects are separate diagnostics; they do not prove the remainder law.','Auxiliary control and pole recovery are conditional bridges; full uniform signed estimate remains unproved.'],global_bound_proved=False,full_signed_bound_proved=False,RH_proved=False)
 bindings(d,v)
 if sha(d/'verification.json')!=vh:raise ValueError('verification changed during report')
 report['hashes_rechecked_at_end']=True
 return report

def main():
 parser=argparse.ArgumentParser();parser.add_argument('run');args=parser.parse_args();d=Path(args.run)
 if any((d/n).exists() for n in ('report.json','report.txt')):raise FileExistsError('fresh report output paths required')
 r=build_report(d)
 with (d/'report.json').open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
 with (d/'report.txt').open('x') as f:
  f.write('Verified complete signed prime-pair forcing report\n'+r['full_identity']+'\n'+r['required_direction']+'\n')
  f.write('Attempts: '+str(r['total_attempts'])+'; verified final counts: '+json.dumps(r['verified_final_counts'],sort_keys=True)+'\n')
  for p in r['selected_programs']:
   f.write(p['program_id']+' '+json.dumps(p['exact_program'],sort_keys=True)+'\n')
   f.write('Final score counts: '+json.dumps({k:v for k,v in p['final_interval_score'].items() if k!='observations'},sort_keys=True)+'\n')
   f.write('Stored failure witnesses: '+json.dumps(p['final_stored_failure_witnesses'],sort_keys=True)+'\n')
   for b in p['blocks']:f.write('X='+str(b['X'])+' B='+str(b['B'])+' Delta='+str(b['original_target_diagnostics']['Delta'])+' normalized -R interval='+json.dumps(b['forcing']['normalized_negative_remainder'],sort_keys=True)+' coverage='+json.dumps(b['coverage'],sort_keys=True)+'\n')
  f.write('\n'+'\n'.join(r['limitations'])+'\nNo full bound or RH proof asserted.\n')
if __name__=='__main__':main()
