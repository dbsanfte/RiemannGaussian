"""Independent complete posthoc direction/finite-certificate audit."""
import json,sys,copy
from pathlib import Path
from fractions import Fraction as F
import check_cancellation_arithmetic_run as I
import check_grouped_arithmetic as G
P=I.P

def descriptors():
 atoms=['prefix','half','even','mod3one','prime'];out=[]
 for region in ['parent','child']:
  for j,left in enumerate(atoms):
   for right in atoms[j+1:]:
    for c in ['-3','-2','-1/2','1/2','2','3']:
     d=dict(family='rational_atom_mix',region=region,left=left,right=right,coefficient=c);out.append(dict(d,id=I.digest(d)))
 return out

def group(d,X):
 return [dict(weight='1',poly=P.canonical(P.add(I.contrast(d['left'],t),I.contrast(d['right'],t),F(d['coefficient'])))) for t in (range(X,2*X) if d['region']=='parent' else range(2*X,4*X))]

def proposals(instances,dual,scales,cap):
 y={(r['instance'],tuple(r['m'])):F(w) for r,w in zip(dual['monomials'],dual['weights'])};rows=[]
 for d in descriptors():
  groups=[group(d,X) for X in scales]+[[] for _ in instances[len(scales):]];expanded=[];dot=F(0)
  for j,g in enumerate(groups):
   p={}
   for term in g:
    a=P.parse(term['poly'],instances[j]['horizon']);p=P.add(p,P.multiply(a,a))
   I.require(all((j,m) in y for m in p),'full proposed dual domain');dot+=sum((v*y[j,m] for m,v in p.items()),F(0));expanded.append(P.canonical(p))
  rows.append(dict(descriptor=d,column_sha256=I.digest(expanded),groups_sha256=I.digest(groups),dot=str(dot),normalized_dot=str(dot/(1+F(d['coefficient'])**2)),negative=dot<0))
 selected=sorted([r for r in rows if r['negative']],key=lambda r:(F(r['normalized_dot']),r['descriptor']['id']))[:cap]
 return rows,selected

def audit(parent):
 parent=Path(parent);d=parent/'adaptive-probe-001';s=I.read(d/'spec.json');src=I.read(d/'source_seal.json');names=['spec','source_seal','seal','proposals','selection_seal','training','candidate_seal','final','tests','producer_receipt'];hashes={n:I.sha(d/(n+'.json')) for n in names}
 def bindings():
  I.require(I.read(d/'seal.json')==dict(spec_sha256=I.sha(d/'spec.json'),source_seal_sha256=I.sha(d/'source_seal.json')),'source seal')
  for n,h in src['hashes'].items():I.require(I.sha(d/'frozen_source'/n)==h and I.sha(Path(__file__).parent/n)==h,'source '+n)
  for n,h in I.read(parent/'source_seal.json')['hashes'].items():I.require(I.sha(parent/'frozen_source'/n)==h and I.sha(Path(__file__).parent/n)==h,'parent source '+n)
  for key,path in [('parent_training',parent/'training.json'),('parent_verification',parent/'independent_verification.json'),('dual_result',parent/'dual-probe-002/result.json'),('dual_verification',parent/'dual-probe-002/independent_verification.json')]:I.require(s[key+'_sha256']==I.sha(path),'input '+key)
 bindings();I.require(s['descriptors']==descriptors() and s['max_new_groups']==8 and s['attempt_index']==26 and s['final_scales']==[11,13],'frozen dictionary/scope');I.require(I.read(parent/'independent_verification.json')['all_passed'] and I.read(parent/'dual-probe-002/independent_verification.json')['all_passed'],'prior verification')
 a=I.read(parent/'training.json')['attempts'][26];pr=a['program'];scales=I.read(parent/'protocol.json')['training_scales'];base=[I.build(pr,X)['instance'] for X in scales]+[I.auxiliary_constraint(I.descriptors())['instance']];I.require(list(map(I.digest,base))==a['case_hashes']+a['auxiliary_hashes'],'original source cases');dual=I.read(parent/'dual-probe-002/result.json')['dual'];G.verify_joint_dual(base,dual,allow_constant_slack=True)
 rows,selected=proposals(base,dual,scales,8);archive=I.read(d/'proposals.json');I.require(archive['candidates']==rows and archive['selected']==selected and archive['candidate_archive_sha256']==I.digest(rows) and archive['selected_sha256']==I.digest(selected),'all120 scores/ranking');ds=I.descriptors();ds['square'].extend(r['descriptor'] for r in selected)
 def augmented(X):
  v=I.build(pr,X)['instance']
  for r in selected:v['square_groups'].append(group(r['descriptor'],X))
  return v
 ordinary=[augmented(X) for X in scales];instances=ordinary+[I.auxiliary_constraint(ds)['instance']];sel=I.read(d/'selection_seal.json');I.require(sel==dict(proposals_sha256=hashes['proposals'],selected_sha256=I.digest(selected),dictionary_sha256=I.digest(ds),case_hashes=list(map(I.digest,instances))),'selection before synthesis')
 t=I.read(d/'training.json');r=t['synthesis'];I.require(t['program']==pr and t['case_hashes']==list(map(I.digest,instances)),'training cases');G.verify_joint_result(instances,r,allow_constant_slack=True);accepted=r['status']=='finite_certificate'
 if accepted:
  gamma=sum((F(c)*F(w) for c,w in zip(I.auxiliary_constraint(ds)['gamma_coefficients'],r['weights']['relation_weights'])),F(0));I.require(gamma==0 and t['gamma']==str(gamma),'exact new dictionary gamma');I.require(t['budgets']==[I.budget(v,r['weights']) for v in ordinary],'training budgets')
 else:I.require(t['gamma'] is None and t['budgets']==[],'no candidate audit')
 I.require(I.read(d/'candidate_seal.json')==dict(training_sha256=hashes['training'],selection_seal_sha256=hashes['selection_seal']),'candidate seal');final=I.read(d/'final.json');I.require(final['refitted'] is False and final['status']==('evaluated' if accepted else 'no_candidate'),'no refit');obs=final['observations'];I.require([v['X'] for v in obs]==([11,13] if accepted else []),'final coverage')
 for o in obs:
  v=augmented(o['X']);I.require(o['case_sha256']==I.digest(v) and o['scalar_budget']==I.budget(v,r['weights']),'final case/budget');residual=I.B.residual(v,r['weights']);valid=all(not m for m in residual) and residual.get((),F(0))>=0
  if o['status']=='finite_certificate':I.require(valid,'final full identity');G.verify_joint_result([v],dict(status='finite_certificate',weights=r['weights'],certificates=[o['certificate']],constant_slacks=[str(residual.get((),F(0)))]),allow_constant_slack=True)
  elif o['status']=='template_mismatch':I.require(not valid,'exact mismatch witness')
  else:I.require(o['status']=='missing_resource' and bool(o['reason']),'retained resource missingness')
 receipt=I.read(d/'producer_receipt.json')
 for n in ['proposals','training','final','tests','selection_seal','candidate_seal']:I.require(receipt[n+'_sha256']==hashes[n],'receipt '+n)
 I.require(I.read(d/'tests.json')['returncode']==0,'focused tests');bindings();I.require(hashes=={n:I.sha(d/(n+'.json')) for n in names},'end hashes')
 return dict(all_passed=True,input_sha256=hashes,candidates=120,negative=sum(v['negative'] for v in rows),selected=len(selected),training_status=r['status'],final_statuses=[v['status'] for v in obs],posthoc_outcome_conditioned=True,global_bound_proved=False,RH_proved=False)
if __name__=='__main__':
 p=Path(sys.argv[1]);r=audit(p)
 with (p/'adaptive-probe-001/independent_verification.json').open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
 print(json.dumps(r))
