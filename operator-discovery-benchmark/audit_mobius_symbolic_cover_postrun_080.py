from pathlib import Path
from fractions import Fraction as Q
import json,math
root=Path('/home/dbsanfte/riemann/operator-discovery-benchmark')
p=next((root/'fractional-prime-kernel-results').rglob('symbolic_cover_followup_001'))
report=json.loads((p/'report.json').read_text());meta=json.loads((p/'source_metadata.json').read_text());manifest=json.loads((p/'frozen_candidates.json').read_text());draw=json.loads((p/'validation_draw.json').read_text());inventory=json.loads((p/'known_parent_inventory.json').read_text())
assert not set(draw['parents'])&set(inventory['parents'])
def evalpoly(poly,x):
 v=Q(0)
 for c in reversed(poly):v=v*x+c
 return v
def span(poly,lo,hi):
 v=[evalpoly(poly,lo),evalpoly(poly,hi)]
 if len(poly)==3 and poly[2]:
  x=-poly[1]/(2*poly[2])
  if lo<=x<=hi:v.append(evalpoly(poly,x))
 return min(v),max(v)
def product(a,b):return [a[0]*b[0],a[0]*b[1]+a[1]*b[0],a[1]*b[1]]
rows={};audits=[];arithmetic_checks=0
for c in manifest['candidates']:
 assert c==json.loads((p/('candidate_'+c['id']+'.json')).read_text())
 target=c['frame']['target'];rays=[[list(map(Q,x)) for x in a] for a in c['frame']['rays']];lo=Q(c['logspec']['lower']);hi=Q(c['logspec']['upper'])
 assert all([rays[0][i][j]+rays[1][i][j] for j in (0,1)]==[Q(target[i]),Q(0)] for i in range(10))
 inactive=meta[c['source_id']]['inactive_admissions'][c['gamma']]['indices'];assert target==[int(i not in inactive) for i in range(10)]
 kappas=list(map(Q,c['kappas']));K=Q(meta[c['source_id']]['norm']['certificate']['K']);w=[]
 for a,k in zip(rays,kappas):
  am=max(max(abs(evalpoly(x,lo)),abs(evalpoly(x,hi))) for x in a);v=3*K*k*am*am*2**48;n=math.isqrt(v.numerator//v.denominator);w.append(Q(n if n*n==v else n+1,2**24))
 assert sum(w,Q(0))**2==Q(c['certificate']['price'])
 checks=json.loads((p/('validation_checks_'+c['id']+'.json')).read_text());counts={'CERTIFIED_FINITE':0,'REFUTED_FINITE':0,'UNRESOLVED_INTERVAL':0};negative_cross=0;cross_ambiguous=0;examples=[]
 for k,u in enumerate(draw['parents']):
  if u not in rows:rows[u]=json.loads((p/('source_'+str(u)+'.json')).read_text())
  item=rows[u]['records'][c['source_id']][c['gamma']];assert item['cell_admission']['status']=='VERIFIED_CELLS';assert item['source_pair_admission']['status']=='VERIFIED_SOURCE_PAIR'
  payload=item['payload'];D=[Q(v.get('1','0')) for v in payload['flux_features']];B={(e['i'],e['j']):sum((Q(t['coefficient']) for t in e['terms']),Q(0)) for e in payload['gram_upper']};SS=[]
  for leaf,a in enumerate(rays):
   stored=checks['leaves'][leaf]['checks'][k];assert stored['u']==u
   S=[sum((a[i][j]*D[i] for i in range(10)),Q(0)) for j in (0,1)];Gram=[Q(0)]*3
   for (i,j),b in B.items():
    term=product(a[i],a[j]);Gram=[x+y*b*(1 if i==j else 2) for x,y in zip(Gram,term)]
   assert S==list(map(Q,stored['S_polynomial']));assert Gram==list(map(Q,stored['Q_polynomial']));assert span(Gram,lo,hi)==(Q(stored['Q_lower']),Q(stored['Q_upper']));assert span(product(S,S),lo,hi)==(Q(stored['S_squared_lower']),Q(stored['S_squared_upper']))
   lower=Q(stored['difference_lower']);upper=Q(stored['difference_upper']);status='CERTIFIED_FINITE' if upper<=0 else 'REFUTED_FINITE' if lower>0 else 'UNRESOLVED_INTERVAL';assert status==stored['status'];counts[status]+=1
   if c['q']=='1':
    diff=[x-kappas[leaf]*y for x,y in zip(product(S,S),Gram)];assert span(diff,lo,hi)==(lower,upper)
   if status=='REFUTED_FINITE' and not any(e['leaf']==leaf for e in examples):examples.append({'leaf':leaf,'u':u,'difference_lower':str(lower)})
   SS.append(S);arithmetic_checks+=1
  binding=item['source_pair_admission'];assert [SS[0][j]+SS[1][j] for j in (0,1)]==[Q(binding['parent_residual'])-Q(binding['child_residual']),Q(0)]
  cr=span([2*v for v in product(*SS)],lo,hi)
  if cr[1]<0:negative_cross+=1
  elif cr[0]<=0<=cr[1]:cross_ambiguous+=1
 for key,field in [('CERTIFIED_FINITE','certified'),('REFUTED_FINITE','refuted'),('UNRESOLVED_INTERVAL','unresolved')]:assert counts[key]==checks[field]
 sig=[]
 for a in rays:sig.append({'mode_polynomial':[str(-a[1][0]),str(-a[1][1]+a[9][0]),str(a[9][1])],'unknown_channels':[i for i,x in enumerate(a) if any(x) and i not in (1,9)]})
 audits.append({'id':c['id'],'gamma':c['gamma'],'mode':c['mode'],'rays':c['frame']['rays'],'kappas':c['kappas'],'price':c['certificate']['price'],'counts':counts,'negative_cross_rows':negative_cross,'cross_ambiguous_rows':cross_ambiguous,'examples':examples,'supported_signatures':sig})
print(json.dumps({'out':str(p),'report':report,'arithmetic_leaf_polynomial_checks':arithmetic_checks,'candidate_audits':audits},indent=2))
