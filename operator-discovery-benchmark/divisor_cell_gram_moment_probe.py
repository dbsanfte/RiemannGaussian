"""Preregistered exact 2x2 dual moment audit, no signed arithmetic values."""
from fractions import Fraction as F
import check_cancellation_divisor_cells as C

def contexts():return [dict(region=r,theta=t,power=j)for r in C.SPEC['regions']for t in C.SPEC['thetas']for j in C.SPEC['powers']]
def probe(dual,scales,*,max_horizon=80,max_operations=20000000):
 if type(scales)is not list or any(type(x)is not int or x<1 for x in scales):raise ValueError('ordinary scales')
 if len(dual['monomials'])!=len(dual['weights']):raise ValueError('dual dimensions')
 y={}
 for row,w in zip(dual['monomials'],dual['weights']):
  if type(row)is not dict or set(row)!={'instance','m'} or type(row['instance'])is not int or row['instance']<0 or type(row['m'])is not list or any(type(n)is not int or n<1 for n in row['m'])or row['m']!=sorted(row['m']):raise ValueError('dual coordinate')
  key=(row['instance'],tuple(row['m']))
  if key in y:raise ValueError('duplicate dual coordinate')
  y[key]=C.rat(w,16384)
 records=[];work=0
 for desc in contexts():
  polynomials=[{}for _ in range(3)]
  for z,X in enumerate(scales):
   if 4*X-1>max_horizon:raise OverflowError('source horizon')
   ts=range(X,2*X)if desc['region']=='parent'else range(2*X,4*X)
   for t in ts:
    work+=t*t
    if work>max_operations:raise OverflowError('complete construction work')
    r=C.core(t,[str(F(a)**desc['power'])for a in range(1,t+1)],dict(kind='divisor_le',coefficient='1',power=desc['theta']))
    for k,(A,B)in enumerate([(r['P'],r['P']),(r['P'],r['D']),(r['D'],r['D'])]):
     work+=len(A)*len(B)
     if work>max_operations:raise OverflowError('complete polynomial work')
     for m,q in C.P.multiply(A,B).items():
      key=(z,m);polynomials[k][key]=polynomials[k].get(key,F(0))+q
  absent=sorted({key for p in polynomials for key,q in p.items()if q and key not in y})
  row=dict(desc,complete_column_sha256=C.digest([[dict(instance=z,m=list(m),coefficient=str(q))for (z,m),q in sorted(p.items())if q]for p in polynomials]),unsupported_coordinates=[dict(instance=z,m=list(m))for z,m in absent])
  if absent:row.update(status='unknown_domain',extension_chosen=False)
  else:
   a,b,c=[sum((q*y[key]for key,q in p.items()),F(0))for p in polynomials];det=a*c-b*b;psd=a>=0 and c>=0 and det>=0
   row.update(status='supported',a=str(a),b=str(b),c=str(c),determinant=str(det),PSD=psd,old_witness_separates_this_2x2_cone=psd)
  records.append(row)
 return dict(contexts=records,context_count=18,extension_chosen=False,full_2x2_failures=sum(r.get('PSD')is False for r in records),unknown_contexts=sum(r['status']=='unknown_domain'for r in records),scope='A negative moment or determinant invalidates this witness for the expanded cone only; no feasibility or bound theorem.',global_bound_proved=False,RH_proved=False)
