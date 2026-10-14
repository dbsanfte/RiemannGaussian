"""Posthoc exact old-witness pairings; missing dual coordinates stay unsupported.
No actual arithmetic values, primal fit or modification of the frozen witness.
"""
import pathlib,json,hashlib,math
from fractions import Fraction as F
import grouped_arithmetic_language as L
import cancellation_gcd_inverse_projection as G

def digest(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
def run(directory):
 d=pathlib.Path(directory);d.mkdir(exist_ok=False,parents=True)
 source=pathlib.Path('cancellation-arithmetic-results/pilot-001/factor-probe-001/native-dual-001/result.json');dual=json.loads(source.read_text())['dual'];y={(m['instance'],tuple(m['m'])):F(w)for m,w in zip(dual['monomials'],dual['weights'])}
 spec=dict(schema=1,scales=[1,2,3,5],source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),probe_source_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),groups=['one','parent_kernel','child_kernel','defect_kernel','antisymmetric_a_minus_b'],method='exact pairings only; unknown coordinates never filled by zero',global_bound_proved=False)
 with (d/'spec.json').open('x')as f:json.dump(spec,f,sort_keys=True,indent=2)
 primitive=[];groups=[]
 def pair(index,p):
  missing=[list(m)for m in p if (index,m)not in y]
  return dict(status='unsupported_domain'if missing else 'exact',missing=missing,dot=None if missing else str(sum((q*y[index,m]for m,q in p.items()),F(0))))
 for index,X in enumerate(spec['scales']):
  H=4*X-1;polys={}
  for a in range(1,H+1):
   for b in range(a,H+1):
    g=math.gcd(a,b);rho=dict(kind='unit')if g==1 else dict(kind='inverse_row',n=g);p=L.mul(L.relation(rho,'mu',H),{tuple(sorted((a,b))):F(1)});polys[a,b]=p;primitive.append(dict(instance=index,X=X,a=a,b=b,gcd=g,polynomial_sha256=digest(L.dump_poly(p)),pairing=pair(index,p)))
  for kernel in spec['groups']:
   p={}
   def K(scale,n):return max(0,2*scale-max(scale,n))
   for a in range(1,H+1):
    for b in range(1,H+1):
     w=1 if kernel=='one'else K(X,max(a,b))if kernel=='parent_kernel'else K(2*X,max(a,b))if kernel=='child_kernel'else K(2*X,max(a,b))-4*K(X,max(a,b))if kernel=='defect_kernel'else F(a-b,H)
     p=L.add(p,L.scale(polys[min(a,b),max(a,b)],w))
   groups.append(dict(instance=index,X=X,kernel=kernel,polynomial_sha256=digest(L.dump_poly(p)),pairing=pair(index,p)))
 summary=dict(primitive_total=len(primitive),primitive_supported=sum(r['pairing']['status']=='exact'for r in primitive),primitive_supported_nonzero=sum(r['pairing']['status']=='exact'and F(r['pairing']['dot'])!=0 for r in primitive),primitive_unsupported=sum(r['pairing']['status']!='exact'for r in primitive),group_supported_nonzero=sum(r['pairing']['status']=='exact'and F(r['pairing']['dot'])!=0 for r in groups))
 report=dict(spec=spec,summary=summary,primitive_pairings=primitive,complete_group_pairings=groups,new_dual_coordinates_assumed_zero=False,global_bound_proved=False,RH_proved=False)
 with (d/'results.json').open('x')as f:json.dump(report,f,sort_keys=True,indent=2)
 return report
if __name__=='__main__':
 import sys
 print(json.dumps(run(sys.argv[1])['summary']))
