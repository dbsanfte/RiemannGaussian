#!/usr/bin/env python3
"""Optional ball-arithmetic audit of the coupled synthetic Riesz response.

Every returned ball encloses rounding in one FINITE numerical expression.
It does NOT enclose its continuum limit, quadrature/interpolation error, or
an actual prime sum. The modes 0, 1/40000 +/- (3/500)i have multiplicities
1,3,3; they are not asserted to be zeta zeros. Keep outside ordinary CI.

The finite expression retains the two original factorial faces, owner-order
band, full phase, exact integer-floor length, and the core radial interval.
Both empty exponential atoms are included. The one-cofactor head is replaced
by its exact analytic value before interpolation; its two faces cancel after
calibration to their common exact owner marginal. Calibration corrects one
known quadrature moment, not all quadrature errors. The reported omitted-count
allowance bounds the lattice classes above 55 / 13, NOT arithmetic labels.

Install scripts/requirements-riesz-balls.txt in an optional environment.
See docs/zeta-riesz-joined-ball-audit.md for scope and reproduction.
"""
from flint import arb,arb_series,ctx,fmpz
import argparse,hashlib,importlib.metadata,math,time,json,multiprocessing
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
from scipy.linalg import eigh_tridiagonal

def legendre(n,lo,hi):
 out=[]
 for k in range(n):
  x,w=arb.legendre_p_root(n,k,weight=True)
  out.append((lo+(hi-lo)*(x+1)/2,w*(hi-lo)/2))
 return out

def beta_rule(a,b,n):
 # Work in centered, variance-one coordinates to avoid ill-conditioned
 # raw moment calculations at N near a million.
 a=arb(a);b=arb(b);mu=a/(a+b);sd=(a*b/((a+b)**2*(a+b+1))).sqrt()
 alpha=b-1;beta=a-1;s=alpha+beta
 ds=[(((beta-alpha)*s/((2*i+s)*(2*i+s+2))+1)/2-mu)/sd for i in range(n)]
 es=[(j*(j+alpha)*(j+beta)*(j+s)/((2*j+s-1)*(2*j+s+1))).sqrt()/(2*j+s)/sd for j in range(1,n)]
 squares=[e*e for e in es]
 seeds=eigh_tridiagonal([float(x) for x in ds],[float(x) for x in es],eigvals_only=True)
 def poly(x):
  p0,p1=arb(1),x-ds[0];d0,d1=arb(0),arb(1)
  for j in range(1,n):
   p0,p1=p1,(x-ds[j])*p1-squares[j-1]*p0
   d0,d1=d1,p0+(x-ds[j])*d1-squares[j-1]*d0
  return p1,d1
 out=[]
 for seed in seeds:
  x=arb(float(seed))
  for _ in range(4):
   v,d=poly(x);x=(x-v/d).mid()
  v,d=poly(x)
  eps=arb(2)**(-ctx.prec+40)+4*abs(v/d).upper()
  for _ in range(50):
   left,right=poly(x-eps)[0],poly(x+eps)[0]
   if left*right<0:break
   eps*=2
  else:raise ArithmeticError('Jacobi root not bracketed')
  x=arb(x,eps.upper())
  pol=[arb(1)]
  if n>1:pol.append((x-ds[0])/es[0])
  for j in range(1,n-1):pol.append(((x-ds[j])*pol[-1]-es[j-1]*pol[-2])/es[j])
  weight=1/sum(q*q for q in pol)
  out.append((mu+sd*x,weight))
 assert all(0<x and x<1 and 0<w for x,w in out)
 assert all(out[j][0]<out[j+1][0] for j in range(n-1))
 assert sum(w for x,w in out).contains(1)
 for k in range(min(8,2*n)):
  observed=sum(w*x**k for x,w in out)
  expected=arb(1)
  for j in range(k):expected*=((a+j)/(a+b+j))
  assert observed.overlaps(expected),(k,observed,expected)
 return out

def binomial_tail(q,n,j):
 # P[Bin(n,q)>=j], including rounded evaluation error. Far tails use
 # Hoeffding only as an enclosure for this finite probability.
 if j<=0:return arb(1)
 if j>n:return arb(0)
 if q<=0:return arb(0)
 if q>=1:return arb(1)
 if q<arb(j)/n:
  eps=(-2*n*(arb(j)/n-q)**2).exp()
  if eps<arb(2)**(-200):return arb(0,eps.upper())
 if arb(j-1)/n<q:
  eps=(-2*n*(q-arb(j-1)/n)**2).exp()
  if eps<arb(2)**(-200):return arb(1,eps.upper())
 with ctx.workprec(224):
  return q.beta_lower(j,n-j+1,regularized=True)

def tables(T,r,ell,size,L):
 ctx.cap=size
 theta=3*T*r/(500*ell);q0=(-T*r/(40000*ell)).exp()
 q0n=q0**ell
 g=[arb(0)]*size
 for i in range(ell,size):
  g[i]=(q0n+6*(i*theta).cos())/i
  if i==ell:g[i]/=2
  q0n*=q0
 G=arb_series(g,prec=size);A=(-G).exp();B=G.exp()
 gap=(1-L/T)/r;first=math.floor(float(gap)*ell)+1
 assert arb(first)/ell>gap and arb(first-1)/ell<gap
 aa=A.coeffs();ww=[arb(0)]*size;head=[arb(0)]*size
 for i in range(max(first,0),size):
  ramp=arb(i)/ell-gap
  ww[i]=aa[i]*ramp;head[i]=g[i]*ramp
 # Remove the complete one-cofactor head before either boundary is sampled.
 return (-ell*(arb_series(ww,prec=size)*B)).coeffs(), (ell*arb_series(head,prec=size)).coeffs(), gap

def cutoff_tail(size,gap,ell,cap):
 # Lattice compositions i_1+...+i_k=size, each i_j>=ell;
 # |tilted g_i|<=7/i. Includes all subset signs in a norm bound
 # ONLY for the omitted count classes of this numerical model.
 d=arb(size)-ell*gap
 if d<=0:return arb(0)
 ans=arb(0)
 for k in range(cap+1,size//ell+1):
  count=fmpz.bin_uiui(size-k*ell+k-1,k-1)
  ans+=d*(arb(14)/ell)**k*arb(count)/arb.fac_ui(k)
 return ans

def task(ij):
 it,face,ir=ij;T,wt=TS[it];r,rw=RS[face][ir];h=HS[face];cap=54 if face==0 else 12
 size=math.ceil(float(arb('0.5')/r)*ELL)+10
 vals,heads,gap=tables(T,r,ELL,size,L)
 total=arb(0);tail=arb(0);largest=0.

 for ip,(p,pw) in enumerate(PS):
  if 1-p<=r:continue
  conditional=CONDITIONALS[face][ir][ip]*CORRECTIONS[face][ip]
  stencil=STENCILS[face][ir][ip]
  response=sum(c*(vals[j]-heads[j]) for j,c in stencil)*(T*(1-p)/40000).exp()
  response+=(1+6*(T*(1-p)/40000).exp()*(3*T*(1-p)/500).cos())*(L/T-p)/(1-p)
  owner=1+6*(T*p/40000).exp()*(3*T*p/500).cos()
  integ=conditional*owner*response/(p*(L/T))
  total+=pw*integ
  largest=max(largest,float(abs(integ).upper()))
  # Bound omitted count contributions at every interpolation node.
  localtail=arb(0)
  for j,c in stencil:
   if j < (cap+1)*ELL:continue
   localtail+=abs(c)*cutoff_tail(j,gap,ELL,cap)
  tail+=abs(pw*conditional*owner/(p*(L/T)))*(T*(1-p)/40000).exp()*localtail
 return it,face,ir,str(total),str(tail),largest

def run(n,ell,tn,rn,pn,bits=384,workers=8):
 global N,ELL,L,HS,TS,RS,PS,CONDITIONALS,CORRECTIONS,STENCILS
 start=time.monotonic();N=n;ELL=ell;ctx.prec=bits;ctx.threads=1
 u=arb(10001)/20000
 # Exact integer cutoff; never convert its enormous integer to a string.
 X=(fmpz(20000)**n)//((fmpz(10001)**n)*(n+1))+2
 L=2*arb(X).log()
 factorial=arb.fac_ui(n)
 TS=[]
 for t,w in legendre(tn,arb(39)*n/20,arb(203)*n/100):
  logpdf=(n+1)*u.log()-u*t+n*t.log()-factorial.log()
  TS.append((t,w*logpdf.exp()))
 HS=[(n+99)//100-2,n//25-1]
 RS=[beta_rule(h+1,n-h+1,rn) for h in HS]
 PS=legendre(pn,arb(1)/2,arb(3)/5)
 jlo=(21*N+39)//40;jhi=23*N//40
 marginals=[binomial_tail(p,N+1,jlo)-binomial_tail(p,N+1,jhi+1) for p,w in PS]
 CONDITIONALS=[];CORRECTIONS=[];STENCILS=[];marginal_errors=[]
 for f,h in enumerate(HS):
  conditional=[[binomial_tail(p/(1-r),N-h,jlo)-binomial_tail(p/(1-r),N-h,jhi+1) for p,pw in PS] for r,rw in RS[f]]
  observed=[sum(rw*conditional[ir][ip] for ir,(r,rw) in enumerate(RS[f])) for ip in range(pn)]
  correction=[m/v if v>arb(2)**(-180) else arb(1) for m,v in zip(marginals,observed)]
  CONDITIONALS.append(conditional);CORRECTIONS.append(correction)
  marginal_errors.append(str(max(abs(v-m) for v,m in zip(observed,marginals))))
  stencils=[]
  for r,rw in RS[f]:
   row=[]
   for p,pw in PS:
    index=(1-p)/r*ELL;base=math.floor(float(index));frac=index-base
    assert arb(base)<=index and index<base+1
    weights=[]
    for j in range(-5,7):
     c=arb(1)
     for k in range(-5,7):
      if k!=j:c*=(frac-k)/(j-k)
     weights.append((base+j,c))
    assert sum(c for j,c in weights).contains(1)
    row.append(weights)
   stencils.append(row)
  STENCILS.append(stencils)
 print('rules',n,ell,tn,rn,pn,'sec',time.monotonic()-start,flush=True)
 fronts=[arb(0),arb(0)];tails=[arb(0),arb(0)];maxima=[0.,0.]
 count=0;total=tn*rn*2
 tasks=[(it,f,ir) for it in range(tn) for f in range(2) for ir in range(rn)]
 with ProcessPoolExecutor(max_workers=workers,mp_context=multiprocessing.get_context('fork')) as pool:
  for it,f,ir,val,tail,maximum in pool.map(task,tasks,chunksize=1):
   w=TS[it][1]*RS[f][ir][1]
   fronts[f]+=w*arb(val);tails[f]+=abs(w)*arb(tail);maxima[f]=max(maxima[f],maximum)
   count+=1
   if count%16==0:print('progress',count,total,'sec',time.monotonic()-start,flush=True)
 result=fronts[0]-fronts[1]
 out=dict(N=n,ell=ell,tn=tn,rn=rn,pn=pn,bits=bits,fronts=[str(v) for v in fronts],
          joined=str(result),omitted_count_bound=[str(v) for v in tails],max_integrand=maxima,
          radial_mass=str(sum(w for t,w in TS)),
          owner_marginal_error_before_calibration=marginal_errors,seconds=time.monotonic()-start,
          scope='Finite ball-arithmetic lattice/quadrature only, with exact moving length, owner-marginal calibration and analytic head replacement. No bound for grid/interpolation/quadrature errors or arithmetic transport.')
 print(json.dumps(out),flush=True)
 return out
if __name__=='__main__':
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--order',type=int,default=65536)
 parser.add_argument('--grid',type=int,default=512)
 parser.add_argument('--tnodes',type=int,default=48)
 parser.add_argument('--rnodes',type=int,default=8)
 parser.add_argument('--pnodes',type=int,default=256)
 parser.add_argument('--bits',type=int,default=384)
 parser.add_argument('--workers',type=int,default=4)
 parser.add_argument('--output',type=Path,required=True)
 a=parser.parse_args()
 if a.order<10000 or a.grid<32 or min(a.tnodes,a.rnodes,a.pnodes)<2 or a.bits<256 or a.workers<1:
  parser.error('require N>=10000, grid>=32, at least two nodes per axis, bits>=256 and workers>=1')
 out=run(a.order,a.grid,a.tnodes,a.rnodes,a.pnodes,a.bits,a.workers)
 out['proof_status']='No continuum enclosure, retained prime-sum bound, or eventual conclusion'
 out['probe_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
 out['versions']={name:importlib.metadata.version(name) for name in ('python-flint','numpy','scipy')}
 out['parameters']={'u':'10001/20000','modes':['0','1/40000+(3/500)i','1/40000-(3/500)i'],
                    'multiplicities':[1,3,3],'owner_interval':['1/2','3/5'],
                    'radial_interval':['39N/20','203N/100'],
                    'length':'2*log(floor(20000^N/(10001^N*(N+1)))+2)',
                    'literal_count_caps_in_model':[55,13]}
 a.output.parent.mkdir(parents=True,exist_ok=True)
 a.output.write_text(json.dumps(out,indent=2)+'\n')
