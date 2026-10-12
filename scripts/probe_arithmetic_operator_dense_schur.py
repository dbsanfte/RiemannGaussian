#!/usr/bin/env python3
"""Exact grid algebra and floating actual-prime diagnostics; never proof input."""
import argparse,cmath,json,math
from fractions import Fraction as F
from pathlib import Path
from probe_arithmetic_operator_growing_schur import primes_to

def phase(y,n): return cmath.exp(-1j*y*math.log(n))
def mu_div_sum(y,n,m):
 g=math.gcd(n,m); out=0j; d=1
 while d*d<=g:
  if g%d==0:
   for k in ([d] if d*d==g else [d,g//d]):
    a=k; mu=1; z=2
    while z*z<=a:
     if a%z==0:
      a//=z;mu=-mu
      if a%z==0:mu=0;break
      while a%z==0:a//=z
     z+=1
    if a>1:mu=-mu
    out+=mu*phase(y,k)
  d+=1
 return out*(2 if n==m else 1)

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--output',required=True);args=parser.parse_args()
 primes=primes_to(250000); cases=[]; native=0; integer_gcd=0; comparisons=0
 for y in [1,54,-54,65,100]:
  J=max(0,int((abs(y)*math.log(150000)-(math.pi/2-1/4))/(2*math.pi)))
  x=math.exp((2*math.pi*J+math.pi/2-1/4)/abs(y)); A=math.exp(1/(16*abs(y)))
  P=[p for p in primes if x<p<=A*x][:5];Q=[q for q in primes if A*x<q<=A*A*x][:5]
  if not P or not Q:continue
  rows=[(p,q) for p in P for q in Q]; X=math.floor(A**3*x*x)
  a=[complex((i*7)%11-5,(i*13)%9-4) for i in range(len(rows))]
  D=[1-phase(y,p)-phase(y,q)+2*phase(y,p)*phase(y,q) for p,q in rows]
  assert max(d.real for d in D)<=-9/8+1e-12
  assert len({p*q for p,q in rows})==len(rows) and all(p*q<=X for p,q in rows)
  literal_matrix=[[mu_div_sum(y,p*q,r*s) for r,s in rows] for p,q in rows]
  for i,(p,q) in enumerate(rows):
   for j,(r,s) in enumerate(rows):
    assert math.gcd(p*q,r*s)==(p if p==r else 1)*(q if q==s else 1)
    integer_gcd+=1
    formula=1-(phase(y,p) if p==r else 0)-(phase(y,q) if q==s else 0)+(D[i] if i==j else 0)
    literal=literal_matrix[i][j]
    assert abs(formula-literal)<2e-12;native+=1
  for mode in ['constant','identity','real_gram','complex_gram']:
   def K(i,j):
    if mode=='constant':return 1
    if mode=='identity':return int(i==j)
    if mode=='real_gram':return sum((1 if (i+f)%3==0 else -1)*(1 if (j+f)%3==0 else -1) for f in range(3))/3
    return cmath.exp(1j*((i%7)-(j%7))/7)
   damped=sum(a[i]*a[j].conjugate()*K(i,j)*literal_matrix[i][j] for i in range(len(rows)) for j in range(len(rows)))
   free=sum(a[i]*a[j].conjugate()*K(i,j) for i in range(len(rows)) for j in range(len(rows)))
   bound=free.real-9/8*sum(abs(v)**2 for v in a)
   assert damped.real<=bound+1e-8;comparisons+=1
  cases.append({'height':y,'J':J,'selectedP':len(P),'selectedQ':len(Q),'nativeCutoff':X,'maximumDiagonalRemainderReal':max(d.real for d in D),'proofInput':False})
 # Rational complex algebra, with no actual phase or Gamma compatibility granted.
 rational=0
 for p in range(4):
  for q in range(4):
   for r in range(4):
    for s in range(4):
     # Constant exact Pythagorean phase c-i*v.
     c=F(7,25);v=F(24,25);dre=1-2*c+2*(c*c-v*v)
     native_re= (2 if p==r and q==s else 1)*(1-(c if p==r else 0)-(c if q==s else 0)+((c*c-v*v) if p==r and q==s else 0))
     joined_re=1-(c if p==r else 0)-(c if q==s else 0)+(dre if p==r and q==s else 0)
     assert native_re==joined_re and dre<=-F(9,8);rational+=1
 report={'scope':'dense actual semiprime grid; Hermitian PSD Schur trace obstruction','checksPassed':True,'proofInput':False,'exactNativeIntegerGcdChecks':integer_gcd,'exactRationalGridIdentities':rational,'rationalSurrogateGrantedPrimeGammaCompatibility':False,'floatingDiagnosticOnly':{'nativeComplexGridEntries':native,'coupledQuadraticBounds':comparisons,'cases':cases},'hypotheticalNonlinearZeroSourceInferred':False,'newRHClaimed':False}
 Path(args.output).write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k!='floatingDiagnosticOnly'}))
if __name__=='__main__':main()
