import runpy
from math import gcd
from pathlib import Path
s=runpy.run_path(str(Path(__file__).resolve().parents[2] / 'semiprime-twist-character-20261022/probes/check_formulas.py'))

def mul(x,y,N):return s['fp_mul'](x,y,N,-1)
def inv(x,N):
 n=(x[0]*x[0]+x[1]*x[1])%N
 assert gcd(n,N)==1
 return (x[0]*pow(n,-1,N)%N,-x[1]*pow(n,-1,N)%N)
def divide(x,y,N):return mul(x,inv(y,N),N)
def add(x,y,N):return ((x[0]+y[0])%N,(x[1]+y[1])%N)
count=0
for p,q in ((7,23),(47,59),(59,83)):
 N=p*q;g=4;u=pow(g,7,N);step=pow(g,5,N);L=9;nu=5
 xs=[pow(g,e,N) for e in (2,9,15)]
 ys=[u*pow(step,i,N)%N for i in range(L)]
 B=None
 for k in range(nu):
  a=u*pow(step,k,N)%N
  Bs=(1,0)
  for y in ys:Bs=mul(Bs,(y,a),N)
  if k==0:B=Bs
  else:
   B=mul(B,(pow(step,L,N),0),N)
   B=mul(B,(pow(step,-k,N),1),N)
   B=divide(B,(pow(step,L-k,N),1),N)
   assert B==Bs
  for x in xs:
   for y in ys:
    assert gcd(x*x+a*a,N)==gcd(y*y+a*a,N)==1
    wx=divide((x,a),(x,-a),N);wy=divide((y,a),(y,-a),N)
    diff=((wx[0]-wy[0])%N,(wx[1]-wy[1])%N)
    sym=s['quartic'](diff,(N,0))
    if gcd(x-y,N)>1:assert sym is None
    else:
     j2=0 if s['quartic']((0,1),(N,0))==0 else 2
     pred=(j2+s['quartic']((x,a),(N,0))+s['quartic']((y,a),(N,0)))%4
     assert sym==pred
    count+=1
print({'nonlinear_palette_leaf_checks':count,'seed_product_updates':3*(nu-1)})
