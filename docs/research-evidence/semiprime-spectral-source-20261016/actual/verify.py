"""Exact finite certificate; stdlib only. No random choices or primality oracle."""
import math,json,pathlib,hashlib
base=pathlib.Path(__file__).parent
m=43;P=69263;Q=70163;N=P*Q;d=m*m;L=2*d+2
RP=(P-1)//2;RQ=(Q-1)//2
# Exhaustive divisibility is a proof for these small integers.
def prime(p):return p>1 and all(p%v for v in range(2,math.isqrt(p)+1))
assert all(prime(p) for p in [m,P,Q,RP,RQ])
assert all(not prime(v) for v in range(42,43)) and prime(41)
assert 41**6<N<=42**6 and N<=m**6
assert 2*Q<=3*P and P>0 and Q>0
assert RP!=RQ and (P-1)%RQ and (Q-1)%RP
assert RP>16*d and RQ>16*d
assert RP**1000>P**677 and RQ**1000>Q**677
assert math.gcd(m*m,N*(P-1)*(Q-1))==1
ell=(N+1-1).bit_length() # ceil(log2(N+1)); N+1 is not a power of two.
assert 2**(ell-1)<N+1<=2**ell
projection_exponent=pow(math.factorial(m),ell)
gamma=pow(pow(2,N-1,N),projection_exponent,N)
assert gamma==3896048378
for p,r in [(P,RP),(Q,RQ)]:
 assert pow(gamma,r,p)==1 and gamma%p!=1 # r prime => exact order r
D=RP*RQ
assert D>16*m**4 and D>8*m*m
q=pow(gamma,d,N)
offsets=[]
for j in range(1,m):
 inv=pow(j,-1,m);a=N*inv*inv%m
 assert 1<=a<m and (N-a*j*j)%m==0
 div=(N-a*j*j)//m;b=(-inv*div+m//2)%m-m//2
 assert (div+j*b)%m==0
 delta=a+m*b-2*a*j
 assert -3*d<=delta<=d
 offsets.append(delta)
us=sorted(set(offsets));J=len(us);T=(L+1)//J
assert J==42 and T==88
zs=[pow(gamma,-N-v,N) for v in us]
assert len(set(zs))==J
assert all(math.gcd(zs[i]-zs[j],N)==1 for i in range(J) for j in range(i))
# Monic H is acquired exactly by multiplication of its linear factors over Z/N.
H=[1]
for z in zs:
 new=[0]*(len(H)+1)
 for k,c in enumerate(H):new[k]=(new[k]-z*c)%N;new[k+1]=(new[k+1]+c)%N
 H=new
assert H[-1]==1
phi=[]
a=pow(q,L,N)
for n in range(T):
 X=pow(q,J*n,N);A=[(1-X*pow(q,s,N))%N for s in range(J)];B=[(a-X*pow(q,s,N))%N for s in range(J)]
 pref=[1];suff=[1]*(J+1)
 for v in A:pref.append(pref[-1]*v%N)
 for s in range(J-1,-1,-1):suff[s]=suff[s+1]*B[s]%N
 value=sum(H[k]*pref[k]*suff[k] for k in range(J+1))%N
 assert math.gcd(value,N)==1
 phi.append(value)
delta=sum(H[k]*pow(a,J-k,N) for k in range(J+1))%N
assert math.gcd(delta,N)==1
hits={};own={}
for p,other,r in [(P,Q,RP),(Q,P,RQ)]:
 table={pow(q,i,p):i for i in range(L)}
 assert len(table)==L
 hs=[]
 for j,off in enumerate(offsets,1):
  row=pow(gamma,N+off,p)
  if row in table:hs.append([j,table[row]])
 j=p%m;inv=pow(j,-1,m);slope=N*inv*inv%m;off=offsets[j-1];lin=off-slope
 assert (slope*p+other+lin)%d==0
 i=(slope*p+other+lin)//d
 assert 0<=i<L and [j,i] in hs
 hits[str(p)]=hs;own[str(p)]={'tag':j,'index':i,'slope':slope}
assert hits[str(P)] and hits[str(Q)] # full norm zero in BOTH fields
result={'m':m,'P':P,'Q':Q,'N':N,'RP':RP,'RQ':RQ,'global_order':D,'sixth_width':42,'gamma':gamma,'projection_log_exponent':ell,'q':q,'L':L,'J':J,'T':T,'offsets':offsets,'deduplicated_offsets':us,'H_coefficients_mod_N':H,'delta_phi0_mod_N':delta,'phi_qJn_mod_N':phi,'field_hits':hits,'own_witnesses':own}
(base/'certificate.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['m','P','Q','N','RP','RQ','global_order','gamma','q','L','J','T','delta_phi0_mod_N','field_hits','own_witnesses']},indent=2))
print('PASS: all scheduled scalar spectral values are units, while full collision norm is zero modulo N.')
