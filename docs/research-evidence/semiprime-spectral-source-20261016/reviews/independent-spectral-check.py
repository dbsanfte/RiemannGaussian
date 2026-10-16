from pathlib import Path
import json,math,hashlib
p=Path(__file__).resolve().parents[1]/'actual'
c=json.loads((p/'certificate.json').read_text());oc=json.loads((p/'orbit-certificate.json').read_text());sc=json.loads((p/'scalar-certificate.json').read_text());m=43;P=69263;Q=70163;N=P*Q;d=m*m;L=2*d+2
assert N==4859699869
def prime(n):return n>=2 and all(n%k for k in range(2,math.isqrt(n)+1))
for n in [m,P,Q,34631,35081]:assert prime(n)
assert 41**6<N<=42**6<43**6 and not any(prime(k) for k in range(42,43))
assert 1**50<=42<2**50
for a,r,other in [(P,34631,Q),(Q,35081,P)]:
 assert a-1==2*r and r>16*d and r**1000>a**677 and (other-1)%r
 for n in [a,a-1]:assert math.gcd(n,d)==1
assert 2*max(P,Q)<3*min(P,Q) and 41**3<min(P,Q)<max(P,Q)<43**3
ell=(N).bit_length();assert ell==33
base=pow(2,N-1,N);gamma=pow(base,math.factorial(m)**ell,N);q=pow(gamma,d,N)
assert gamma==c['gamma']==3896048378 and q==c['q']==1007400003
for a,r in [(P,34631),(Q,35081)]:assert pow(gamma,r,a)==1 and gamma%a!=1 and pow(q,r,a)==1 and q%a!=1
D=34631*35081;assert D==1214890111 and D>16*m**4
rows=[]
for j in range(1,m):
 I=pow(j,-1,m);a=N*I*I%m;assert 1<=a<m
 D0,rem=divmod(N-a*j*j,m);assert rem==0
 b=(-I*D0+m//2)%m-m//2
 c0,rem=divmod(D0+j*b,m);assert rem==0
 delta=a+m*b-2*a*j;assert -3*d<=delta<=d
 rows.append((j,a,b,c0,delta))
assert [t[4] for t in rows]==c['offsets'];offsets=sorted(t[4] for t in rows);assert len(set(offsets))==42 and offsets==c['deduplicated_offsets']
z=[pow(gamma,-N-x,N) for x in offsets]
for i in range(len(z)):
 for j in range(i):assert math.gcd(z[i]-z[j],N)==1

def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a

def add(a,b,p):
 out=[0]*max(len(a),len(b))
 for i,x in enumerate(a):out[i]+=x
 for i,x in enumerate(b):out[i]+=x
 return trim([x%p for x in out])

def mul(a,b,p):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]=(out[i+j]+x*y)%p
 return trim(out)

def rem(a,b,p):
 a=trim([x%p for x in a]);ib=pow(b[-1],-1,p)
 while len(a)>=len(b) and a!=[0]:
  s=len(a)-len(b);v=a[-1]*ib%p
  for i,x in enumerate(b):a[s+i]=(a[s+i]-v*x)%p
  trim(a)
 return a

def powx(n,f,p):
 a=[1];x=rem([0,1],f,p)
 while n:
  if n&1:a=rem(mul(a,x,p),f,p)
  x=rem(mul(x,x,p),f,p);n//=2
 return a

def ev(a,x,p):
 v=0
 for t in reversed(a):v=(v*x+t)%p
 return v
H=[1]
for x in z:H=mul(H,[-x%N,1],N)
assert H==c['H_coefficients_mod_N'];J=42;aq=pow(q,L,N)
pre=[[1]]
for s in range(J):pre.append(mul(pre[-1],[1,-pow(q,s,N)%N],N))
suf=[[1] for _ in range(J+1)]
for s in reversed(range(J)):suf[s]=mul([aq,-pow(q,s,N)%N],suf[s+1],N)
phi=[0]
for k,h in enumerate(H):phi=add(phi,[h*x%N for x in mul(pre[k],suf[k],N)],N)
assert phi[0]==c['delta_phi0_mod_N']==4699488932 and math.gcd(phi[0],N)==1
assert L//J==88 and [ev(phi,pow(q,J*n,N),N) for n in range(88)]==c['phi_qJn_mod_N']

def det(a,p):
 a=[row[:] for row in a];ans=1
 for k in range(len(a)):
  s=next((i for i in range(k,len(a)) if a[i][k]%p),None)
  if s is None:return 0
  if s!=k:a[k],a[s]=a[s],a[k];ans=-ans
  piv=a[k][k]%p;ans=ans*piv%p;inv=pow(piv,-1,p)
  for i in range(k+1,len(a)):
   rat=a[i][k]*inv%p
   for j in range(k+1,len(a)):a[i][j]=(a[i][j]-rat*a[k][j])%p
 return ans%p
for p0,R in [(P,34631),(Q,35081)]:
 o=oc[str(p0)];f=[x%p0 for x in phi];assert f==o['phi'] and len(f)==43
 rr=add(powx(R,f,p0),[-1],p0);assert rr==o['X_power_order_minus_one_remainder']
 assert add(mul(o['bezout_phi'],f,p0),mul(o['bezout_remainder'],rr,p0),p0)==[1]
 aa,bb=f,rr
 while bb!=[0]:aa,bb=bb,rem(aa,bb,p0)
 assert len(aa)==1 and aa[0]!=0
 M=[[0]*J for _ in range(J)]
 for i in range(J-1):M[i][i+1]=1
 M[-1]=[-x%p0 for x in H[:-1]]
 for X in range(J+1):
  A=[[(int(i==j)-aq*M[i][j]-X*pow(q,i,p0)*(int(i==j)-M[i][j]))%p0 for j in range(J)] for i in range(J)]
  assert det(A,p0)==ev(f,X,p0)
 # independent Frobenius all-scalar gcd check
 fr=add(powx(p0,f,p0),[0,-1],p0)
 so=sc[str(p0)];assert so['field_prime']==p0 and so['phi']==f
 assert so['X_power_p_minus_X_remainder']==fr and so['gcd']==[1]
 assert add(mul(so['bezout_phi'],f,p0),mul(so['bezout_remainder'],fr,p0),p0)==[1]
 aa,bb=f,fr
 while bb!=[0]:aa,bb=bb,rem(aa,bb,p0)
 assert len(aa)==1 and aa[0]!=0
 # independent local orbit map for all canonical collisions
 table={pow(q,i,p0):i for i in range(R)};hits=[]
 for j,a,b,cc,delta in rows:
  v=pow(gamma,N+delta,p0);i=table[v]
  if i<L:hits.append([j,i])
 expected=c['field_hits'][str(p0)] if 'field_hits' in c else None
 print('field',p0,'hits',hits,'Bezout+all43pencilpoints PASS')
 assert hits==([[6,281],[13,2023],[33,1535],[39,186]] if p0==P else [[6,2162],[8,208],[16,2674],[17,2086],[30,568],[36,2522],[39,1212]])
 own=next(t for t in rows if t[0]==p0%m);j,a,b,cc,delta=own;other=N//p0
 num=a*p0+other+m*b-2*a*j;assert num%d==0
 i=num//d;assert (i,a)==((1535,40) if p0==P else (568,14))
 assert 0<=i<L and pow(gamma,N+delta,p0)==pow(q,i,p0)
print('independent reconstruction PASS',{'gamma':gamma,'q':q,'J':J,'T':88,'phi0':phi[0]})
