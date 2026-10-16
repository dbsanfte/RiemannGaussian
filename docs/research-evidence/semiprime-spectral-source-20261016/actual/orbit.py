import json,pathlib
base=pathlib.Path(__file__).parent;c=json.loads((base/'certificate.json').read_text());N=c['N'];q=c['q'];L=c['L'];H=c['H_coefficients_mod_N'];J=c['J']
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b,p):return trim([((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0))%p for i in range(max(len(a),len(b)))])
def neg(a,p):return [(-v)%p for v in a]
def mul(a,b,p):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%p
 return trim(z)
def divmodp(a,b,p):
 a=trim(a[:]);b=trim(b[:]);assert b!=[0];iv=pow(b[-1],-1,p);out=[0]*max(1,len(a)-len(b)+1)
 while a!=[0] and len(a)>=len(b):
  k=len(a)-len(b);v=a[-1]*iv%p;out[k]=v
  for i,x in enumerate(b):a[k+i]=(a[k+i]-v*x)%p
  trim(a)
 return trim(out),a
def rem(a,b,p):return divmodp(a,b,p)[1]
def power(a,n,b,p):
 z=[1]
 while n:
  if n&1:z=rem(mul(z,a,p),b,p)
  a=rem(mul(a,a,p),b,p);n//=2
 return z
def xgcd(a,b,p):
 r0,r1=a,b;s0,s1=[1],[0];t0,t1=[0],[1]
 while r1!=[0]:
  z,r=divmodp(r0,r1,p);r0,r1=r1,r;s0,s1=s1,add(s0,neg(mul(z,s1,p),p),p);t0,t1=t1,add(t0,neg(mul(z,t1,p),p),p)
 iv=pow(r0[-1],-1,p)
 return [x*iv%p for x in r0],[x*iv%p for x in s0],[x*iv%p for x in t0]
def determinant(a,p):
 a=[row[:] for row in a];value=1
 for k in range(len(a)):
  pivot=next((i for i in range(k,len(a)) if a[i][k]%p),None)
  if pivot is None:return 0
  if pivot!=k:a[k],a[pivot]=a[pivot],a[k];value=-value
  v=a[k][k]%p;value=value*v%p;iv=pow(v,-1,p)
  for i in range(k+1,len(a)):
   factor=a[i][k]*iv%p
   for j in range(k+1,len(a)):a[i][j]=(a[i][j]-factor*a[k][j])%p
   a[i][k]=0
 return value%p
def evalpoly(a,x,p):
 z=0
 for v in reversed(a):z=(z*x+v)%p
 return z
out={}
for p,R in [(c['P'],c['RP']),(c['Q'],c['RQ'])]:
 a=pow(q,L,p);phi=[0]
 for k,h in enumerate(H):
  term=[h%p]
  for s in range(J):term=mul(term,[1 if s<k else a,-pow(q,s,p)%p],p)
  phi=add(phi,term,p)
 # Independently construct the ACTUAL coefficient companion and pencil.
 # Equality at J+1 distinct points certifies the entire degree<=J polynomial.
 companion=[[0]*J for _ in range(J)]
 for i in range(J-1):companion[i][i+1]=1
 companion[-1]=[-H[j]%p for j in range(J)]
 for X in range(J+1):
  matrix=[[( (1-X*pow(q,i,p))*(i==j)+(X*pow(q,i,p)-a)*companion[i][j])%p for j in range(J)] for i in range(J)]
  assert determinant(matrix,p)==evalpoly(phi,X,p)
 r=add(power([0,1],R,phi,p),[-1],p)
 gcd,A,B=xgcd(phi,r,p)
 print(p,'degree',len(phi)-1,'orbit gcd',gcd)
 assert gcd==[1]
 assert add(mul(A,phi,p),mul(B,r,p),p)==gcd
 out[str(p)]={'order':R,'direct_pencil_determinant_points_verified':list(range(J+1)),'phi':phi,'X_power_order_minus_one_remainder':r,'gcd':gcd,'bezout_phi':A,'bezout_remainder':B}
(base/'orbit-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
