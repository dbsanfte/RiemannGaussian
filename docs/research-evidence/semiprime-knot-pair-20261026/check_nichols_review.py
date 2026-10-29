import sympy as s
a,b=s.symbols('a b',nonzero=True); A=1-a; B=1-b; E=A+B
R=s.zeros(16)
def add(i,j,terms):
 for k,l,c in terms:R[4*k+l,4*i+j]+=c
add(0,0,[(0,0,1)]);add(0,1,[(0,1,A),(1,0,a)]);add(0,2,[(0,2,B),(2,0,b)])
add(0,3,[(0,3,E),(1,2,-A*B),(2,1,-b*A*B),(3,0,a*b)])
for i,j,k,l,c in [(1,0,0,1,1),(1,1,1,1,-a),(2,0,0,2,1),(2,2,2,2,-b),(3,0,0,3,1),(3,1,1,3,1/b),(3,2,2,3,b),(3,3,3,3,1)]:add(i,j,[(k,l,c)])
add(1,2,[(0,3,1),(2,1,-b)]);add(1,3,[(1,3,A),(3,1,a*b)]);add(2,1,[(0,3,1/b),(1,2,-1/b)]);add(2,3,[(2,3,B),(3,2,1)])
def clean(M):return M.applyfunc(s.cancel)
def rotate(M):
 T=s.zeros(16)
 for i in range(4):
  for j in range(4):
   for k in range(4):
    for l in range(4):T[4*l+j,4*k+i]=M[4*k+l,4*i+j]
 return T
def pt(M):return clean(s.Matrix(4,4,lambda k,i:sum([1,-1,-1,1][j]*M[4*k+j,4*i+j] for j in range(4))))
Ri=clean(R.inv());T=rotate(R);U=rotate(Ri)
y=s.symbols('y:16'); Y=s.Matrix(y)
def p(i,j):return y[4*i+j]
x=s.zeros(16,1)
def put(i,j,v):x[4*i+j]=v
def get(i,j):return x[4*i+j]
put(0,0,p(0,0));put(1,1,(A*p(0,0)-p(1,1))/a);put(2,2,(B*p(0,0)-p(2,2))/b);put(3,3,p(3,3)-E*p(0,0)-A*get(1,1)-B*get(2,2))
put(0,1,p(1,0));put(1,0,p(0,1)/a);put(2,3,(p(3,2)-p(1,0))/b);put(3,2,p(2,3)+A*B*p(0,1)/a)
put(0,2,p(2,0));put(2,0,p(0,2)/b);put(1,3,b*p(3,1)-p(2,0));put(3,1,(p(1,3)+A*B*p(0,2))/(a*b))
put(3,0,p(0,3)/(a*b));put(0,3,p(3,0));put(2,1,-p(1,2)/b);put(1,2,-b*p(2,1))
assert clean(T*x-Y)==s.zeros(16,1)
x=s.zeros(16,1);C=(2*A*B-E)/(a*b)
put(3,3,p(3,3));put(1,1,-a*p(1,1)-A*p(3,3));put(2,2,-b*p(2,2)-B*p(3,3));put(0,0,p(0,0)+A*get(1,1)/a+B*get(2,2)/b-C*p(3,3))
put(2,3,p(3,2));put(3,2,b*p(2,3));put(1,0,p(0,1)-p(2,3));put(0,1,a*p(1,0)+A*B*p(3,2))
put(1,3,a*b*p(3,1));put(3,1,p(1,3)/b);put(2,0,p(0,2)-p(1,3)/b);put(0,2,b*p(2,0)+b*A*B*p(3,1))
put(3,0,p(0,3));put(0,3,a*b*p(3,0));put(2,1,-p(1,2)/b);put(1,2,-b*p(2,1))
assert clean(U*x-Y)==s.zeros(16,1)
assert s.factor(R.det())==(a*b)**4
assert s.factor(T.det())==(a*b)**4
assert s.factor(U.det())==(a*b)**-4
assert pt(R)==s.eye(4);assert pt(Ri)==s.eye(4)
J=1-(a+b)*A*B
assert clean(pt(R**3)-J*s.eye(4))==s.zeros(4)
K=lambda t:t+1/t-1
assert s.cancel(J-a*b*(K(a)*K(b)+1-a*b))==0
print('PASS: determinants R,T,U; both printed rotated inverse solves; enhancement partial traces; full trefoil scalar and correction.')
print('Mirror scalar:', s.factor(pt(Ri**3)[0,0]))
assert clean(pt(Ri**3)-J.subs({a:1/a,b:1/b},simultaneous=True)*s.eye(4))==s.zeros(4)
print('PASS: negative trefoil is J(a^-1,b^-1).')
