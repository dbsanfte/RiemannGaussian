"""One fixed exact AP identity diagnostic; no search/coverage campaign."""
from math import gcd, isqrt
import json

r, P, Q, beta = 37, 50147, 50459, 4
N, H, M = P * Q, r**2, r**4
Bcap, dp, dq = 16*r*r, 25073, 25229

def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))

assert all(prime(x) for x in (P,Q,dp,dq))
assert P == 2*dp+1 and Q == 2*dq+1
assert pow(beta,dp,P) == pow(beta,dq,Q) == 1
assert beta % P != 1 and beta % Q != 1
assert min(dp,dq) > Bcap and gcd(dp,dq) == 1
assert dp*dq > 256*r**4 and N <= r**6 and max(P,Q) <= 2*r**3
assert gcd(dp*dq, N*(N*N-1)) == 1
rows = []
for t in range(r):
    s = 1+r*t
    C = s*s*pow(N,-1,H) % H
    X = C*N-1
    bb = (-2-X+X*X*pow(4,-1,M)-X**3*pow(8,-1,M)) % M
    if bb > M//2:
        bb -= M
    assert (-bb*pow(2,-1,H)) % H == s
    assert (s*s+bb*s+C*N) % M == 0
    rows.append((s,bb,C))
a, b = -5*r, 5*r
leaf_count = r*(r-1)*(b-a+1)
assert 2*N > 11*r**5  # all actual integer exponents K are positive

def trace(k):
    base = pow(beta,k,N)
    seeds = sum(pow(base,-M*sigma,N) for sigma in range(a,b+1)) % N
    return seeds*sum(pow(base,C*N,N)*sum(pow(base,c*c+bb*c,N)
               for c in range(1,r)) for s,bb,C in rows) % N

indices = {'1':1,'N-1':N-1,'N':N,'N+1':N+1,
           '(N-1)^2':(N-1)**2,'N^2':N*N,'N^2-1':N*N-1}
traces = {name:trace(k) for name,k in indices.items()}
result = {'parameters': {'r':r,'P':P,'Q':Q,'N':N,'beta':beta,
          'dP':dp,'dQ':dq,'B':Bcap,'global_order':dp*dq,
          'leaf_count':leaf_count,'public_zero_count':0},
          'traces': {name: {'value':traces[name],
                     'gcd':gcd(traces[name],N),
                     'gcd_minus_leaf_count':gcd(traces[name]-leaf_count,N),
                     'gcd_beta_index_minus_one':gcd(pow(beta,k,N)-1,N)}
                     for name,k in indices.items()}}
defects = {'S_N-S_1':traces['N']-traces['1'],
           'S_N-S_1^N':traces['N']-pow(traces['1'],N,N),
           'S_(N-1)-S_0':traces['N-1']-leaf_count,
           'S_(N+1)-S_2':traces['N+1']-trace(2)}
result['defects'] = {name:{'residue':value % N,'gcd':gcd(value,N)}
                     for name,value in defects.items()}
witnesses = []
for local, other in [(P,Q),(Q,P)]:
    c = pow(local,-1,r)
    s = c*local % H
    _,bb,C = next(row for row in rows if row[0] == s)
    numerator = c*c*local+bb*c+C*other
    assert numerator % M == 0
    sigma = numerator//M
    K = C*N+c*c+bb*c-M*sigma
    assert a <= sigma <= b and K == (local-1)*(C*other-c*c) != 0
    assert pow(beta,K,local) == 1
    witnesses.append({'local_prime_for_verification':local,'s':s,'c':c,
                      'sigma':sigma,'K':K})
result['covered_witnesses'] = witnesses
SP, SQ = trace(P), trace(Q)
assert (SP-traces['1']) % P == (SQ-traces['1']) % Q == 0
assert (traces['N']-SQ) % P == (traces['N']-SP) % Q == 0
result['forced_frobenius_relations'] = 'pass'
print(json.dumps(result,indent=2))
