"""Exact polynomial certificate; no residue sampling or knot numerical campaign."""
f = [1, 0, 0, -3, 0, 0, 1]  # ascending coefficients
G = [0] * 17
for e, c in [(16,1),(13,-3),(11,-3),(10,2),(8,7),(6,2),(5,-3),(3,-3),(0,1)]:
    G[e] += c
r = G[:]
while len(r) > 6:
    c, d = r[-1], len(r)-7
    for j, a in enumerate(f):
        r[d+j] -= c*a
    r.pop()
assert r == [-1,-3,2,3,8,-6]
a, b = f[::-1], r[::-1]
m, n = len(a)-1, len(b)-1
A = [[0]*i+a+[0]*(n-1-i) for i in range(n)]
A += [[0]*i+b+[0]*(m-1-i) for i in range(m)]
prev, sign = 1, 1
for k in range(m+n-1):
    if not A[k][k]:
        j = next(j for j in range(k+1,m+n) if A[j][k])
        A[k], A[j] = A[j], A[k]
        sign = -sign
    pivot = A[k][k]
    for i in range(k+1,m+n):
        for j in range(k+1,m+n):
            v = A[i][j]*pivot-A[i][k]*A[k][j]
            assert v % prev == 0
            A[i][j] = v // prev
        A[i][k] = 0
    prev = pivot
resultant = sign*A[-1][-1]
assert resultant == 25
print('g mod f:', r)
print('Res(f, g mod f):', resultant)
