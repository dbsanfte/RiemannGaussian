from math import gcd, isqrt


def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def local_image(a, n, p):
    return {(a * x + n * pow(x, -1, p)) % p for x in range(1, p)}


for p in range(11, 102):
    if not prime(p):
        continue
    for n in range(1, p):
        coefficients = {n * t * t % p for t in range(1, p)}
        merged = {(a - z) % p for a in coefficients for z in local_image(a, n, p)}
        assert len(merged) == p, (p, n, merged)
    print(f'l={p}: every nonzero n has all coefficient-compensated shifts')

N, D, beta, a, theta, s = 247, 7, 4, 1, 2, 4
n = N % D
menu = local_image(3, n, D) | local_image(2, n, D)
assert s in menu
assert a == theta * theta * 2 % D
assert gcd(N, D) == 1
z = theta * s % D
kappa = theta * s // D
q = pow(beta, D, N)
correct = pow(beta, N + a - z, N)
wrong = pow(beta, N + a - theta * s, N)
assert correct == wrong * pow(q, kappa, N) % N
product, product_wrong = 1, 1
for i in (1, 2):
    product = product * (pow(q, i, N) - correct) % N
    product_wrong = product_wrong * (pow(q, i, N) - wrong) % N
assert gcd(product, N) == 13
assert gcd(product_wrong, N) == 1
print('Actual menu carry example:', dict(N=N, D=D, beta=beta, a=a, theta=theta,
      s=s, z=z, kappa=kappa, q=q, correct=correct, wrong=wrong,
      gcd_correct=gcd(product, N), gcd_wrong=gcd(product_wrong, N)))
