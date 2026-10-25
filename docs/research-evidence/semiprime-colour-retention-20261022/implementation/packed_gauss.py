"""Reference paid packed Gauss quotient; no hidden factors/fields are inputs.

Proof: gauss_literature/packed-gauss-quotient.md; extractor:
packed_coefficients/report.md section 1 (adjacent research scratch trees).
GMP-backed byte Kronecker convolution is the default when available. The
Python packed fallback is exact; no certified Python/GMP runtime is claimed.
"""
from math import gcd, isqrt
try:
    from gmpy2 import mpz as BigInt
    PACK_BACKEND = 'gmpy2-mpz-byte-kronecker'
except ImportError:
    BigInt = int
    PACK_BACKEND = 'stdlib-int-byte-kronecker'


class PublicFactor(ValueError):
    def __init__(self, factor):
        self.factor = factor
        super().__init__(f'public input gcd supplies proper factor {factor}')


def prime_factors(n):
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            result.append(p)
            while n % p == 0:
                n //= p
        p += 1 if p == 2 else 2
    if n > 1:
        result.append(n)
    return result


def divisors(n):
    out = [1]
    for p in prime_factors(n):
        power = 1
        old = out[:]
        while n % (power * p) == 0:
            power *= p
            out.extend(d * power for d in old)
    return sorted(out, reverse=True)


def cyclic_mul(a, b, modulus, backend='packed'):
    """Acquire full cyclic convolution. Width strictly exceeds carry bound."""
    k = len(a)
    if not k or len(b) != k or modulus < 2:
        raise ValueError('equal nonempty vectors and modulus >=2 required')
    a = [int(x) % modulus for x in a]
    b = [int(x) % modulus for x in b]
    if backend == 'quadratic':
        out = [0] * k
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                out[(i+j) % k] = (out[(i+j) % k] + x*y) % modulus
        return out
    if backend != 'packed':
        raise ValueError('backend must be packed or quadratic')
    bound = k * (modulus-1)**2
    width = max(1, (bound.bit_length()+7)//8)
    # Base=256**width > bound. No convolution digit can carry.
    aa = BigInt.from_bytes(b''.join(x.to_bytes(width, 'little') for x in a), 'little')
    bb = BigInt.from_bytes(b''.join(x.to_bytes(width, 'little') for x in b), 'little')
    data = (aa*bb).to_bytes((2*k-1)*width, 'little')
    out = [0] * k
    for i in range(2*k-1):
        value = int.from_bytes(data[i*width:(i+1)*width], 'little')
        out[i % k] = (out[i % k] + value) % modulus
    return out


class PackedGauss:
    def __init__(self, modulus, auxiliary_prime, order, backend='packed'):
        N, ell, k = modulus, auxiliary_prime, order
        if N < 3 or N % 2 == 0:
            raise ValueError('odd modulus >=3 required')
        if ell < 2 or any(ell % p == 0 for p in range(2, isqrt(ell)+1)):
            raise ValueError('auxiliary must be a public prime')
        if k < 1 or (ell-1) % k:
            raise ValueError('positive order must divide auxiliary_prime-1')
        g = gcd(N, ell*k)
        if 1 < g < N:
            raise PublicFactor(g)
        if g != 1:
            raise ValueError('input gcd is entire modulus; coprime contract fails')
        self.N, self.ell, self.k, self.backend = N, ell, k, backend
        factors = prime_factors(ell-1)
        self.generator = next(g for g in range(1, ell)
                              if all(pow(g, (ell-1)//p, ell) != 1 for p in factors))
        self.logs = [None] * ell
        x = 1
        for e in range(ell-1):
            self.logs[x] = e % k
            x = x*self.generator % ell
        self.histograms = 0
        self.multiplications = 0

    def mul(self, a, b):
        self.multiplications += 1
        return cyclic_mul(a, b, self.N, self.backend)

    def one(self):
        return [1] + [0]*(self.k-1)

    def projector(self, a):
        a %= self.k
        h = self.k // gcd(a, self.k)
        inv = pow(h, -1, self.N)
        out = [0]*self.k
        for t in range(h):
            out[a*t % self.k] = inv
        return out

    def jacobi_histogram(self, a, b):
        self.histograms += 1
        out = [0]*self.k
        for t in range(2, self.ell):
            e = (a*self.logs[t]+b*self.logs[(1-t) % self.ell]) % self.k
            out[e] = (out[e]+1) % self.N
        return out

    def product_constant(self, a, b):
        """All-character c_ab, including both trivial and cancellation cases."""
        a, b = a % self.k, b % self.k
        J = self.jacobi_histogram(a, b)
        both = self.mul(self.projector(a), self.projector(b))
        cancel = [(x-y) % self.N for x, y in zip(self.projector(a+b), both)]
        correction = self.mul(cancel, J)
        return [(j+(self.ell-1)*(c-z)) % self.N
                for j, c, z in zip(J, correction, both)]

    def quotient(self, exponent):
        """Return actual k coefficients C_E with G_1**E=C_E G_(E mod k)."""
        if exponent < 0:
            raise ValueError('nonnegative exponent required')
        if exponent == 0:
            return [self.N-1]+[0]*(self.k-1)
        C, e = self.one(), 1 % self.k
        for bit in bin(exponent)[3:]:
            C = self.mul(self.mul(C, C), self.product_constant(e, e))
            e = 2*e % self.k
            if bit == '1':
                C = self.mul(C, self.product_constant(e, 1))
                e = (e+1) % self.k
        return C


def all_divisor_monomial_extract(modulus, coefficients):
    """Return first support-separating factor, or exact all-divisor statuses.

    Normalized input sum(C)=1 is required. Production never receives P,Q.
    Folding parents and all excluded-position gcds are linear per divisor.
    BOTH_LOCALLY_NONMONOMIAL interpretation assumes odd squarefree semiprime N.
    """
    N, k = modulus, len(coefficients)
    if N < 3 or N % 2 == 0 or k < 1:
        raise ValueError('odd modulus and nonempty coefficient vector required')
    C = [int(c) % N for c in coefficients]
    if sum(C) % N != 1:
        raise ValueError('normalization sum(C)=1 modulo N required')
    vectors, records = {k: C}, []
    factors = prime_factors(k)
    folding_additions = 0
    for d in divisors(k):
        if d != k:
            p = next(p for p in factors if (k//d) % p == 0)
            parent = d*p
            V = [0]*d
            for i, c in enumerate(vectors[parent]):
                V[i % d] = (V[i % d]+c) % N
                folding_additions += 1
            vectors[d] = V
        V = vectors[d]
        support = [i for i, c in enumerate(V) if c]
        if len(support) == 1 and V[support[0]] == 1:
            records.append({'divisor': d, 'status': 'GLOBAL_MONOMIAL',
                            'position': support[0]})
            continue
        prefix, suffix = [N]*(d+1), [N]*(d+1)
        for i, c in enumerate(V):
            prefix[i+1] = gcd(prefix[i], c)
        for i in range(d-1, -1, -1):
            suffix[i] = gcd(suffix[i+1], V[i])
        for r in range(d):
            g = gcd(prefix[r], suffix[r+1])
            if 1 < g < N:
                return {'factor': g, 'divisor': d, 'position': r,
                        'records': records, 'folding_additions': folding_additions}
        records.append({'divisor': d, 'status': 'BOTH_LOCALLY_NONMONOMIAL'})
    return {'factor': None, 'records': records,
            'folding_additions': folding_additions}


def main():
    import argparse
    import json
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--modulus', type=int, required=True)
    parser.add_argument('--auxiliary-prime', type=int, required=True)
    parser.add_argument('--order', type=int, required=True)
    parser.add_argument('--exponent', type=int, help='default: modulus')
    parser.add_argument('--backend', choices=['packed', 'quadratic'], default='packed')
    parser.add_argument('--extract', action='store_true',
                        help='all-divisor test, requires sum(C_E)=1 (e.g. odd E)')
    args = parser.parse_args()
    try:
        pg = PackedGauss(args.modulus, args.auxiliary_prime, args.order, args.backend)
        E = args.modulus if args.exponent is None else args.exponent
        C = pg.quotient(E)
        result = {'modulus': pg.N, 'auxiliary_prime': pg.ell, 'order': pg.k,
                  'exponent': E, 'coefficients': C, 'generator': pg.generator,
                  'backend': PACK_BACKEND if args.backend == 'packed' else 'quadratic',
                  'jacobi_histograms': pg.histograms,
                  'cyclic_multiplications': pg.multiplications}
        if args.extract:
            result['restriction_extractor'] = all_divisor_monomial_extract(pg.N, C)
        print(json.dumps(result, sort_keys=True))
    except PublicFactor as exc:
        print(json.dumps({'factor': exc.factor, 'source': 'public input gcd'}))
    except ValueError as exc:
        parser.error(str(exc))


if __name__ == '__main__':
    main()
