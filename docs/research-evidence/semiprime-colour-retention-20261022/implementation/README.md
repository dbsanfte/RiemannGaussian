# Packed Gauss quotient: portable reference implementation

`packed_gauss.py` acquires the actual k modular coefficients of C_E in (Z/N)[X]/(X^k-1), using only N and public auxiliary prime ell, k dividing ell-1, and E. It certifies the small public auxiliary by trial division, finds a public primitive root, walks its full log table, builds every needed Jacobi histogram, applies all-character exception projectors, and executes the proved binary recurrence. No hidden factor, finite field, root modulo N, character value of P, or precomputed Gauss sum is a production input.

It also implements the all-divisor monomial restriction extractor from `../packed_coefficients/report.md`, section 1. This consumes one acquired coefficient vector normalized by sum(C)=1; C_N has this normalization for odd N. It folds using the prescribed divisor-parent tree and computes every excluded-position gcd with prefix/suffix arrays. A proper result is a scalar factor. Otherwise it reports global monomials or the theorem's conditional `BOTH_LOCALLY_NONMONOMIAL` status. The latter interpretation assumes N is a distinct-prime odd semiprime, as in the theorem; this program does not certify that promise. No guarded polynomial half-gcd or torsion controller is implemented.

## Running

Use Python 3. With gmpy2 installed, the default backend packs coefficients into fixed-width little-endian bytes and multiplies two mpz integers. Without it, the same exact code uses Python integers; `--backend quadratic` explicitly selects the quadratic control convolution.

```
python3 packed_gauss.py --modulus 35 --auxiliary-prime 3 --order 2 --extract
python3 -m unittest -v test_packed_gauss.py
```

The CLI returns JSON including the actual coefficients and extractor result. A proper public input gcd is returned as a factor; a wholly noncoprime input or invalid auxiliary is rejected. E defaults to N. E=0 is implemented (C_0=-1), but does not meet the extractor's sum-one contract. Packed C_E output is not advertised as factor-producing for every input.

The local reviewed environment also supports:

```
/home/dbsanfte/riemann/formal/.lake/plot-venv/bin/python -m unittest -v test_packed_gauss.py
```

## Packing and arithmetic ledger

For canonical residues 0<=a_i,b_i<N, each coefficient of the ordinary product is at most k(N-1)^2. Choose byte width w with 256^w>k(N-1)^2. No product digit carries into its neighbor. The implementation packs each vector once, multiplies, converts the result to bytes once, then slices the 2k-1 fixed-width digits and folds their indices modulo k. It does not repeatedly shift one large integer while extracting coefficients. Packing and extraction have linear output volume O(k(log N+log k)) bits.

This realizes the paper's integer-convolution reduction. The soft-linear multiplication claim depends on the underlying integer multiplication model; this reference does not certify Python allocation cost or GMP's selected algorithm at every input size. The explicit quadratic backend and tiny full-carrier test oracle are controls, not evidence for the paper's soft-linear bound. The primitive's algebraic proof and theoretical bit ledger are in:

- `/tmp/semiprime-weighted-acquisition-20261022/gauss_literature/packed-gauss-quotient.md`;
- `/tmp/semiprime-weighted-acquisition-20261022/high_order_colour/packed-gauss-independent-review.md`;
- `/tmp/semiprime-colour-retention-20261022/packed_coefficients/report.md`.

At most O(log E) Jacobi histograms, projector combinations, and cyclic multiplications are acquired. Each histogram enumerates ell-2 public terms. Projector denominators divide k, so gcd(N,ell*k)=1 certifies every inverse. Every divisor vector is produced from one parent, not by rescanning the original k coefficients for each divisor. Total folding additions are at most omega(k)*sum_(d|k)d, and all support tests cost O(sum_(d|k)d) gcd calls. The complete construction plus extractor has the proved soft O(ell+k) native bound when N-sized logarithms are suppressed, without constructing the joint ell*k carrier. That is a mathematical algorithm bound, not a certified interpreter-runtime assertion.

## Meaningful exact validation

`test_packed_gauss.py` checks byte packing against independent quadratic convolution, including maximum carry bounds and 130-bit moduli. On small public auxiliary primes it constructs the full test-only algebra with X^k=1 and Phi_ell(Z)=0, then checks every product constant c_ab and multiple C_E recurrences directly. This includes trivial, one-trivial, canceling, nonprimitive and ordinary characters, k=1, ell=2, composite orders, E=0, and exponent wrap. A separate cocycle identity uses larger supplied exponents, and unit guards are checked.

Synthetic CRT vectors exercise equal global monomials, one local monomial versus a dense vector, unequal local monomials, dense vectors at both factors, and a case whose first support separation appears only after a proper-divisor fold. P,Q occur only in these validation oracles. The tests are exact algebra controls; no factor-success campaign, timing benchmark, universal auxiliary selection, native-query solution, or improved factoring exponent is claimed.
