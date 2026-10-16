# A supplied small multiple of the global order suffices in soft-m bit cost

2026-10-16. Independently checked conditional extraction lemma. It does not acquire the promised multiple.

Let m>=2 be an integer, n=m², N=P Q with distinct primes, and S=P+Q−1. Suppose D|N−S, 0<S<D, and every prime divisor of D exceeds n. Given a NONZERO integer K with |K|=cD and 1<=c<=n, one can recover D and factor N deterministically in soft-O(m (log|K|+log m)+polylog N) bit operations. Thus for the qualified original source, where logN,log|K|=O(logm), this is soft-O(m) bits.

The actual-source premise D=R_P R_Q with distinct exact local prime orders R_P,R_Q>16m² suffices. Its D>16m⁴ and balanced S<=3m³ imply S<D. D divides phi(N)=N−S. This is conditional on that qualified branch, not a claim for arbitrary public gamma. No knowledge of R_P,R_Q or factors of K is used.

## Exact cofactor stripping

Let A=n! mod |K|. Since c is one of the factors 1,...,n, c|n!. Since all prime factors of D exceed n, gcd(D,n!)=1. Therefore

    gcd(|K|,A)=gcd(cD,n!)=c,
    D=|K|/gcd(|K|,A).

This equality handles repeated prime powers in c and does not need a smoothness heuristic. K may be negative; use its absolute value. K=0 is explicitly excluded.

The alternative public promise 0<|K|<=16m⁶ together with D>16m⁴ and D|K ensures c<m². Conversely, c<=m² and D|phi(N)<N<=m⁶ ensure |K|<m⁸, also giving O(logm)-bit modulus. The two upper-bound contracts are sufficient alternatives, not equivalent bounds on all valid K.

## Composite-safe factorial, with no factor-return branches

Work in R=Z/|K|Z, even when its factorization is unknown. Construct

    f(X)=product_(i=1)^m (X+i).

Use a balanced polynomial product tree. Compute f(jm), j=0,...,m−1, by the ordinary subproduct/remainder tree, whose leaves are the monic linear polynomials X−jm. Then

    A=product_(j=0)^(m−1) f(jm) mod |K|=(m²)! mod |K|.

Both trees have degree at most m and cost O(M_R(m) logm) ring operations up to standard logarithmic factors. Every remainder divisor is MONIC. Fast monic division uses reversal and reciprocal of a power series with constant coefficient1. Its Newton update g -> g(2−fg) uses addition/multiplication and no scalar division, including in characteristic2 or over zero divisors. Distinctness or invertibility of point differences is unnecessary for EVALUATION by remainder trees. It is interpolation that would require unit differences. The points jm may therefore collide modulo factors of K without invalidating the output.

In particular, no BGS arithmetic-progression interpolation hypothesis and no guarded inversion of a potentially nonunit is needed. A gcd branch returning a factor of K would generally not be a factor of N; this construction avoids that concern entirely. The final integer gcd is used only for the exact cofactor identity above.

For a direct bit realization, represent ring coefficients by canonical ell-bit residues, ell=ceil(log2|K|). Integer Kronecker encoding multiplies degree-m coefficient arrays using O(m(ell+logm))-bit integers before reduction; product coefficients have O(ell+logm) bits beyond one coefficient scale. Fast integer multiplication, reduction, product trees and monic Newton division yield soft-O(m(ell+logm)) bit cost. This also bounds workspace up to polylog factors. Construction of the points, the m output multiplications, and the one gcd/exact integer division fit this bound. No randomness or hidden-order arithmetic oracle occurs.

## Recovering the semiprime

Compute S0=N mod D as the least nonnegative integer residue. The promises D|N−S and 0<S<D imply S0=S. Set T=S0+1. Then the discriminant T²−4N=(P−Q)² is an exact nonnegative square. An integer square root and the two values (T±sqrt(T²−4N))/2 recover P,Q in polylogN bit cost. Under a merely claimed certificate, one can verify these final factors by multiplication; the theorem does not claim to recognize all invalid K promises or that an invalid candidate must produce a factor.

## Primary support and scope

The constructive proof above uses the classical Strassen block-factorial method and generic monic multipoint evaluation, rather than importing an arithmetic-progression optimized theorem with unverified unit assumptions.

- Neiger--Salvy--Schost--Villard, Faster Modular Composition, author primary PDF https://cs.uwaterloo.ca/~eschost/publications/NSSV24.pdf, introduction p1 explicitly distinguishes quasi-linear monic division/multipoint evaluation over commutative rings from interpolation requiring unit differences. Only that standard arithmetic premise is used; none of its randomized modular-composition conclusions is required.
- Bostan--Gaudry--Schost, Linear Recurrences with Polynomial Coefficients and Application to Integer Factorization and Cartier--Manin Operator, author primary PDF https://mathexp.eu/bostan/publications/BoGaSc04.pdf, arithmetic conventions p3 cover polynomial multiplication over arbitrary commutative rings. Its faster special evaluation formulas carry additional hypotheses; the present proof does not invoke them.

The extraction interface has improved from a full q-collision scalar to the alternative sufficient certificate of a small NONZERO integer multiple of D. No cheap method to obtain that multiple is asserted. In particular, a relation only in one hidden field, a zero integer relation, or a congruence modulo N is not this input. Large unknown multipliers outside c<=m² are not covered. This is a conditional positive recovery lemma, not a factoring algorithm or a lower bound against other query routes.
