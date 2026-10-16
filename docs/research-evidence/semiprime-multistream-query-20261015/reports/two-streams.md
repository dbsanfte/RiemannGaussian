# Two-stream / short hypergeometric transformations audit

No whole-family soft O(J+sqrt L) acquisition algorithm was obtained. The exact short terminating identity below pays only soft O(JK) for its coefficients when K is polylogarithmic, but still requires long row products. Conversely, the existing exclusive-own-row obstruction cannot exclude arbitrary two-stream encodings: two privately constructed streams already suffice algebraically. This is an interface gap, not a scalar complexity lower bound.

Work is over A=Z/NZ, q a supplied unit, P_n(z)=(z;q)_n=product_{r=0}^{n-1}(1-zq^r), J~m, L~m². The retained source has distinct odd prime local orders R_P,R_Q>L. Thus 1-q^t is a unit for 1<=t<=L. Targets z_j=gamma^(-N-delta_j) lie in the local odd q-subgroups. No group order or factorization is an algorithm input.

## A short q-Chu–Vandermonde identity, including the denominator debt

For 0<=K<=L, the first q-Chu–Vandermonde sum (DLMF 17.6.2), with n=L, a=q^(-K), c=zq^(-K), gives

 P_L(z)/P_L(zq^(-K))
 = sum_{k=0}^K [(q^(-L);q)_k(q^(-K);q)_k / ((zq^(-K);q)_k(q;q)_k)] (zq^L)^k.

This rational expression is valid only where its denominators are invertible. It must not be evaluated through zero denominators on a collision input. Its correct universally specialized finite form is

 P_L(z) = sum_{k=0}^K B_k (zq^L)^k P_{L-k}(zq^(k-K)),
 B_k=(q^(-L);q)_k(q^(-K);q)_k/(q;q)_k.                     (1)

Equation (1) follows by multiplying the generic identity by P_L(zq^(-K)) and cancelling the initial k factors symbolically, then specializing the resulting polynomial identity in z. Its only inversions are factors of (q;q)_K, which are units under the source assumptions; it remains valid when a row product vanishes in either field. It needs neither discrete logarithms nor order knowledge.

All B_k can be generated in O(K) ring operations, with a single batch inversion of 1-q^t, t<=K. Given the z_j, the coefficient/monomial metadata costs O(JK) ring operations plus O(log L) powering (and the already public target powers cost O(J log N)). Hence K=polylog m fits the desired budget. But (1) requests K+1 products of lengths L,L-1,...,L-K at shifted row origins. In particular k=0 retains P_L(zq^(-K)); K=0 is the original identity. These are not selected coefficients in one or two fixed-top Gaussian streams. No claim of a lower bound for further aggregation of (1) is made.

A unit normalizer cannot simply be supplied for free. Choosing c=-z would make P_L(c) a unit on the odd local source groups: -zq^r cannot equal 1. But to keep c/a=z in the same q-Chu specialization this forces a=-1, which does not terminate at a small K since q^K cannot be -1 in an odd-order group. This rules out that particular combination of short termination and automatically safe negative normalizer. Other identities remain open. If an acquired normalizer has proper gcd with N it factors N; computing its long value is itself unpaid. A short denominator with gcd N gives no proper factor, and division by it is invalid.

Source: https://dlmf.nist.gov/17.6.E2 (formula); the reversed second version, https://dlmf.nist.gov/17.6.E3, has the same product normalizer rather than a free fixed-top lookup.

## Why two streams evade the known support obstruction

On the retained exclusive-own-row family, some actual row values have gcd P and others gcd Q. A single forward prefix stream with unit denominator products has nested prime-zero supports, so one value times a unit cannot encode both. This nesting argument does not extend to two streams.

Indeed, with the factors privately known, construct stream A with values A_0=1,A_k=P for k>=1, and stream B with values B_0=1,B_k=Q for k>=1. Both are forward prefix streams (first numerator P or Q, all later numerators 1, all denominators 1). Their products at indices 0 or 1 have the four supports: unit, P-only, Q-only, both. Every scalar a in Z/PQ is a unit multiple of the corresponding value 1,P,Q,0. For the P-only case, choose a unit u with u=a/P mod Q and u nonzero mod P by CRT; the Q-only case is symmetric. Thus even exact two-stream representations with arbitrary unit prefactors are algebraically possible for every row list. This is not a public algorithm: acquiring these streams and prefactors uses the factors. It proves that a new two-stream impossibility theorem needs additional public-construction constraints; exclusive supports alone are insufficient.

Sums are still less constrained: cancellation can create zeros from unit summands. Ratios require explicit unit-denominator checks; ratios with nonunit denominator are not values in A. None of these observations supplies the required public coefficients/indices.

## Root-of-unity Lucas and Heine: exact remaining interfaces

The finite Gaussian identity at a primitive r-th root in a field of characteristic not dividing r is

 [ar+b choose cr+e]_q = binom(a,c) [b choose e]_q, 0<=b,e<r.

It follows from the finite q-binomial generating product by grouping blocks of r factors (including the usual q-binomial signs), so no analytic convergence is involved. But its block length is the actual local order. The source has different R_P and R_Q. A single public integer r coprime to N with Phi_r(q)=0 in both fields would force r=R_P=R_Q, impossible here. This precise statement uses the primitive-root characterization for characteristic not dividing r. If an acquired Phi_r(q) has a proper gcd, that test factors N; no inexpensive procedure to find such an r is supplied by Lucas. Using the two hidden orders separately requires the unavailable local decomposition. For public t<min(R_P,R_Q), 1-q^t is a unit and gives no denominator factor. This is a scoped failure of direct common-order specialization, not exclusion of all cyclotomic methods.

Bhatnagar's bibasic Heine paper (arXiv:1606.05460), notably its transformation and convergence discussion around equations (5), (6), (8), assumes complex bases of modulus below one and convergent infinite series/products. Its finite terminating specializations can yield algebraic identities after denominator clearing, but the analytic formula itself is not a composite-ring evaluation algorithm, nor does it charge J varying parameters. No finite specialization removing the long normalizer was identified here.

The recent q-Binomial Identities Finder (arXiv:2408.00186, published 2026) constructs and certifies symbolic q-binomial identities from parameter constraints. Its algorithm concerns symbolic conversion/identity discovery; it supplies no arithmetic bound for J selected scalar values of a length-L Pochhammer over Z/NZ. Its finite identities may be specialized after clearing and checking denominators; their existence does not instantiate the missing fixed-stream acquisition.

Primary URLs: https://arxiv.org/abs/1606.05460 ; https://arxiv.org/abs/2408.00186 . Downloaded PDFs and extracted text are adjacent and hashed in sources.json. This audit makes no exhaustive claim about every hypergeometric transformation, no arbitrary two-stream lower bound, and no improvement on the existing soft O(J+sqrt(JL)) acquisition baseline.
