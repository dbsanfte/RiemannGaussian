# Scalar geometric product literature audit — 2026-10-15

## Result

No verified nearlinear whole-family acquisition algorithm was found. The degree-sensitive Bostan–Yurkevich bound remains soft O(J+sqrt(JL)) ring operations, hence soft O(m^(3/2)) for J~m,L~m². This is an upper bound and a limitation of a specified dense-block contract, not an arbitrary scalar lower bound. A separate rigorous obstruction below rules out rational multiplicative endpoint telescoping.

## Primary sources checked

* Bostan–Yurkevich, *Fast Computation of the N-th Term of a q-Holonomic Sequence and Applications*, JSC 115 (2023), 96–123, https://arxiv.org/abs/2012.08656 and https://arxiv.org/pdf/2012.08656 . Downloaded fresh as by.pdf, extracted by.txt. Expanded article includes Algorithm 3, §3.4, Theorems 5–6 and Corollary 7. Author copy: https://yurkevi.ch/data/Alin%20Bostan,%20Sergey%20Yurkevich_2020_Fast%20Computation%20of%20the%20N-th%20Term%20of%20a%20q-Holonomic%20Sequence%20and%20Applications.pdf .
* Current primary author bibliographies https://mathexp.eu/bostan/ and https://yurkevi.ch/me.html checked, plus searches for 2024–2026 q-holonomic/q-Pochhammer evaluation improvements. No applicable newer degree-sensitive theorem located. This is a search result, not a completeness theorem about the literature.
* Bostan–Flajolet–Salvy–Schost, *Fast Computation of Special Resultants*, https://cs.uwaterloo.ca/~eschost/publications/BoFlSaSc05.pdf ; archived primary and previous source audit restored. Composed polynomial output retains product degree; this does not establish a scalar shortcut for varying origins.
* Bernstein et al., *Faster computation of isogenies of large prime degree*, https://velusqrt.isogeny.org/velusqrt-20200616.pdf surfaced as related resultant/structured index-set technique. No theorem for these arbitrary supplied target rows follows merely from that analogy.

## Correct parameter charging

For scalar recurrence A_(n+1)=F(u q^n)A_n, order r=1 but coefficient degree d=J. Theorem 5 over a field K, with its nonsingular recurrence assumptions and N>d, costs O(r^theta sqrt(Nd)+r² M(sqrt(Nd))). Here N in that theorem is L, not the semiprime modulus. Its fixed-degree soft O(sqrt(L)) summary cannot be used at growing J.

Theorem 6 computes several indices of ONE fixed recurrence. Its last §3.4 paragraph explicitly restores dependence: at most sqrt(L) indices cost O((r^theta d sqrt(L)+r² M(d sqrt(L))) log L), or at most sqrt(L/d) indices cost O((r^theta sqrt(Ld)+r² M(sqrt(Ld))) log L). Thus its unparameterized fixed-recurrence statement is not soft O(m) for m distinct Y_j. Changing target Y_j changes the recurrence. Even shared prefix values do not license division by prefix products over Z/N.

Theorem 8 concerns exact rational/integer outputs and their growing bitsizes; it is not a modular scalar improvement.

## Ring-safe existing construction

Restored verified previous report: ../restored-q/tmp/semiprime-implicit-followup-20261008/review/q-factorial-upper-bound.md . It gives a direct proof rather than blindly transferring a field theorem. Build P_s(X)=prod_(i<s) F(u q^i X) by P_(2t)(X)=P_t(q^t X)P_t(X), then evaluate P_s at q^(sk), k<L/s. Chirp convolution uses only powers and inverse of known unit q, not inverses of q^k-1, differences of targets, or candidate collision factors. Cost soft O(Js+L/s+J). Optimizing s~sqrt(L/J) gives soft O(J+sqrt(JL)). Kronecker polynomial multiplication gives soft O((J+sqrt(JL))(log N+log(JL))) bits. No field interpolation or FFT-root assumptions are needed.

Variable unit origins are absorbed by target rescaling and an explicit known unit phase. Unequal lengths use disjoint binary blocks, grouping equal block lengths; summing soft O(J_k+sqrt(2^k J_k)) retains soft O(J+sqrt(JLmax)). Exponents must remain polynomial bit length, as in the stated public family. Arbitrary nonunit origins cannot be normalized this way.

Since F is monic and u,q units, deg P_s=Js exactly even modulo composite N. A backend materializing all Js+1 coefficients and floor(L/s) block values must expose at least Js+floor(L/s)>=2sqrt(JL)-1 residue words. This is a rigorous obstruction to this output contract. Repeated squaring of a compact instruction graph does not prove its scalar evaluation has that cost or a smaller cost; both reuse at distinct arguments and acquisition must be charged.

## A rigorous obstruction to rational endpoint cancellation

Proposition. Let K be any field, q in K*, and F in K[X] have positive degree J and F(0) nonzero. There are no nonzero G in K(X), c in K*, and integer a such that

    F(X) = c X^a G(qX)/G(X)

as rational functions.

Proof. Scaling X by q preserves valuation at zero and at infinity. The quotient G(qX)/G(X) consequently has valuation zero at both places. Valuation at zero in the asserted identity gives a=0. Valuation at infinity would then give -J=0, impossible.

For the supplied family F(X)=prod_j(X-Y_j), every Y_j is a unit; reducing mod either semiprime factor preserves degree J and nonzero constant coefficient. Hence any proposed identity over the composite ring that specializes to nonzero rational endpoints over a residue field is ruled out. This blocks ordinary rational multiplicative telescoping, including Laurent-monomial normalizations, without making an unjustified scalar complexity claim. It does NOT rule out length-dependent endpoint functions of growing degree, special-function endpoints such as q-Pochhammers, finite-orbit numerical formulas, moving moduli, higher-order recurrences, or short circuits. Nor does it rule out cancellations in ratios of different target rows when an actual signed orbit-boundary identity is supplied. The target here is an all-positive product.

The familiar identity (a;q)_(2t)=(a;q)_t(a q^t;q)_t does not use the same scalar twice. Iterating it creates shifted arguments. The distinct identity (a;q)_L(-a;q)_L=(a²;q²)_L is valid without divisions but only pairs opposite targets; it requires demonstrated pairing in the literal family. Squaring arbitrary numeric q does not produce such a pairing.

## gcd-only qualification

A gcd query can stop early on a proper factor, and any attempted inversion should be replaced by a gcd test: gcd=1 licenses inversion, 1<gcd<N solves factoring, gcd=N does neither. Product zero modulo N can combine collisions at the two different primes; resolving it by product-tree subdivision has its own acquisition cost. Computing gcd of this dense-block product does not remove the coefficient/evaluation floor. No universal gcd-only lower bound is claimed, and a different early-factor algorithm remains outside this obstruction.

## Outstanding genuine theorem

A positive result still needs an actual short evaluator or whole-family signed cancellation identity with all public target phases and endpoints preserved. First-order q-holonomicity, a scalar output, numerical q-squaring, and bibliographic fixed-degree sqrt(L) claims supply none of those by themselves.
