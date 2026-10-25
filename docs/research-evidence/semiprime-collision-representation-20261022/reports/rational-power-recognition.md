# Rational-power recognition from the one acquired W^N vector

22 October2026. Constructive attempts using exact rational-power lifts, a carried first-order differential relation, and valid automorphism differences. No frozen edits, backend, examples, generic lower bound, or all-input recognition theorem. The main exact finding is that a paid low-order wrap lift of W^N is canonically flat; it does not expose the hidden rational exponent through an ordinary logarithmic derivative.

## Actual input and exact unfolded source

Let f=X^m−1, W=t(1+gamma X)/(X+gamma), and F_0=W^N modf, acquired in soft m bit work. Unit denominators/inverses are guarded as in the retained setup. At a hidden prime P with j=P modm,

    F_0=(rho_j W)^Q mod(P,f), N=P Q.              (1)

This is genuine whole-local-algebra equality. But write P=j+mh. BEFORE cyclic reduction the exact relation is

    W(X)^N = [t(1+gamma X^j(1+f)^h)
                   /(X^j(1+f)^h+gamma)]^Q modP.  (2)

Replacing X^P by X^j is justified only modulo f. Thus an ordinary rational-power Padé recognizer on the canonical degree-<m representative may not impose the differential equation of (rho_j W)^Q without also acquiring/retaining this wrap factor.

## 1. Paid wrap jets and a valid logarithmic derivative

Compute the ONE lift W^N modf² by binary powering in the rank-2m quotient, in soft m. Write it F_0+f F_1 with both F_i of degree<m. As an UNREDUCED rational function over Z/N,

    (W^N)'=N W^(N−1)W'=0.

Taking its derivative and reducing modf gives exactly

    F_0'+mX^(m−1)F_1=0,
    F_1=−(mX^(m−1))^−1 F_0' modf.                (3)

The inverse exists because m and X are units. Hence this first wrap jet is already a paid explicit function of F_0; it is not a new independent rational-exponent certificate. Applying F_0'/F_0 as if it were Q times the logarithmic derivative of rho_jW would omit precisely the second term in(3).

There is a stronger constructive description. For any fixed jet order k below both hidden primes, form

    S(X)=X(1+f)^(-1/m) modf^k.

The binomial coefficients use only m and the factorials through k−1 as denominators; these are units under the retained P,Q>16m² for all fixed/polylog k. It has S^m=1 and S'=0 to the required order. The unique flat lift of F_0 is

    W^N modf^k = F_0(S(X)) modf^k.                (4)

One proof is to work at either hidden prime, use the étale root coordinate S, and Taylor-expand through degree k−1; all ordinary derivatives of W^N vanish, and the factorials are invertible in this range. CRT gives(4). This is an identity, not an assumption of a derivative on the cyclic quotient. For fixed k it is actually acquired in soft m; a growing k charges its rank km and power-series work.

The true hidden h in(2) satisfies h=−j/m modP, because P=0 in F_P. Thus its small-order f-adic coefficients coincide with the public flat substitution X^j(1+f)^(-j/m). The apparently unknown logarithmic-derivative correction cancels exactly. This resolves the naive low-jet recognition attempt; it makes no claim that another nonlinear recognition method is impossible.

## 2. A carried ODE gives an exact equation, but no closed short recurrence yet

For an unreduced rational power G=W^q one has

    d(X)G'=q c G,
    d(X)=(X+gamma)(1+gamma X),
    c=gamma²−1.                                  (5)

Indeed W'/W=c/d. If G_0 is its cyclic representative and G_1 the first f-adic digit, reduction of(5) gives

    d(X)[G_0'+mX^(m−1)G_1]=q c G_0 modf.          (6)

For the permuted input (rho_jW)^q, d is replaced by (X^j+gamma)(1+gamma X^j), and the right side contains q*j*X^(j−1)c. This is the actual first-order rational-power equation with the wrap included. Since d is a unit in the retained algebra, for ANY supplied q,j and G_0 it algebraically determines a candidate G_1. The extra certificate needed is that this digit belongs to the SAME global rational power, with its numerator/denominator degree boundary; solving(6) alone does not test that certificate.

In particular the public lift F_1 of W^N is flat by(3), while the naive lift of (rho_jW)^Q generally is not. Its equality in(1) is insufficient to identify those two lifts. A Padé recognizer that equates them would reject a true source. No low-order recurrence closing only on F_0 and public j,q was found after retaining the actual carry term. A useful future theorem would give a small CLOSED family of wrap/carry states, acquired jointly for every unit j, with a boundary condition that forces a factor or the true local rational exponent. This remains an arithmetic recognition problem, not a free ordinary ODE test.

## 3. Valid automorphism differences and low-degree rational tests

Automorphisms DO descend. For fixed public unit s,

    rho_s(F_0)/F_0 = [rho_s(W)/W]^N modf.          (7)

The reference base rho_s(W)/W is low-degree for fixed small s, and both sides are paid with one additional vector/power. At the true P it is the j-conjugate Qth power of that rational base, so the source is retained. However(7) is a globally valid power identity for ALL inputs; it alone is not a zero divisor or a separator. Repeating it for polylogarithmically many s provides an ACTUALLY acquired joint family, but I found no identity eliminating Q and selecting j from it without rebuilding the varying native power relation. Commuting rho actions only yield tautological commutators unless an additional asymmetric relation is proved.

For a fixed supplied exponent e, the test F_0=(rho_jW)^e has a denominator-cleared numerator with O(e) common shifted vectors. When e=1, it is exactly

    (X^j+gamma)(F_0−rho_jW)
      =(gamma F_0−t)+(F_0−t gamma)X^j,

so deterministic gcd-aware KMP on TWO acquired arrays handles all j in soft m. This is an actual low-degree recognition consumer. Its native source would require e=Q, which is unknown and exceeds the small-degree regime. Reducing e modulo m is invalid: integer powers of W are not periodic with public period m. This observation identifies the usable interface rather than claiming that a fixed small e covers all inputs.

## Perfect-power literature scope

Giesbrecht–Roche, *Detecting lacunary perfect powers and computing their roots*, arXiv:0901.1848v2,3Dec2010, primary23-page paper opened, introduction/input model inspected: https://arxiv.org/pdf/0901.1848 . Its Monte Carlo detection concerns supplied sparse POLYNOMIALS f=h^r over Q or a supplied field of characteristic larger than deg f; deterministic root routines have their own sparsity/output or conjectural conditions. It does not recognize a rational power from ONLY its residue modulo X^m−1. Applying it to F_0 tests a different polynomial; applying it to the full unfolded rational numerator has degree N, exceeding the hidden characteristic and lacking the requisite sparse explicit representation. No known-field oracle or perfect-power result from that source is treated as a native recognition algorithm.

## Source, cost and next exact target

All additional objects actually constructed above—one f² lift, fixed-k flat lifts, and a polylog family of fixed-s automorphism ratios—have charged soft m work for fixed/polylog parameters, including inverses and scalar exponent bit lengths. They preserve the whole-local identities where stated. Their failure to yield j is not evidence of a general lower bound.

The target remains a recognition algorithm for a vector known to satisfy(1), with W low-degree and N public, that finds an asymmetric whole-local permutation or a proper factor in total soft m. A valid short ODE/Padé method must retain the carry in(2)/(6), while a valid automorphism method must turn the family(7) into a source-forced nontrivial equalizer rather than a unit identity. No such recognition theorem or construction was obtained in this pass. The varying j,I native query, original nonzero-annihilator recovery and saturated-hit conditions have not been silently removed.
