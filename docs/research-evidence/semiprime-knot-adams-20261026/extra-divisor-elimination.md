# Complete-family removal of extra zeros: common-unit skein channel and remaining norm

26 October 2026. Constructive finite algebra pass. Scratch only; no numerical experiments or repository edits. Prior inputs are fractional-twist.md, the fixed three-state skein basis, the paid native roots, and the new Frobenius order-coprimality screen.

**Positive complete-family identity.** The extra divisor can be replaced by one common factor B that is a certified unit at EVERY physical clock, using a lawful finite skein combination. Its ENTIRE scalar correction product is acquired by two ordinary scalar q-factorials in soft(L+sqrt m), including normalization. This removes extraneous zeros globally, without an invalid inference from rowwise common zeros to global product common zeros. It does not yet compute the resulting skein norm: after that cheap correction the remaining scalar is exactly the original prefix. No less-than-soft-sqrt(Lm) complete query has been derived.

## 1. Inputs and lawful common-extra interpolation

Let u=q^-1, alpha=(u+1)/u, beta=u^-1. The supplied odd-order groups make 2,u,u+1 units. The three fixed twist-skein states satisfy

    F_0=1,
    D_1=F_1-1=alpha B+beta B²,
    D_2=F_2-1=alpha(u+1)B+beta(u+3)B².

Their coefficient determinant 2(u+1)/u² is a unit. Thus

    B=[(u+3)D_1-D_2]/(2alpha),
    B²=[D_2-(u+1)D_1]/(2beta).                      (1)

This is the previously proved local basis, but the choice and entire-clock normalization below are new to this elimination test. For any acquired root orientation v put

    w_v=1+u-v-u/v.

The lawful finite skein element

    H_v(B)=B²-w_v B=B(B-w_v)                         (2)

is explicitly obtained from (1), using only 2,u,u+1 inverses. Unlike forcing the formal exponent U on its constrained one-parameter curve, this permits the second root to be fixed at zero independently of v. No topological knot realization or generic representation theorem is required: a finite scalar linear combination of the three fixed normalized skein states is enough. Every coefficient is acquired in O(1) work per supplied orientation, including all degenerate cases of the earlier fractional-U target denominator.

Equivalently one can use the direct linear element B-w_v, which has no extra root. Equation (2) is useful because it demonstrates a common divisor whose whole physical norm is explicitly cheap, rather than requiring a new unit test at every row and index.

Primary normalization input remains Kohli's negative-twist formula, Proposition 2.18 and the previously audited three-state algebra: https://arxiv.org/pdf/2505.08296 . All claims beyond that are exact finite polynomial identities.

## 2. Native complete-family scalar identity

For each of the L supplied reciprocal rows retain BOTH orientations v_j and v_j^-1. Write s_j=v_j/(v_j-1)^2, a known unit, and

    M(B)=product_j (B-w_(v_j))(B-w_(v_j^-1)),
    P_native(B)=product_j P_(s_j)(B),
    P_s(B)=1-s*(u-1)²/u+s*(1+u^-1)B+s²B²/u.

The exact root factorization is P_native=D*M, where

    D=(product_j s_j²)/u^L

is an explicitly acquired unit. Consequently

    H_native(B):=product_j H_(v_j)(B)H_(v_j^-1)(B)
      =B^(2L)*D^-1*P_native(B).                     (3)

All coefficients of H_native, M and P_native are acquired in soft L by balanced product trees; their degrees are at most 4L, exactly 2L and exactly 2L respectively, with unit leading coefficients. This is a whole native coefficient identity. It does not multiply scalar invariants of incompatible knot inputs or assume a generic knot expectation preserves a determinant identity.

Now use n=floor(m/2) disjoint adjacent pairs:

    a_h=eta³*q^(2h), b_h=eta^-5*q^(-2h),
    B_h=(a_h-1)(b_h-1), 0<=h<n.

Both exponents 4h+3 and -4h-5 are nonzero in the supplied short eta-order window. Hence each B_h is a CERTIFIED unit. There is no separate extra-root collision to locate. Taking the complete physical product of (3) gives

    product_h H_native(B_h)
      =D^-n * U_clock^(2L) * product_h P_native(B_h),
    U_clock=product_h B_h.                           (4)

The prefactor in (4) is a unit globally, so the zero AND nonunit predicates are exactly equivalent over the composite ring. This statement does not need squarefreeness because multiplication by a unit preserves both predicates. A final unpaired original factor when m is odd is evaluated directly in soft L.

## 3. Pay for the complete correction, not just its descriptor

The entire scalar U_clock is exactly

    U_clock=(eta³;q²)_n * (eta^-5;q^-2)_n,            (5)

where (z;r)_n=product_(h=0)^(n-1)(1-z r^h). The two minus signs in B_h cancel. Both are scalar q-factorials, with known unit starts and steps. The standard initialized product-tree/monic-multipoint baby-step/giant-step algorithm acquires each in soft sqrt(n) ring operations over R, without any point-difference inverse. Their factors are already certified units by the native exponent guard; it does not infer that condition from a possibly singular norm. Acquiring D costs soft L, and powering U_clock^(2L), D^n costs only polylogarithmically many further ring operations.

Thus the COMPLETE correction in (4) costs soft(L+sqrt m), with no L-by-m support enumeration. This is a genuine scalar normalization result at the requested scale. It does not acquire the left-hand norm in that cost. Evaluating H_native at all those points by the existing compressed geometric algorithm costs soft(L+sqrt(Lm)), up to constant degrees and pair length; its Laurent pullback along a_h has constant-factor degree O(L). Dividing by the known unit prefactor then returns precisely the original prefix at that existing cost.

The conclusion is deliberately different from merely leaving an extra divisor formal: the divisor has been made common, all its physical values are known units, and its whole scalar has been acquired. The remaining difficulty is entirely the original interaction norm, with no new decoder defect attached.

## 4. Why multiple channel products do not automatically eliminate extras

For the earlier forced-U scalar J_v=(B-w_v)*ell_v, consider perturbed channels

    J_(v,lambda)=(B-w_v)*[ell_v+lambda(B-w_v)].

At a single row/index, two distinct lambda with unit difference have a common zero only when B=w_v (fieldwise). This can be useful if both values are acquired at that SAME leaf. It is insufficient after taking products over all rows and clocks: distinct channels can vanish at different leaves.

The simplest exact logical counterexample is the two-leaf affine factors E_1(lambda)=lambda and E_2(lambda)=lambda-1 over a field. Their global product vanishes at lambda=0 and1, although neither leaf vanishes at both. This is an algebraic diagnosis of the channel-product inference, not a claim that those two leaves are attained by the native catalogue. A physical family with an additional genuine common leaf still permits a search algorithm to follow an extra-only subblock and require backtracking; local uniqueness alone supplies no polylogarithmic bound on that search.

More generally if there are D leaf factors affine in lambda, each nonoriginal leaf with nonzero slope excludes at most one lambda over a field. A list longer than D can avoid all such zeros, but D is of order Lm here and the acquisition/query costs exceed the target. Zero slopes and composite-ring components require additional branches. This is only a bound for that explicit finite-channel covering argument, not a complexity lower bound or a proof that a polylog native-specific list cannot work.

## 5. Resultants, Bezout, and determinants: exact location of the readout

If two extra polynomials E_0(B),E_1(B) have unit resultant, polynomial Bezout coefficients can certify their lack of common zero at one common B. One must acquire both the resultant certificate and the coefficients over R, with guarded pivots or a division-free algorithm. Unit resultant does not justify replacing

    product_h [A(B_h)J_0(B_h)+C(B_h)J_1(B_h)]

by a constant-number linear combination of product_h J_0(B_h) and product_h J_1(B_h). Expansion has mixed channel assignments at different indices. The expression on the left is simply a new known coefficient polynomial followed by its unacquired long norm. Distinct native rows can also contribute common roots between their extras even if each individual row's two extras are disjoint; unit resultant for the whole product is an additional obligation.

The common-unit construction (2) avoids both problems more directly than this Bezout trial. It acquires a zero-equivalent whole-family polynomial and a cheap, safe scalar correction. A determinant lemma for the resulting norm would still need an initialized inverse or Green kernel for the original varying-clock interaction; a constant-rank row presentation is not that inverse. No such primitive is assumed or established here.

An alternative channel polynomial in a formal perturbation parameter has original products among its coefficients, but acquiring those far coefficients is exactly the scalar readout. Evaluating at a constant/polylogarithmic number of parameters does not by itself extract them; retaining all mixed assignments or a degree-Lm perturbation expansion exceeds the desired size. This is scoped to that direct interpolation approach.

## 6. Recovery and strengthened Frobenius interface

Equation (4) gives a stronger recovery guarantee than the original fractional-U product: no extra scalar zeros remain. At a localized H_v(B_h) zero, B_h is a unit, so B_h-w_v is nonunit. The exact identity

    B(a)-B(v)=-(a-v)(a-u/v)/a

maps it to a genuine original row at the first argument a, or b=u/a at the second argument. Proper gcds factor; a saturated genuine difference retains its original signed label and nonzero O(log N)-bit gap for the licensed short-annihilator extractor. Monic product queries remain restriction-stable, so the same construction can be used during row/index localization if its norm is acquired. At the formal positive endpoint, retain the actual opposite-row metadata: if v=x/eta=t_i, use x'=q/x=q^(-i); if v=t_i^(-1), use x=q^(-i). The second member of the pair uses i+1. Thus the apparent m+1 endpoint maps to the legal negative index -m. See extra-divisor-review.md for all four orientation cases and the odd-tail case. Original pair signs and the odd tail remain explicit.

After the paid Frobenius screen, N-th powering is a bijection of all relevant local subgroups. The construction above needs no inverse exponent, membership oracle or logarithm and does not treat N-th powering as additive. Its coefficient linear combinations are ordinary ring operations, lawful independently of that stronger group interface.

The precise useful remaining primitive is now the zero/nonunit norm of the acquired common-unit skein polynomial H_native(B_h), or equivalently of its directly recovered monic factors, in soft(L+sqrt m). Its coefficient input, common scalar correction, finite-ring legality and original-leaf readout are all paid here. This pass solves the extra-divisor normalization/decoding issue constructively, while leaving the full-query acquisition at the existing soft(L+sqrt(Lm)) bound. No new factoring exponent or broader obstruction is claimed.
