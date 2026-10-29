# Independent review: negative twist lift and acquired deformed family

26 October 2026. Primary formula and exact algebra/cost review. Reviewed the construction supplied in the task message while twist-lift.md was being written; no source/repository edits or numerical experiments.

**PASS for the positive construction, subject to the explicit scope below.** The actual native reciprocal Alexander polynomial can be realized by a binary-encoded connected sum of negative twist knots, and the entire one-parameter deformed LG family on the fixed adjacent-pair hyperbola can be acquired in soft L. This does not prove its zero predicate is the native one or acquire the original prefix.

## Native factor and knot choice

On the already screened native branch, each supplied v_j is a unit and v_j-1 is a unit. Consequently

    c_j=-v_j/(v_j-1)^2

is a unit. With w(T)=T+T^-1-2,

    1+c_j*w(T)
      =(T+T^-1-v_j-v_j^-1)/(2-v_j-v_j^-1).

Multiplying these normalized factors gives exactly the acquired native K(T), not just a polynomial with the same zero set. Choose the unique negative integer n_j in [-N,-1] representing c_j; since c_j is a unit it is nonzero modulo N, so in fact n_j lies in [-N+1,-1]. Put s_j=-n_j>=1. Each integer has O(log N) bits.

Kohli Proposition 2.18 uses the twist convention K_0=unknot, K_1=trefoil and gives the reciprocal Alexander polynomial

    Delta_(K_n)(T)=n*T-(2n-1)+n*T^-1=1+n*w(T).

Thus n_j congruent c_j has the correct sign. The connected sum of these genuine twist knots has Alexander polynomial congruent to K(T) over R. Its integral Alexander polynomial need not equal a separately chosen integer lift of K; modular equality is precisely what is needed here. The familiar block V_n=[[n,0],[-1,1]] also verifies the reciprocal determinant directly:

    T^-1 det(T V_n-V_n^T)=1+n*w(T).

The construction specifies an actual knot by binary twist data; it does not acquire its fully expanded crossing diagram in soft L. Using Kohli's closed formula below avoids that expansion for the claimed scalar acquisition. Connected-sum multiplicativity is explicitly stated in Kohli Proposition 2.5.

## Primary negative-branch formula and exact simplification

Checked https://arxiv.org/pdf/2505.08296 , Corollary 2.12 (a_1 definition), Proposition 2.18 negative branch n<=-1, its concluding Alexander specialization, and Proposition 2.5. Let a=t_0,b=t_1,u=ab and B=(a-1)(b-1). The source has

    a_1(s)=(u^s-1)/(u-1)=A_s,
    LG(K_-s)=(a^-1-1)(b^-1-1)
       *[A_s+B*((u+1)A_s-2s)/(u-1)] + B*A_s+1.

Since (a^-1-1)(b^-1-1)=B/u, this is exactly

    F_-s(B)=1+(1+u^-1)A_s*B+u^-1 H_s*B²,
    H_s=((u+1)A_s-2s)/(u-1).                         (1)

For s=1, A_1=H_1=1, giving the figure-eight polynomial 1+(1+u^-1)B+u^-1 B²; this matches its independent primary LG formula and fixes the negative-branch sign. Equation (1) is the source normalization unknot=1, with no additional modified-dimension quotient.

The quotients defining A_s,H_s are actually integer polynomials in u: A_s is the finite geometric sum and the numerator of H_s vanishes at u=1. More usefully, the following binary recurrences compute them without dividing by u-1 at all.

## Division-free binary acquisition

Track (s,v_s,A_s,H_s), where v_s=u^s. The polynomial concatenation identities are

    v_(s+t)=v_s*v_t,
    A_(s+t)=A_s+v_s*A_t,
    H_(s+t)=H_s+v_s*H_t+2t*A_s.                      (2)

The last equation follows after multiplying through by u-1 and using (u-1)A_s=v_s-1. It is a polynomial identity, so remains true when u-1 is a zero divisor or zero. Seeds are

    (v_0,A_0,H_0)=(1,0,0), (v_1,A_1,H_1)=(u,1,1).

In particular doubling and incrementing give

    A_2s=(1+v_s)A_s,
    H_2s=(1+v_s)H_s+2s*A_s,
    v_2s=v_s²,

    A_(s+1)=A_s+v_s,
    H_(s+1)=H_s+(u+1)A_s+1,
    v_(s+1)=u*v_s.

These evaluate (1)'s coefficients in O(log s) ring operations. Only u^-1 is used in (1), and u is a known unit; no Alexander value or collision difference is inverted. The integer s may be maintained modulo N for coefficient multipliers, while its O(log N)-bit binary word controls the recurrences. The canonical integer lift is part of the actual knot choice: changing n by N generally changes u^s and hence LG, even though it leaves the modular Alexander polynomial unchanged.

For every native pair in the chosen reciprocal orientation,

    a_i=eta^(2i+1), b_i=eta^(-2i-3), u=q^-1,
    B_i=(a_i-1)(b_i-1).

The same u is shared by every i and every twist block. Acquire the L quadratic factors (1), then form

    H_native(B)=product_j F_-s_j(B).

A balanced product tree acquires its degree-at-most-2L coefficient list in soft O(L), after soft O(L log N) ring work for binary coefficients, absorbed in the stated soft bound. Storage is soft L, and every scalar family value of this specifically chosen connected-sum knot equals H_native(B_i). The native u-1 is also a unit, but the recurrence proof does not need it. Neither a constant-sized color description nor a crossing expansion is being counted as a scalar algorithm: the full polynomial coefficients are explicitly acquired.

## Original pair and remaining distinction

For one twist block n=-s, the desired adjacent Alexander pair is

    P_-s(B)=1-s*(u-1)^2/u+s*(1+u^-1)B+s²*B²/u.

Indeed w(a)+w(b)=(u-1)^2/u-(1+u^-1)B and w(a)w(b)=B²/u. Therefore

    F_-s-P_-s
      =s*(u-1)^2/u +(1+u^-1)(A_s-s)B
           +(H_s-s²)*B²/u.                           (3)

At u=1, A_s=s and H_s=s², so both become (1+sB)^2. At the actual u=q^-1 with large odd order, equation (3) is a real scalar correction, not a removable normalization. Its zeros or units cannot be inferred from the existence of the acquired coefficient list. The earlier figure-eight diagnostic already excludes the universal assertion that the coupled scalar preserves every Alexander-product zero; it is not a certified attained full native-catalogue counterexample.

Thus this is a meaningful paid native-input construction and acquisition of the full DEFORMED scalar family. It does not acquire the many-point odd-weight prefix, establish equality of its zero/nonunit bit with the target, or improve the factoring exponent. Those limitations are essential to the reviewed positive statement.

## Final full-file reread

Reread the completed twist-lift.md after its creation. Its additional finite-sum definition of H_s, concatenation formula, negative representative bounds, common-u family, exact correction and tail handling all pass. In particular cbar_j in [1,N-1] gives s_j=N-cbar_j in [1,N-1], not zero; s_j mod N is a unit. The acquired product F has degree at most 2L even when individual leading coefficients are nonunits. Acquiring all its coefficients is explicitly charged; no full prefix or collision predicate is claimed. Disjoint pairs are indexed i=1,3,5,..., so they do not double-count overlapping adjacent factors. If m is odd, the final K(eta^(2m+1)) factor can be evaluated directly at soft L cost, with the same original-label recovery contract if used by the original consumer.

One wording clarification is advisable in Section 1: after defining the actual connected-sum knot C, “The block-diagonal Seifert presentation has size 2L and 3L nonzero entries” can read as asserting that the independently displayed V_n is a Seifert matrix for Kohli's exact T_n, solely from the Alexander determinant match. Equality of Alexander polynomials does not by itself establish that identification. It suffices to call it the independently constructed block-diagonal matrix realizing the same modular Alexander polynomial. The actual knot C is unambiguously supplied by the binary twist list and the source's twist-knot formula; its scalar acquisition does not need any V_n-to-T_n topological identification. Alternatively one can supply the ordinary band-surface verification for the chosen twist convention. This is a presentation/justification issue, not a failure of the paid knot choice or the scalar algorithm.

Final disposition: PASS for the supplied native knot choice and full deformed-family acquisition; preserve the matrix-versus-knot distinction just described. No original-query speedup is asserted or obtained.

## Authorized final wording correction

Corrected only the scratch twist-lift.md: the block-diagonal V_(n_j) independently realizes the same modular Alexander polynomial; equality of that polynomial does not identify it with a Seifert matrix for Kohli's exact T_n convention. The actual C is specified by the O(L log N)-bit binary twist list, and its scalar algorithm uses the source formula without any matrix-to-knot identification.

Final material check: negative representatives remain nonzero and in [-N+1,-1]; the division-free A_s,H_s recurrences and shared u=q^-1 give the complete degree-at-most-2L deformed scalar polynomial in soft L bit cost. This bound includes residue arithmetic and log N-bit twist counts through soft factors; it does not cover expanded diagrams or expanded integer polynomial coefficients. The original collision predicate, full orbit product and a new exponent remain unproved and are explicitly not claimed. No further material algebra or complexity caveat found. Final disposition: PASS for precisely the stated native knot choice and deformed-family acquisition.
