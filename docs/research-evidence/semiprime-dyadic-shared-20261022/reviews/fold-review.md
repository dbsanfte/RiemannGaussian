# Independent fused-fold review and a shared resultant carrier

The first coefficient-first/spatial-first contraction in additive-contraction.md (7)–(9) is algebraically correct on its stated primitive component. This is stronger than merely splitting the original spatial weight into parity parts. This review does not establish a closed near-linear evaluator.

## Verified first update

Put d=m/2, Y=X^2, u=b^-1, and C_k=B_k-B_(k+d). Pairing k with k+d first, then retaining odd outputs, gives

 G(Z)=CT_X sum_(k<d) C_k R(X)X^(uk)/(1-Z R(X)^2Y^(uk)).

Writing R=r0+Xr1, P=R(X)R(-X), S=2r0, A=S^2-2P, relative trace yields

 K_even(s,Y)=r0(1-sP)/(1-sA+s^2P^2),
 K_odd(s,Y)=Y r1(1+sP)/(1-sA+s^2P^2).

The normalization is right: these are averages of R/(1-sR^2) and XR/(1-sR^2), respectively. Therefore the contracted expression is

 CT_Y sum C_k Y^floor(uk/2) K_(k mod2)(Z Y^(uk),Y).

The coefficient list has genuinely halved. In particular it is wrong to dismiss this step merely because the original orbit numerator had m^2 entries. Splitting k=2l+epsilon leaves the affine exponent u*l*(2n+1), rather than the synchronized u*l*n of the starting state. That affine tag must remain in the recursive invariant.

## A useful degree invariant for ONE shared carrier

Write R=f/g with f=t(1+gamma X), g=X(X+gamma). At a d-fold spatial contraction, where d is a power of two and Y=X^d, a natural shared power carrier has denominator

 D_d(s,Y)=Res_X(X^d-Y, g(X)^d-s f(X)^d).

This is the norm denominator for 1/(1-s R(X)^d). Its s-degree is at most d and Y-degree at most 2d: the latter follows directly by evaluating the resultant as a polynomial in Y with second input of X-degree 2d. Thus it is not legitimate to charge its full degree as m^2 at every level.

If the remaining output precision is p=ceil(m/d), then its explicit truncated coefficient rectangle has O(d*min(d+1,p))=O(m+d) entries. For d<=sqrt(m), the full rectangle is O(d^2)<=O(m); for d>=sqrt(m), truncation gives O(dp)=O(m). This is a positive size invariant for ONE denominator, including the genuine cyclic spatial norm. It suggests truncation-first shared resultant arithmetic rather than independent power-vector construction.

This size bound is not yet an acquisition bound: a fast resultant/norm algorithm respecting the s-prefix and the stated total O(m) rectangle must be supplied. Nor does the bound acquire all moving numerators. It does rule out using the degree of an unnecessary full carrier as the stopping argument.

## Where the invariant still needs an algorithm

The scalar output class after repeated odd/even extraction has a=d*n+r. The coefficient modulation is consequently X^(u*k*r) Y^(u*k*n). At the same time the power numerator contains R(X)^r and the relevant coefficient-list branch. The residues r cannot be silently identified, even though their norm denominator may be shared. Coefficient parity extraction generates distinct modulated lists and spatial parity extraction generates distinct trace numerators. Keeping them as a single unevaluated sum does not pay their final contractions.

A closed affine-tag state therefore needs four explicit data contracts:

* one common truncated carrier, with a proved construction/update cost;
* the coefficient-list transforms and their total size across branches;
* compressed numerators indexed by affine residue r, with the cost of multiplying by the opposite-fiber denominator before tracing;
* an actual contraction algorithm for the final coefficients, not just their norm or straight-line expression.

The first-step formulas meet these contracts at constant branch count. I could not prove that all subsequent numerator branches have total O(m polylog m) size AND update cost. In particular the one-carrier bound above cannot be multiplied by the number of residue classes and still called near-linear. Conversely the need to write one numerator per class is not proved: exploiting their common rational source is exactly the promising shared step.

For a native query, all lower-order cyclic strata must also be retained, with their normalized trace weights. Their initial ranks form a geometric sum, so an actually near-linear per-rank algorithm would combine at soft O(m). The remaining native W_j^ell factor and seed I are separate obligations; acquisition of H_a alone is not a factorization theorem.

## Review outcome and precise next construction

PASS for the first fused fold, including parity signs, trace normalization and scalar-list halving. A potentially useful additional invariant is the O(m) truncated size of its d-fold shared resultant carrier. No proof of the full affine-tag numerator closure or its arithmetic acquisition was obtained.

The narrow next construction is to compute, simultaneously for all required residues r, the appropriately weighted relative-trace numerators over that shared D_d, while charging total coefficient/list/precision work rather than a separate O(m) carrier operation per residue. A proof of that interface would move this branch beyond a valid first-step identity. This report makes no lower-bound assertion and does not count a compressed norm description as a fast contraction.
