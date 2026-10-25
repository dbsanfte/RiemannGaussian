# Actual product acquisition for separately bounded row windows

24 October 2026. A paid execution refinement, not a new worst-case exponent. For acquired unit targets V_j and signed integer windows s_j<=i<s_j+h_j, let S=sum_j h_j. All endpoints have polynomially bounded magnitude and O(log N) bits. The complete product and norm localization cost soft(J+sqrt(S)), including all starts and unequal residual tails. This lets a future proved arithmetic total-width saving translate directly into query work; it does not supply that saving.

## Exact windows from the signed-weight rows

Use the fully initialized signed-weight source `/tmp/semiprime-arithmetic-query-reuse-20261024/signed-two-weight-query.md`, SHA256 `b36e44e9d5e2c897caac87d6ad6339548fd9d438bd21352bd50971ff236efc93`, with H=k^2, the actual pi/q and rows (a,b,ell,V), and SEPARATE public factor bins [B,2B). For each row define the real function

    g(x)=(a*x+b*N/x+ell)/H,  B<=x<=2B.

Its extrema occur at the two endpoints and, only if ab>0, at x=sqrt(bN/a) when that point lies in the closed bin. The critical value is (2 sign(a)*sqrt(abN)+ell)/H. Endpoint values are rational; membership and exact integer floor/ceiling of the quadratic surd are determined by integer square-root/division and sign comparisons, in polynomial(log N) bits. Signed coefficients and a=0 or b=0 pose no difficulty. The pair is nonzero, so no constant-zero polynomial is silently retained as a useful row.

Set s_j=ceil(min g), e_j=floor(max g), and h_j=max(0,e_j-s_j+1). These are acquired O(log N)-bit integers. A zero-length window is omitted. Every own-tag collision in this factor bin remains present, since its index is the INTEGER g(R). Closed endpoints only add candidates. The Gauss/ellipse bound on |a|x+|b|N/x holds uniformly throughout this public bin, so these windows lie inside the earlier conservative signed window. Consequently every selected correct-bin saturated leaf retains the earlier small-integer quadratic decoder guarantee. No cross-bin localization is introduced.

## Acquire all full blocks and unequal tails

If S=0, the product is 1. Otherwise let hmax=max h_j and choose b=min(hmax,ceil(sqrt(S))). Use P_d(X;q)=prod_(0<=t<d)(1-q^t X). Build its actual degree-b coefficient array by a product tree. For n_j=floor(h_j/b), evaluate P_b by monic multipoint evaluation at ALL

    q^(s_j+b*g)*V_j^(-1),  0<=g<n_j.

There are at most S/b such arguments, each actually acquired by unit powering. Their products supply all full blocks. No collision factor or target difference is inverted.

Put r_j=h_j mod b and X_j=q^(s_j+b*n_j)*V_j^(-1). Build the actual polynomials P_(2^d) for 2^d<b. Their total degree is O(b). For every nonzero binary digit d of r_j, acquire and evaluate

    P_(2^d)(q^(r_j mod 2^d)*X_j).

The products of these factors are EXACTLY P_(r_j)(X_j), since the ascending binary pieces tile [0,r_j). At each level monic MPE handles all requested points. The total number of tail points is O(J log b); total polynomial degree is O(b), so all tails cost soft(b+J), including coefficients, offsets, evaluations and products.

The resulting normalized product is prod_j prod_i(1-q^i/V_j). Multiplying by the acquired known unit prod_j V_j^(h_j) gives the exact product prod_j prod_i(V_j-q^i) if desired. Norm gcd decisions are unchanged by this unit. Total work is

    soft(b+S/b+J)=soft(J+sqrt(S)).

For b=hmax<ceil(sqrt(S)), S/b<=J because every h_j<=hmax. This covers the cap branch too. Negative starts use the already known inverse of q. There is no interpolation requiring separated points, no inverse of a zero factor, and no uninitialized terminal amplitude.

## Localization and scope

On norm gcd N, first binary-partition the row list, always following a nonunit child unless a proper gcd has already factored N. Then, for the selected row, binary-partition its own interval. The same product procedure evaluates each restricted query. Every restriction has no larger J or S. Norm multiplicativity supplies a nonunit child; an N-norm leaf vanishes as a whole element at the nonsplit field. There are O(log J+log hmax) restricted calls, absorbed by soft notation. The signed-weight integer quadratic consumer applies to the actual retained labels.

For the current Gauss family, the available proof still gives only S=O(k^(5/2)) up to bin/log factors. Thus the established worst-case cost remains soft k^(5/4). Exact extrema can reduce particular windows but no smaller all-semiprime bound on S, nor a smaller guaranteed covering row subset, was proved in this pass. This report supplies an initialized variable-window interface for a future arithmetic saving; it is not such a saving itself.
