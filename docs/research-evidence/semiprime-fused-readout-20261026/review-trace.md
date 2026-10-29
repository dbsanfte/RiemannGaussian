# Independent review of structured-trace.md

26 October 2026. Paper-only algebra, ring-guard and initialized-cost review. No tests or repository changes. **PASS: no formula correction found.**

## Displacement and exact eigenbasis

For a column e<B-1, C L-Z C R vanishes by

    (1-Z_s rho^{e+1})a_{Bs+e+1}
      =(A-Z_s rho^e)a_{Bs+e}.

The last column is -(A-Z_s rho^{B-1})a_{Bs+B-1}=d_s. Thus C T-Z C=d v^t has the displayed sign and boundary a_{B(s+1)}.

For the kth lower-Toeplitz column of V, L V=R V diag(A rho^{-k}) gives exactly

    s_r/s_{r-1}=(1-A rho^r)/(A(1-rho^r)).

Therefore P=R V, not V alone, diagonalizes T. All denominator factors 1-rho^r are short certified units; V has constant diagonal one, and R has unit diagonal. Hence convolution/series inversion and bidiagonal solves really pay both P and P^{-1} actions over the composite coefficient algebra. Zero numerator coefficients do not affect that conclusion.

The Cauchy denominator is eta_k-Z_s, with exponent difference h-k-Bs. If h=BM+r, its smallest value is r+1 and largest h. These are precisely in the supplied unit range. The Cauchy numerator w_k=s_{B-1-k} follows from v^t P=e_last^t V. No native root difference is inverted.

## Actual geometric-vector transform and dual trace

Solving R v=u(y) gives v_e=-sum_{t=0}^e(y/rho)^t. Toeplitz inversion then yields exactly

    sum Psi_k(y)z^k=-1/[S0(z)(1-z)(1-yz/rho)] mod z^B.

Its sign and rho placement are correct. For T(z)=1/[S0(z)(1-z)], the defining s_r recurrence gives

    (1-rho^{-h}z)T(rho z)=(1-z)T(z) mod z^B.

The finite product product_{r=1}^h(1-rho^{-r}z) satisfies the same relation and constant term; coefficient comparison uses only 1-rho^k, k<B. Thus the asserted short multiplier identity is finite and ring-safe, even if numerator factors outside the short unit screen vanish.

For T Y-Y Z=H, the Cauchy cross-gap guards give unique solvability entrywise after the paid P transform. Rectangular trace cyclicity gives

    tr(C H)=tr((C T-Z C)Y)=v^t Y d.

This proves the dual formula and all signs in (7). Its actual RHS remains the sum of J same-root rank-one terms. Applying the explicit Cauchy sum separately to each costs soft J(B+M); neither the Toeplitz transform nor the Sylvester equation supplies a free matched trace.

## Linked product and finite kernel cancellation

With Z'=sigma Z, E=T H-H Z' has exactly the width-at-most-2J decomposition in (9). Direct multiplication gives

    Z C H-C H Z'=C E-d v^t H.

Since sigma=rho^B, every diagonal divisor Z_s(1-sigma) is certified a unit. The linked-generator method can therefore be executed with the claimed cost, and substitution of E indeed gives back the same diagonal identity. Width at most 2J is merely an acquired representation, not a minimal-rank or complexity lower bound.

In (11), the constant coefficient is alpha_s(1-Z_s), every interior coefficient cancels by the ratio recurrence, and the degree-B term is exactly d_s y^B. After multiplication by y^{Bs}, adjacent boundary terms cancel because d_{s-1}=-(1-Z_s)alpha_s. The leftover is -(1-rho^{BM})a_{BM}y^{BM}. Restoring precisely the tails BM,...,BM+r=h cancels that boundary and leaves

    (1-rho^h y)G_h(y)=(1-y)G_h(rho y).

This is the correct endpoint relation for the actual finite product. It provides a shifted alphabet, not a supplied value at that alphabet. The native good-family one-step separation is sufficient to exclude a hidden root permutation here; this does not claim arbitrary q-shifts are disjoint. No factor is divided out at a possible collision.

## Arbitrary h and all starts/tails

For h=BM+r, the block factorial table at offset zero gives f_{Bs}; a second table at residue offset r gives f_{B(M-s)+r}. Together with f_r and f_h this acquires every coefficient start. The residual r+1 a-values use the same short ratio/factorial data. A shifted recurrence sequence can acquire b_{BM},...,b_{BM+r} by first computing X^{BM} mod F and then its finite recurrence extension. Hence soft(J+B+M) for starts and exact tails is justified. The initial special case r=1 has exactly the two tails h-1,h. No uncharged arbitrary long factorial stream is required.

The complete trace route costs soft(J(B+M)+J+B+M), minimized at B about sqrt h, or one can use a full soft(h+J) coefficient stream. In h>J these do not beat the stated existing shared-product bound. This is a ledger for the executed algorithms, not a scalar-query lower bound. The fixed-F linear-circuit transposition consequence is correctly kept separate from nonlinear weak norm/ratio output.

**Disposition:** accept P=RV, the explicit inverse action, all Cauchy gap guards, dual and linked-displacement formulas, finite q-kernel boundary cancellation and arbitrary-h start/tail initialization. No faster paired trace or full-query acquisition is established.

## Applied disposition

The primary agent clarified that directly supplied row weights need no spectral interpolation or separated roots; the resulting linear pairing does not compute the nonlinear hit mask. The reviewed formulas and cost are unchanged.
