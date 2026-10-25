# Dyadic native rows and exact rational Graeffe interface

22 October 2026. Independent arithmetic audit; no repository edits, backend or examples. Let m=2^k>=4, m>=ceil(N^(1/6)), and retain odd distinct-prime N=P Q with P,Q>16m². The power-of-two scale can be chosen within a factor2; this selector fact alone is not a collision-query improvement.

## Canonical source, integer bounds and antipodal carry

Use odd unit tags j modulo m. Let a be the representative of N*j^-2 modulo m in [1,m), hence odd. Define b as the unique centered representative in [-m/2,m/2) of ((a*j²-N)/m)*j^-1 modulo m. Let c=(N+jmb-j²a)/m², ellrow=mb-2aj and E=N+a+ellrow. All divisions are exact because j is a unit; no inverse of2 is used.

For the true tag P=j+mh,

    P*(aP+Q+ellrow)=m²*(a h²+b h+c).

Since P is coprime to m² this proves I=(aP+Q+ellrow)/m² is an integer and E-m²I=(P-1)(Q-a). Thus the original scalar Fermat coverage survives unchanged for even m. With the half-open centering, |b|<=m/2, |ellrow|<3m² and -3m²<=a+ellrow<=m². P<=m³, Q<m⁴/16 then give 13<I<(17/16)m²+3<4m², without balance. E>=N-3m² and N>256m⁴ give positive O(log N)-bit scalar leaf gaps for the same native/paid boundary ranges as before.

For j'=m-j, a'=a and b' =2a-b-ms for a unique integer s. Bounds on the TWO centered representatives give s in {0,1,2}, including midpoint cases b=-m/2. Hence ellrow'=-ellrow-m²s exactly. One must NOT replace b' by -b. There are phi(m)/2 distinct pairs for m>=4; m=2 has a fixed unit tag and needs finite handling.

Prepared gamma has odd local orders, so q=gamma^(m²) has EXACTLY the same local orders. Here no small-q-order screen is necessary to repair powering loss, though the existing screen remains valid. Original annihilator/decoder hypotheses are unchanged. No even-order Gauss pairing formula is imported: the rational W carrier below needs no Gauss auxiliary.

## Exact even-modulus colors

The discriminant identity ellrow²-4aN=m²(b²-4ac) remains true, but 4aj is NOT invertible modulo m. The previous kappa=-Delta/(4aj) formula and its lifted v must not be imported.

The exact true residue image is I=j^-1(a h²+b h+c) modulo m. It has a particularly small public classification:

* If b is ODD, the image is exactly the parity class I=c/j modulo2. Modulo2 the polynomial is constant; its derivative2ah+b is odd, so each of the two starting h parities lifts uniquely for every compatible output. Thus every compatible output has exactly two preimages modulo m, and the image has m/2 residues.
* If b is EVEN, set d=b/2 as an ordinary integer and use the unit inverse of a. Then the image is exactly kappa+lambda Squares(Z/m), with kappa=j^-1(c-a^-1*d²) and lambda=a/j. This completion uses b/2, not an inverse of2 or4.

For k>=3, unit squareclasses modulo2^k are the four odd classes modulo8. Enumerate one square image and its four unit multiples; their total output is O(m), even allowing overlap in high-valuation strata. Add the two parity palettes for the odd-b branch. Public enumeration of all squares and sorting gives the complete constant-size palette menu and all row assignments in softm. For m=4 the two unit classes and direct finite square image suffice. Ordered-subset boundary MPE applies independently of primality, with these actual palette lists and original scalar leaf ledgers.

## W units and weighted trace correction

Let t²=gamma be the already paid scalar root and

    W_(gamma,t)(X)=t(1+gamma X)/(X+gamma),
    A_m=(Z/N)[X]/(X^m-1), bar(X)=X^-1.

W bar(W)=gamma algebraically for every m. For EVEN m,

    Norm(X+gamma)=gamma^m-1,
    Norm(X)=-1,
    Norm(W)=-t^m.

Odd local orders make gamma^m-1 a unit, since a nontrivial odd order cannot divide the power of two m. The numerator is a unit too: its norm is 1-gamma^m. Check gcds if the retained order contract has not been established.

The weighted rational-trace proof and its extra U0 precision remain valid. Its quadratic h at z=0 is X(X+gamma), so Norm_quadratic(1-X^m) is NOW 1-gamma^m, instead of1+gamma^m. The determinant denominator Norm(g), g=X(X+gamma), is also1-gamma^m. The quadratic resultant numerator p^m-S_m+1, regular trace m*CT, exact U0=ztV(0) and precision z^(m+1) for U0/z do not change. No hidden characteristic-two algebra is used: the scalar characteristics P,Q are still odd and m is a unit modulo N.

## Genuine rank-halving rational norm closure

There is an exact finite-fiber identity

    W_(gamma,t)(X) W_(gamma,t)(-X)
      =gamma*(1-gamma² X²)/(gamma²-X²)
      =W_(gamma²,gamma)(-X²).                  (G)

For m>=4, U=-X² obeys U^(m/2)=1 because m/2 is even. Thus the rational family REALLY closes under one Graeffe norm, with rank halved, gamma replaced by gamma² and its known scalar root replaced by gamma. The final rank2 to rank1 step has U=-1 rather than1 and must retain that terminal sign/twist. Denominators stay units because all successive scalar parameters are powers of the original odd-order gamma.

For odd j, the norm commutes with rho_j: (-X²)^j=-X^(2j). Therefore norming a corrected target produces the SAME FORM with the inherited integer a_j,ellrow_j,N and reduced automorphism tag j modulo m/2. Whole-local-algebra own-tag equality is preserved forward under this norm. The exponent in its seed is STILL original m², and inherited coefficients are not the canonical reduced-modulus representatives. One may rewrite the row relation at modulus m/2 with b_new=2b,c_new=4c, but cannot replace its a/ell/index with freshly centered canonical data for free.

This is a finite-fiber acquisition interface, not merely a congruence description. A supplied ONE rational packed element can be normed by even/odd splitting and polynomial multiplication at its actual degree. Applying it to the whole native leaf family still requires a shared contraction; no m separate packed targets are assumed acquired.

Crucially this fiber involution X->-X is NOT automatically a native tag pairing j->j+m/2 in the full cyclic algebra. The latter identification holds only on primitive components where X^(m/2)=-1. Lower-order components remain in A_m and must not be discarded. Antipodal j->-j is instead bar, a different involution. Norm of a DIFFERENCE also detects an OR of fiber zeros; it does not certify both factors vanish at the same original leaf. A controller must preserve the original same-leaf scalar recovery condition or establish a separate valid norm-localization theorem.

The full norm of a target alone is (-t^m)^E, and of its seed is (-t^m)^(m²I). E is even (N,a odd and ellrow even), so equality of these whole-element norms implies t^[m(E-m²I)]=1. Odd scalar orders and dyadic m then give the original gamma annihilator for the SAME nonzero gap. This is a forward WHOLE-equality recovery implication, not an inverse or a norm-zero inference.

## Audit endpoint

The classical native source, all-factor bounds, original decoder and a constant-menu exact even-modulus color classification survive. Rational W admits genuine dyadic norm closure (G), and the weighted-trace primitive needs only its explicitly identified unit-sign replacement. This is a valid new contraction interface for the other agent to exploit. It does not yet acquire the full collision query: same-leaf support under difference norms, inherited row metadata/seed stride, all lower-order components and total shared arithmetic remain to be handled. No selector, norm identity or paid trace is promoted to a completed near-linear controller.
