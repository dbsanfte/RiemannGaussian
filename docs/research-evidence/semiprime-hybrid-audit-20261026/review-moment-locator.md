# Independent review of moment-locator.md

26 October 2026. Read-only cross-review against the frozen
`semiprime-cofactor-recurrence-20261024/cofactor-contraction.md`,
`semiprime-quotient-gradient-20261024/weak-readout.md` interface as
quoted in the audit, and the directly reread Oct26
`bispectral-string.md` and `exact-string.md`. No tests or source edits.

**Scoped PASS on the finite algebra and hybrid-interface conclusion.**
Two wording/index clarifications should be integrated; neither changes
the calculation.

1. Replace “strictly less than acquiring the full product” in the
opening by “a weaker requested output specification than acquiring
the full product (no computational separation is proved).” The actual
projective pair remains an uninitialized contraction; the report does
not establish a lower cost or reduction in the opposite direction.

2. In Section 4 define the retained TQ factor with its exact source
indices. On the n-point reindexed string it is
`P_ret=product_(i=2)^n F(x_(i-1))`, not a product that silently omits
both endpoints. The first endpoint is supplied by `T_0(F)=F(x_0)`.
The last endpoint is INCLUDED in P_ret, though it may have been
screened a unit to make the good hit strictly interior. Calling this
“interior” is harmless only with that explicit convention. Removing
the last endpoint and simultaneously keeping C independent of F and
T linear in F would require an extra accounted F(x_(n-1)) factor.

## Checks executed by hand

- The old derivative gives
  `lambda_i=(-1)^i q^[-im+i(i+1)/2]/[(q;q)_i(q;q)_(m-i)]`.
  Multiplication by `(q;q)_m*x_i^(-m)` is exactly the reported
  `nu_i`, including the second `-mi` in its exponent. There is no
  missing monomial or sign in equation (1).

- For integer s>=0 with J+s<m, Lagrange interpolation of
  `X^s F(X)` on m+1 unit-separated nodes gives the aligned
  `mu_(m+s)=0`. Equivalently
  `B_t=(q^(t+1-2m);q)_m` contains a factor `1-q^0` precisely
  throughout t=m,...,2m-1; all relevant j+m+s lie in this band.
  Thus the executed candidate pair is indeed (0,0) on the actual
  good-side input, not merely a generic illustrative example.

- The full Hankel determinant is
  `D_clock*product_i F(x_i)` by the square Vandermonde factorization.
  D_clock is a unit and independent of F. Its first derivatives
  in directions 1 and X are exactly D_clock times the old
  unweighted complementary products. No desired-value inverse is
  used. Only the projective ratio is claimed, so numerical
  acquisition of D_clock is unnecessary.

- Under the promised single simple hit in the good field, the
  modified discrete measure has exactly n-1 nonzero residues at
  distinct nodes. Its full moment recurrence therefore has order
  n-1; its corank-one Hankel kernel is the polynomial vanishing on
  the n-1 NONHIT nodes, namely G_n/(X-x_I). This scopes the short
  Prony failure correctly and is not an arbitrary-algorithm bound.

- The exact TQ source has
  `det M_epsilon=P_ret*C(epsilon)*T_epsilon(F)`;
  C is F-independent and T is linear in F. At an interior unique
  hit, differentiating gives
  `D_g det=C*T(F)*D_g P_ret`: the term
  `P_ret*C*T(g)` vanishes. At epsilon=0, C=1 and T(F) is the
  screened first endpoint, so the common factor can be a unit
  without a generic-epsilon assumption. Differentiating only the
  cheap core indeed returns T(g), the discarded zero term's
  coefficient, not the desired complementary product.

- The old good-orientation uniqueness hypothesis is kept separate
  from new scalar-knot coverage. With m=n-1 for the moment theorem
  and n for the TQ construction, the stated 3J and 2n guards fit
  the old n=3H+2 window asymptotically. Wrong-orientation validation
  is not promoted to an unconditional orientation palette.

The valid positive bridge is therefore the FULL determinant's
projective gradient, with an honest missing acquisition step. The
report correctly avoids assigning arbitrary additive moment/core
zeros an original short-annihilator decoder. No correction to my
`topology-prefix.md` is required by these checks.
