# A joined higher-cyclotomic q-binomial determinant

2026-10-18. Paper proof and exact finite polynomial/rational regressions.
No Lean theorem, prime estimate, RH improvement, generalized-prime model,
or family-wide no-go is asserted. This is a further test of the
[literal cyclotomic source](arithmetic-operator-cyclotomic-source.md).
The prior literal prime-power/order-landing audit is preserved unchanged.

## Decision

The prescribed two-row determinant below gains actual third-order
cyclotomic divisibility BEFORE taking norms. That gain is genuine, and for
every index n>2 it is exactly third order as a polynomial. Nevertheless its
complete logarithmic norm, after an explicit polynomial height and constant,
has an exponentially small remainder. The faithful cyclotomic zero source
extracted by Φ_n³ is carried with the opposite sign by the actual integer
quotient. No estimate beyond the previous Möbius convolution is obtained.

This closes this particular determinant/norm shortcut. It does not close
other higher q-congruences, growing-size determinants, arithmetic extra
valuations of the quotient, or other joined additive relations.

## 1. Actual common numerator, not separate norms

Write Gaussian binomials as Q(N,M;q)=[N choose M]_q. For every n≥2 set

  A_n(q)=Q(5n,n;q),        F_n(q)=Q(5,1;q^(n²)),
  B_n(q)=Q(4n,2n;q),      G_n(q)=Q(4,2;q^(n²)),
  D_n(q)=det [[A_n(q),F_n(q)],[B_n(q),G_n(q)]]
        =A_n(q)G_n(q)−B_n(q)F_n(q) ∈ Z[q].

Both Gaussian rows have area 4n². Put z=q^(n²). The comparison entries are
literal Gaussian polynomials:

  F_n=1+z+z²+z³+z⁴,  G_n=F_n+z².

The subtraction is performed on this common integer numerator, retaining
the interaction of the actual rows. No row is replaced by its modulus.

The exact degree is

  m_n=deg D_n=8n²−n−1, with leading coefficient −1.

To see this, the two native q-binomial products agree through degree n;
their first difference is −q^(n+1), as follows from the denominators
P_n(q)=∏_(j≤n)(1−q^j) and P_(2n)(q) modulo q^(n+2). Their numerator factors
start later, and n+1<n². Thus D_n has first nonzero coefficient −q^(n+1).
Each product in D_n is reciprocal of degree 8n², so the displayed degree
and leading coefficient follow. This is exact, not an asymptotic degree count.

## 2. Higher congruence, and exact multiplicity

Zudilin's primary paper, equation (2), records Straub's congruence

  Q(an,bn;q) ≡ Q(a,b;q^(n²))
    − b(a−b)binomial(a,b)(n²−1)(q^n−1)²/24   mod Φ_n(q)³.

For the two rows b(a−b)=4, while the ordinary binomials are 5 and 6.
Consequently the second-order defect in the determinant is proportional to

  (q^n−1)²(5G_n−6F_n),

and 5G_n−6F_n is zero modulo Φ_n, since q^(n²)=1 there. Thus

  Φ_n(q)³ divides D_n(q) in Z[q], for every n≥2.

Although the quoted congruence contains 24 in its rational presentation,
the resulting D_n is an integer polynomial and Φ_n is monic. Polynomial
division therefore gives an integer quotient. No factor 24, bad-prime
exclusion, or separate denominator-clearing height is inserted into this
particular determinant claim.

The fourth-order primary theorem also gives an exact obstruction to taking
another cyclotomic power in this family. Let ζ=e(1/n) be the principal
primitive root, ε=q^n−1, K=(n²−1)/24, and

  H(q)=Σ_(k=1)^(n−1) q^k/(1−q^k)+(n−1)/2.

Near q=ζ use q=ζ(1+ε)^(1/n), so

  H(q)=−Kε+h₂ε²+O(ε³).

The first coefficient uses the finite root identity
Σ ζ^k/(1−ζ^k)²=−(n²−1)/12, obtained by logarithmically differentiating
(X^n−1)/(X−1) at X=1. Pairing k and n−k gives
Σ kζ^k/(1−ζ^k)²=(n/2)Σ ζ^k/(1−ζ^k)², hence the coefficient −K.

Theorem 1, equation (6), applied to the two rows gives after their common
numerator is joined

  D_n(q)/ε³ at q=ζ
    =−60(2h₂−K)
    =−(60/n²) Σ_(k=1)^(n−1)
             k² ζ^k(1+ζ^k)/(1−ζ^k)³.                 (★)

Here the left side means the holomorphic limiting quotient; ε has a simple
zero at ζ. Details of the coefficient cancellation are useful for checking
the constants: in Theorem 1 the two corrections are

  −20ε[5H+6Kε+(4n−7)Kε²/2],
  −24ε[4H+5Kε+(4n−6)Kε²/2].

In D_n their H coefficient is 25G_n−24F_n=F_n+25z², their Kε coefficient
is 30z², and the Kε² coefficient has constant term −15. Since
(F_n+25z²)'_(ε=0)=60n and (z²)'_(ε=0)=2n, the n-dependent terms cancel,
leaving −60(2h₂−K). Differentiating each summand of H twice gives
2h₂−K=n^(-2)Σ k²ζ^k(1+ζ^k)/(1−ζ^k)³.

For n>2 this coefficient is nonzero. Indeed, put

  T_k=ζ^k(1+ζ^k)/(1−ζ^k)³
     =−i cos(πk/n)/(4 sin(πk/n)³).

For 1≤k<n/2, T_k has strictly negative imaginary part and
T_(n−k)=−T_k. The pair in Σk²T_k is n(2k−n)T_k, with strictly positive
imaginary part. There is at least one pair; if n is even the middle term
is zero. Hence (★) is nonzero. It follows that

  ord_(Φ_n) D_n=3 for every n>2.

The index-two exception is exactly fourth order:
Φ₂(q)^4 divides D₂(q), and [D₂(q)/(q+1)^4]_(q=−1)=195≠0.
This last fixed-index polynomial identity is included in the exact regression.

## 3. Nonzero actual integer determinant and a uniform height bound

Fix any integer base b≥2, t=1/b≤1/2, and P_m=∏_(j=1)^m(1−t^j).
The positive infinite product obeys

  P_∞≥(1−t)(1−Σ_(j≥2)t^j)=1−t−t²≥1/4.

Define the following positive real quantities, all directly from native
q-factorials:

  A=P_(5n)/(P_n P_(4n)),  B=P_(4n)/P_(2n)²,
  F=Σ_(j=0)^4 t^(jn²),   α=t^(n+1), u=t^n,
  L_n=−D_n(b)/b^m_n,
  C_b=1/[(1−t)P_∞].

The exact product identity is

  L_n=(B−A)F/α−A t^(2n²−n−1).                    (1)

Let

  R=∏_(j=n+1)^(2n)(1−t^j),
  S=∏_(j=2n+1)^(4n)(1−t^j),
  T=∏_(j=4n+1)^(5n)(1−t^j).

Then A=T/P_n, B/A=S/(RT), RT≥P_∞≥1/4, 1≤A≤4 and C_b≤8.
Ordinary product inequalities 1−Σx_j≤∏(1−x_j)≤1 and the second
Bonferroni bound give the following explicit estimates:

  S−RT≥S−R≥α−2αu≥α/2,
  |A−P_∞^(-1)|≤16α,
  |(S−RT)/α−1/(1−t)|≤8u,
  1−RT≤4α.

For clarity, the third bound uses U=Σ_(j=n+1)^(2n)t^j
=α(1−u)/(1−t) and
0≤U−(1−R)≤U²/2≤2α². The remaining three errors are bounded by
2αu each: truncating U's geometric series, 1−S, and R(1−T).
This pays every finite product tail.

Put δ=(B/A)−1=(S−RT)/(RT). The preceding bounds imply

  |δ/α−1/(1−t)|≤64u,
  |(B−A)/α−C_b|≤288u.

Also F≤2, |F−1|≤2t^(n²)≤2u, and
t^(2n²−n−1)≤u. Equation (1) therefore gives

  |L_n−C_b|≤596u≤600b^(-n).                     (2)

There is a positive lower bound independent of n and b:
δ/α≥1/2, F≥1 and t^(2n²−n−1)≤1/32 imply

  L_n≥(15/32)A≥15/32.

In particular D_n(b)<0 and is nonzero for **every** b≥2,n≥2. Because
C_b≥1, the mean-value estimate for the logarithm and (2) give

  e_b(n):=log|D_n(b)|−m_n log b−log C_b,
  |e_b(n)|≤1280b^(-n).                          (3)

All constants in (2)–(3) are uniform for the prescribed b≥2,n≥2. The
rough constants are intentional, to make the complete error ledger verifiable.

The constant is ordinary q-product data:
log C_b=−log(1−1/b)−Σ_(j≥1)log(1−b^(-j)). It is retained in the centering;
forgetting that nonzero constant would manufacture an artificial density.

## 4. Source before estimate: the full determinant has no zero pole

By (3), E_b(s)=Σ_(n≥2)e_b(n)n^(-s) is entire. Thus the full determinant
norm series has the explicit continuation

  Σ_(n≥2)log|D_n(b)| n^(-s)
    =log b[8ζ(s−2)−ζ(s−1)−ζ(s)−6]
      +log C_b[ζ(s)−1]+E_b(s).

Its elementary poles can occur at 3,2,1. It has no pole at a hypothetical
nontrivial zeta zero. This is proved from the actual joined integer
determinant, not inferred from a generalized-prime model or a prime density.

The annular centered matched-power response also vanishes explicitly: for
fixed ρ, Σ_(X≤n<2X)e_b(n)n^(ρ−1) is exponentially small in X, hence its
normalization by X^(Reρ) tends to zero. No growing-height claim is required.

## 5. Where the faithfully extracted source goes; full density retained

Let A_b(n)=log Φ_n(b), R_b(n)=A_b(n)−φ(n)log b, as in the prior literal
cyclotomic gate. Its exact series is C_b^tail(s)/ζ(s), with the entire
zero-free numerator C_b^tail(s)=Σ log(1−b^(-j))j^(-s). Here C_b^tail is
different from the positive determinant constant C_b in §3.

Integer monic division in §2 supplies the actual positive integer

  Q_b(n)=|D_n(b)|/Φ_n(b)³ ∈ N, Q_b(n)>0.

All indices n≥2 are retained, prime and composite; all prime factors of
Φ_n(b), including nonprimitive and exceptional two-adic factors, remain.
The fixed extra Φ₂ factor is retained inside Q_b(2), not discarded.
The exact source ledger is

  U_b(n):=log Q_b(n)−[m_n−3φ(n)]log b−log C_b,
  3R_b(n)+U_b(n)=e_b(n).                         (4)

Therefore

  Σ_(n≥2)U_b(n)n^(-s)
    =−3 C_b^tail(s)/ζ(s)+3R_b(1)+E_b(s).         (5)

The quotient's tracked residual has exactly the opposite nonzero zeta
source, with full coefficient 3. No thinning/density factor reduces it.
The totient correction in U_b is part of tracking the SAME residual R_b;
it must not be mislabeled a source-free polynomial correction. The full
uncentered quotient may mix totient and tail sources, as in the prior gate.

Taking finite prefixes in (4) gives the explicit discrepancy bound

  |Σ_(n=2)^N U_b(n)+3Σ_(n=2)^N R_b(n)|
      ≤1280/[b(b−1)].                           (6)

Thus power bounds O(N^θ), θ≥0, for the tracked quotient prefix are equivalent
to the same bounds for R_b, hence to the previous exact μ*c_b/Mertens
convolution target. The determinant identity has not proved either bound.

The height budget is also explicit. Each row has area 4n²; the determinant
has degree 8n²−n−1, while the guaranteed extracted divisor has degree
3φ(n)≤3n. Multiplying all rows through N gives cubic logarithmic height
Σm_n log b, whereas the extracted cyclotomic height is at most quadratic.
Q_b(n)≥1 only yields the corresponding quadratic pointwise bound, far
larger than the faithful N^ρ prefix source. Extraction is not a saving.

Exact polynomial order is NOT equality of integer p-adic valuations. For
example b=2,n=4 has Φ₄(2)=5, v₅(D₄(2))=4, and v₅(Q₂(4))=1, even though
ord_(Φ₄)D₄=3. Such extra arithmetic quotient valuations remain actual data;
this note neither discards them nor supplies an estimate for their coupling.

Order-index scale n remains distinct from the prime-factor scale, which can
be exponential in n (and the determinant size is exponential in n²). No
ordinary prime-cutoff zeta source is inferred by replacing one with another.
The literal nonzero prime-power phase transport and the failure of phase
resetting in the preceding audit remain untouched.

Precisely, the source ledger here uses ordinary logarithmic norms, with
complex s on the order index n. It is not an identity for a literal
prime-power packet at nonzero y. If p has valuations a in Φ_n(b) and c in
Q_b(n), the packet of the product uses Σ_(r≤3a+c)p^(-iry), which generally
differs from 3Σ_(r≤a)p^(-iry)+Σ_(r≤c)p^(-iry). Thus no nonzero prime-phase
determinant source theorem or no-go is inferred from (4)–(5).

## 6. Evidence and next decision

Primary: W. Zudilin, *Congruences for q-binomial coefficients*,
[arXiv:1901.07843v2](https://arxiv.org/pdf/1901.07843), revised 1 April 2019.
Equation (2), printed p1, supplies the cubic congruence. Theorem 1 / (6),
printed p2, supplies the fourth-order expansion used in (★). Printed p3
explicitly defines its rational-function congruences by denominators
coprime to Φ_n. The determinant consequence and the product-height/source
proof above are derived here, rather than attributed as a theorem of that
paper. No GRH or prime-order distribution theorem is used.

The exact probe checks integer polynomial coefficients and degree,
cyclotomic divisibility AND failure at the next power, the coefficient (★)
in Q[q]/Φ_n using exact rational polynomial inverses, actual base evaluation,
prime-power valuation lower bounds and their extra quotient factors, and
rational enclosures for the infinite-product height constant. It uses no
floating root or source scan. The 509 checks and reproducible probe are in
`.lake/arithmetic-operator-qpascal-higher-gate/exact-results.json` and
`exact_probe.py` in the same directory. The current gate manifest pins
their contents together with this paper-level derivation.

No standalone Lean ledger is proposed: without native proof of this
determinant congruence, a conditional log reassociation would certify a
tautology rather than the useful new gate. All determinant/source claims
are explicitly paper-level. A future independent estimate would have to
control the actual quotient residual or its additional arithmetic valuation
coupling; reusing its exact full norm or positivity cannot supply that step.
