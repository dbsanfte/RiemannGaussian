# Exact strings, small polynomial cores, and the collision norm

26 October 2026. The knot-theory search was extended through finite fusion,
cyclic covers, Bethe strings, and determinant dualities. This packet derives
and pays for a small polynomial core and an entire short moment sequence.
It also sharpens the smaller-component order statement. **The complete
collision query is not faster, and the guaranteed sixth-exponent factoring
goal remains open.** These are paper proofs with independent review, not
Lean results or numerical coverage evidence.

## Contract and result

Use the already acquired recentered polynomial
\(F(z)=\sum_{j=0}^{J}f_jz^j\), where \(J=2L=\widetilde O(k)\),
\(k\asymp N^{1/6}\), and \(H=k^2\). The physical clock is
\(z_i=\eta q^i=\eta^{2i+1}\), with \(q=\eta^2\) of local orders above
\(16H\). Up to a certified unit, the original prefix query is

\[
 P_m=\prod_{i=1}^{m}F(z_i),\qquad m=O(k^{3/2}).
\]

The existing complete evaluator costs
\(\widetilde O(J+\sqrt{Jm})\), or \(\widetilde O(k^{5/4})\) at this
scale. The desired bound is \(\widetilde O(J+\sqrt m)\), within
\(\widetilde O(k)\). These are bounds for this route, not claims to improve
the general factoring baseline. Short prefixes \(m\leq J\), or
\(m\leq3J\) when using the moment formula, already fit the target through
the old evaluator. All costs suppress logarithmic factors in \(N\).

The exact construction gives a polynomial residue Jacobian with

\[
 \det\mathcal J_\epsilon
 =\Omega_m\left(\prod_{i=2}^{m}F(z_i)\right)
 C(\epsilon)T_J(\epsilon),
\]

where \(\Omega_m\) is a certified clock unit, \(C\) is a scalar geometric
factorial, and **all coefficients of \(T_J\), of degree at most \(J\),
are acquired in \(\widetilde O(J)\)**. The complete value
\(C(\epsilon)T_J(\epsilon)\) at one supplied \(\epsilon\) costs
\(\widetilde O(J+\sqrt m)\). The multiplicative factor
\(\prod_{i=2}^{m}F(z_i)\) still carries almost the entire original query.
Neither determinant notation nor a normalized spectrum acquires it.

## Constructive exact-string calculation

Let the long clock polynomial \(Q(z)=\prod_{i=1}^{m}(z-z_i)\) be a
symbolic descriptor. Its full coefficient list is not acquired. Set

\[
 a(z)=(z-z_m)F(z),\quad
 d_\epsilon(z)=\epsilon(z-z_1)F(qz).
\]

The finite identity

\[
 a(z)Q(qz)+d_\epsilon(z)Q(z/q)=
 \left[q^m(z-z_0)F(z)+
 \epsilon q^{-m}(z-z_{m+1})F(qz)\right]Q(z)
\]

has a transfer polynomial acquired in \(\widetilde O(J)\). It is a formal
polynomial identity; a nonzero physical Bethe vector or physical norm is
not assumed. Differentiating the cleared residue equations at the string
gives a tridiagonal matrix after dividing only by certified clock units.
Its continuant expansion gives

\[
 S_\epsilon(F)=\sum_{j=0}^{J}f_jz_1^j
       (\epsilon q^{j+1-2m};q)_m
       =C(\epsilon)T_J(\epsilon),
\]

\[
 C(\epsilon)=(\epsilon q^{J+1-2m};q)_{m-J},
\quad
 T_J(\epsilon)=\sum_{j=0}^{J}f_jz_1^j
 (\epsilon q^{j+1-2m};q)_{J-j}(\epsilon q^{1-m};q)_j.
\]

Here \((x;q)_s=\prod_{r=0}^{s-1}(1-xq^r)\). A balanced,
division-free polynomial recursion acquires the coefficients of \(T_J\)
in \(\widetilde O(J)\); it works even if its leading coefficient vanishes.
The long common factor \(C\) is evaluated at one parameter by the existing
scalar factorial algorithm. Its universal zeros are auxiliary spectral
zeros, not original collision witnesses. At \(\epsilon=0\),
\(T_J(0)=F(z_1)\) and the full determinant returns exactly the original
product, up to \(\Omega_m\).

See the [derivation and paid recursion](exact-string.md) and
[independent review](string-review.md). The numerical value of
\(\Omega_m\) is optional for a zero/nonunit query; its unit status is
proved. Acquiring that optional unit is not the unresolved bottleneck.

## Cheap moments and the determinant that they actually give

With the explicit q-binomial weights \(w_r\), all moments

\[
 \mu_t=\sum_{r=0}^{m}w_r z_{r+1}^{t}F(z_{r+1}),
 \qquad 0\leq t\leq2J,
\]

are acquired in \(\widetilde O(J+\sqrt m)\) by one scalar factorial,
short unit ratios, and one convolution. A small Hankel matrix made from
these moments describes a weighted subset sum. It does not have the full
collision product as a factor. The exact small resultant/Christoffel
determinant for the full-support product instead requires values of the
long clock polynomial at every native root: those entries are the unpaid
original query.

For the pencil \(A+\epsilon D\), \(\det A=P_m\). On the branch where
\(A\) is invertible,

\[
 \det(I+\epsilon A^{-1}D)=C(\epsilon)T_J(\epsilon)/F(z_1).
\]

This normalization divides out precisely the target. At collisions it is
not a legal inversion. Generalized-eigenvalue language is therefore
restricted to regular generic pencils; the division-free determinant
identity holds at singular inputs too. Confluent resultant identities
extend polynomially, without claiming that each derivative row retains
a clock factor. See [moment construction](bispectral-string.md) and
[review](bispectral-review.md).

## What the literature contributes

* [Caradoc–Foda–Kitanine](https://arxiv.org/pdf/math-ph/0601061)
  gives finite higher-spin fusion and its normalization. The explicit
  two-stack specialization removes \((1-X)(1-qX)\) from the unfused
  scalar. Those are exactly adjacent comparison factors. The normalized
  endpoint value consequently discards their zeros. Our
  [fusion calculation](string-fusion.md) retains the correction and derives
  its cleared finite recurrence; division at a collision is not licensed.
* [Nepomechie–Wang](https://arxiv.org/pdf/1409.7382) supplies twist
  regularization and additional physicality conditions for singular Bethe
  solutions. These conditions prevent equating our engineered polynomial
  identity with a physical norm without further proof.
* [Mukhin–Tarasov–Varchenko](https://arxiv.org/html/math/0605172) and
  [Claeys–Van Neck–De Baerdemacker](https://arxiv.org/html/1706.05511)
  motivate exchanging long strings for smaller determinant data. Their
  model-specific hypotheses and scalar normalizations remain necessary;
  the native finite identities above were derived separately.
* [Silver–Williams](https://arxiv.org/pdf/math/0202197) and
  [Doyle–Fili–Hyde](https://nyjm.albany.edu/j/2022/28-21p.pdf) motivate
  cyclic-cover and finite incidence tests. Our target is a marked hit
  \(q_j^i=b\), not a periodic return to 1. An ordinary multiple cover loses
  that hit; changing its boundary to \(b^d\) preserves it. The
  [safe twisted-cover construction](cyclic-cover.md) costs
  \(\widetilde O(J+|S|+k)\) for an actually supplied index set \(S\).
  Taking the whole interval does not improve the old query bound.

The [source ledger](sources.json) records inspected locations, limitations,
and hashes of the existing internal inputs. No external full texts are
copied into this archive.

## Native arithmetic and further tested routes

After the existing \(k\)-roughening, the smaller component has order
\(r_P<P\leq\sqrt N\leq k^3\), with every prime divisor greater than
\(k\). Any nontrivial order loss therefore leaves

\[
 r'_P\leq r_P/(k+1)<k^2<16H.
\]

For the paid short-label cleaning schedule this triggers the established
first-drop factor recovery. Thus **continuing label cleaning preserves the
smaller component's order exactly**. It does not prove that order prime,
identify it, or supply a shorter collision cover. A huge aggregate
exponent still requires paid localization to a short annihilating factor.
See [native-label analysis](native-inversion.md),
[group-polynomial acquisition audit](group-polynomial.md), and
[independent review](native-group-review.md).

The [quadratic-phase test](recurrence.md) retains the integer carry in each
row exponent. Its immediate interlacing only trades row count for clock
length. The explicit retained rows \((7,1)\) or \((5,1)\), according to
\(N\bmod3\), have full Fourier support on the auxiliary phase cycle;
expanding that entire cycle costs too much. This is a limitation of that
expansion, not a lower bound for compressed native algorithms. The
[initial review](review-initial.md) also checks the twisted-cover costs.

A useful next advance must obtain the full retained norm or its guaranteed
zero predicate at the target cost, possibly from the acquired small core
and native conic constraints. No theorem here makes an additive core or
moment zero a guaranteed original collision. Proper gcds of auxiliary
values remain useful, but saturated additive zeros have no automatic
short-annihilator decoder.

## Validation and preservation

The [integration review](integration-review.md) records the incorporated
qualifications. All 775 prior protected files, both journal/agent prefixes,
and 22 concurrent engineering files are checked against the pre-edit
snapshot. This packet adds no numerical campaign, executable research
implementation, Lean module, public asset, commit, or push. See the
[validation record](review.json) and [manifest](manifest.json).
