# Uniform decay of the actual mixed-prime arithmetic sectors

Lean proves an independent bound for the entire arithmetic sum over all
multiples of any positive integer having at least two distinct prime
factors. At the existing hypothetical-zero normalization, these sums tend
to zero uniformly without any restriction on the chosen factor's size or
growth. Moving finite complex families also decay under an explicit growing
total-weight budget. The complete signed complement remains open; no new
zero exclusion or RH proof follows from this slice.

## The original arithmetic source

Keep the existing coefficient, filter, and cutoff unchanged:

\[
c_D(m)=\sum_{ab=m,\ a>D}\mu(a)\log b,\qquad
K_{p,N,s}(m)=m^{-s}\sum_{k\in\operatorname{supp}p}
 p_k\frac{(\log m)^{N+k}}{(N+k)!}.
\]

For a hypothetical zero `rho=beta+i*gamma` with `beta>1/2`, write

\[
u=3/2-\beta\in(1/2,1),\quad c=3/2+i\gamma,\quad
q=u^{-1/4},\quad D_N=\lfloor q^N\rfloor,
\]

and take the already constructed polynomial
`p=zetaRightHalfPoleJetFilter rho hrho`. The existing complete source is

\[
u^{N+1}\sum_{m\ge1}c_{D_N}(m)K_{p,N,c}(m)
\longrightarrow-m_\rho.
\]

Its convergence and genuine multiplicity are proved upstream in
[ZetaMoebiusTailMoments.lean](../RiemannGaussian/ZetaMoebiusTailMoments.lean).
The new results concern parts of this same arithmetic sum.

## First checked mechanism: coprime factor sectors

The [complete divisor cancellation](zeta-moebius-divisor-fibres.md) first
gives two exact finite prefix convolutions on products `P*n` with
`gcd(P,n)=1`. Both the logarithmic slope and intercept remain signed.
The finite coprime Euler factor and its logarithmic channel are retained
in the response; neither coprimality nor the physical factor `P^(-s)`
is omitted.

One ordinate-dependent constant bounds its filtered response by

\[
C_\gamma D\,\tau(P)^2(1+2\log P)
 \sum_k|p_k|.
\]

This already proves actual sector decay uniformly for moving factors
with `P_N^2<=D_N`, and automatically for every fixed eligible factor.
The complementary actual products retain the whole source.

Compiled entry points:

- [ZetaMoebiusFactorPrefix.lean](../RiemannGaussian/ZetaMoebiusFactorPrefix.lean):
  `zetaMoebiusFactorCoefficient_eq_convolutions`.
- [ZetaMoebiusFactorResponse.lean](../RiemannGaussian/ZetaMoebiusFactorResponse.lean):
  `LSeriesHasSum_zetaMoebiusFactorResponse`.
- [ZetaMoebiusFactorBound.lean](../RiemannGaussian/ZetaMoebiusFactorBound.lean):
  `exists_zetaMoebiusFactorFilter_bound`.
- [ZetaMoebiusFactorDecay.lean](../RiemannGaussian/ZetaMoebiusFactorDecay.lean):
  `tendsto_zetaRightHalfMoebiusFactor_actualSum` and
  `tendsto_zetaRightHalfMoebiusFactor_fixed_actualSum`.

## Stronger mechanism: all multiples via least common multiples

The implementation exposed a broader exact identity. Suppose `P>1` is
not a prime power. Every multiple `m` of `P` has `Lambda(m)=0`. Since
the complete convolution `mu * log` is `Lambda`, the original tail there
is exactly the negative finite head:

\[
c_D(m)=-\sum_{\substack{a\le D\\a\mid m}}\mu(a)\log(m/a).
\]

For each retained head divisor, the simultaneous conditions `a|m` and
`P|m` are exactly `lcm(a,P)|m`. Put

\[
L_a=\operatorname{lcm}(a,P),\quad
A_{D,P}(s)=\sum_{1\le a\le D}\mu(a)L_a^{-s},\quad
B_{D,P}(s)=\sum_{1\le a\le D}\mu(a)\log(L_a/a)L_a^{-s}.
\]

Lean proves genuine absolute convergence on `Re s>1` and the identity

\[
\boxed{\sum_{P\mid m}c_D(m)m^{-s}
 =A_{D,P}(s)\zeta'(s)-B_{D,P}(s)\zeta(s).}
\]

Both multipliers are entire finite sums. This formula includes arbitrary
prime valuations in `m/P`; it requires no infinite exchange over coprime
factor sectors. Zero-index conventions are discharged in the coefficient
and dilation proofs.

Compiled entry points in
[ZetaMoebiusMultipleResponse.lean](../RiemannGaussian/ZetaMoebiusMultipleResponse.lean):

- `zetaMoebiusLogTailCoefficient_eq_neg_prefix`
- `zetaMoebiusMultipleCoefficient_eq_prefix`
- `zetaMultipleLogCoefficient_eq_dilation`
- `LSeriesHasSum_zetaMoebiusMultipleResponse`

## The information that supplies the uniform bound

On `Re s>=1/2`, retain the physical weight `L_a^(-s)` while estimating
its logarithmic displacement:

\[
0\le\log(L_a/a)\le\log L_a,\qquad
|L_a^{-s}|\log L_a\le2.
\]

Consequently `|A_{D,P}(s)|<=D` and `|B_{D,P}(s)|<=2D`, with **no
factor-dependent constant**. Bounding the Dirichlet weight by one before
using it to control the logarithm would lose this uniformity.

The existing low-height exclusion gives `|gamma|>1`. A unit Cauchy circle
about `c` therefore avoids zeta's pole and stays in `Re s>=1/2`. The entire
multipliers and the bounded values of zeta and its derivative on that
circle give, for every polynomial, cutoff, order, and eligible factor,

\[
\left|\sum_{P\mid m}c_D(m)K_{p,N,c}(m)\right|
 \le C_\gamma D\sum_k|p_k|.
\]

This is a bound on the norm of the **signed sum**; it is not a bound on
the sum of absolute values of its arithmetic terms. Cauchy's theorem
uses the exact response after the complete cancellation. It needs no
unproved cancellation estimate or pole-jet assumption for this sector.

Compiled entry points:

- [ZetaEntireMultiplierBound.lean](../RiemannGaussian/ZetaEntireMultiplierBound.lean):
  `exists_zetaEntireMultiplier_filter_bound`.
- [ZetaMoebiusMultipleBound.lean](../RiemannGaussian/ZetaMoebiusMultipleBound.lean):
  `norm_zetaPrimeFeature_mul_log_le_two`,
  `norm_zetaMoebiusMultipleMultipliers_le`, and
  `exists_zetaMoebiusMultipleFilter_bound`.

## Uniform decay and all finite complex families

With the original selected-zero data, Lean obtains

\[
\left|u^{N+1}\sum_{P\mid m}c_{D_N}(m)K_{p,N,c}(m)\right|
 \le C_\rho(\sqrt u)^N.
\]

The constant is independent of `P` and `N`. Thus an arbitrary moving
positive mixed-prime factor `P_N` has a negligible actual sector, without
a growth condition. The stated geometric rate is a convenient envelope,
not a claimed sharp rate.

For every finite complex family `w_P`, the unnormalized bound is

\[
\left|\sum_{P\in S}w_P\sum_{P\mid m}c_D(m)K_{p,N,c}(m)\right|
 \le C_\gamma D\left(\sum_k|p_k|\right)
 \left(\sum_{P\in S}|w_P|\right).
\]

Hence any moving finite family with `sum |w_N(P)|<=D_N` has normalized
limit zero. Factor sizes, overlaps, phases, and prime valuations have no
separate restriction. The total absolute weight is an explicit cost;
the theorem does not claim cost-free simultaneous deletion of all factors.

Compiled entry points in
[ZetaMoebiusMultipleDecay.lean](../RiemannGaussian/ZetaMoebiusMultipleDecay.lean):

- `hasSum_zetaMoebiusMultipleFilter`
- `exists_zetaMoebiusMultipleFamily_bound`
- `exists_zetaRightHalfMoebiusMultiple_uniform_bound`
- `tendsto_zetaRightHalfMoebiusMultiple_actualSum`
- `tendsto_zetaRightHalfMoebiusMultipleFamily_actualSum`

## What remains

The same module proves exact sector-plus-complement reconstruction with
genuinely summable series. For every chosen moving mixed-prime factor,

\[
u^{N+1}\sum_{P_N\nmid m}c_{D_N}(m)K_{p,N,c}(m)
 \longrightarrow-m_\rho.
\]

The terminal theorem is `tendsto_zetaRightHalfMoebiusMultiple_remainder`.
The [simultaneous cofinal sieve](zeta-moebius-growing-sieve.md) now combines
these sectors with exact grouped overlap coefficients and a discharged
total-weight budget. Its final distinct-prime complement retains the full
source, and the total error from the original filtered response has a
proved geometric bound. The independent signed estimate for that
surviving arithmetic remains open. No exchange of an unbounded factor sum
with the source limit, finite-band masked decay, or new global zero bound
is asserted here.

These are applications and new repository interfaces for classical Möbius,
Dirichlet-series, and Cauchy identities; no historical novelty claim has
been established. The [failed fractional absolute allowance](zeta-moebius-fractional-budget-audit.md)
remains ruled out. This slice uses the retained signed arithmetic response.
