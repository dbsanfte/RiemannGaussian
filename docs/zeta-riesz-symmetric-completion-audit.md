# Signed symmetric identities: completion and cutoff audit

This slice proves the requested classical identities with actual convergence
and differentiation, and pays the allocation-removal error on the actual
balanced, pair-saturated three-prime subband. It does **not** prove an
independent signed floor for `nondominantRemainder`, an `o(1)` error for
completion to the unrestricted three-prime series, or a new zero exclusion.
The existing allowance-divergence theorem and the open `3/40` contradiction
target are unchanged.

## Complete three-prime series

For `Re(s)>1`, the increasing, distinct prime triples satisfy

$$
E_3(s)=\sum_{p<q<r}(pqr)^{-s},\qquad
6E_3(s)=P(s)^3-3P(s)P(2s)+2P(3s).
$$

[`PrimeNewtonThree.six_threeSeries`](../RiemannGaussian/PrimeNewtonThree.lean)
proves this from the finite Newton identity and absolute convergence.
[`PrimeNewtonMoments.lean`](../RiemannGaussian/PrimeNewtonMoments.lean)
proves actual differentiation under the series at every order:

$$
M_N(s):=\frac{D^N E_3(s)}{N!}
=\sum_{p<q<r}\frac{\log(pqr)^N}{N!}(pqr)^{-s},\qquad D=-\partial_s.
$$

The theorem names are `signedTaylorMoment_threeSeries`, `hasSum_threeMoment`
and `six_threeMoment`. The last retains all product-rule cross terms on the
Newton side. The generic justification is in
[`DirichletFamilyMoments.lean`](../RiemannGaussian/DirichletFamilyMoments.lean).
Absolute values in its convergence proofs justify exchanges; no bound on the
remaining signed carrier is obtained by those majorants.

## The coefficient distinction matters on the actual surviving support

Put `t=log n`, and freeze the physical cutoff `L` while differentiating.
The existing `LinearClass` requires every prime logarithm to lie between
`(t-L)/2` and `t-L`. On that class with three prime factors,

$$
c_{\mathrm{lin},L}(n)=\frac{t}{L}(2L-t),\qquad
\mathcal C_{\mathrm{lin},3}
=2(N+1)M_{N+1}-\frac{(N+1)(N+2)}L M_{N+2}.
$$

The balanced triples used in the divergence proof instead have **every pair
product below the physical cutoff**. Their actual coefficient and complete
polynomial extension are

$$
c_L(n)=\frac{t}{L}(t-L),\qquad
\mathcal C_{\mathrm{bal},3}
=\frac{(N+1)(N+2)}L M_{N+2}-(N+1)M_{N+1}.
$$

Both complete expressions have genuine `HasSum` proofs in
[`ZetaRieszCompleteOperators.lean`](../RiemannGaussian/ZetaRieszCompleteOperators.lean).
Neither assertion replaces the actual cutoff class or the multiplier
`1-theta_N(n)` by the complete sum.

This distinction is proved for the **original floor-defined cutoff and
original obstruction boxes**, not a model cutoff:
[`eventually_surviving_boxes_coefficient`](../RiemannGaussian/ZetaRieszBalancedTripleAudit.lean)
shows that throughout `1/2<u<=exp(-11/16)` these labels eventually belong to
`nondominantBand`, fail `LinearClass`, and have the second coefficient above.

For three primes with individual logarithms below `L` and total logarithm
at least `L`, the exact correction is

$$
c_L(pqr)=\frac{t}{L}\left(2L-t-
\sum_{\{v,w\}\subset\{p,q,r\}}(L-\log(vw))_+\right).
$$

`three_profile_with_pair_hinges` proves the corresponding divisor profile.
On the pair-saturated class the polynomial discrepancy is exactly
`(t/L)(3L-2t)` (`balanced_polynomial_defect`). This correction lives on
surviving labels. Existing off-mask deletions do not automatically estimate
it; a signed comparison must retain it with the original product phase.

### The allocation correction is paid on this subband

`balancedTripleBand u N K` is an explicit filter of the actual
`nondominantBand`: squarefree triples, `L<=log n`, all pair products below
the physical cutoff, and every prime logarithm at most half the product
logarithm. The theorem `eventually_boxes_subset_balancedTripleBand` proves
that it contains the same obstruction boxes, on the original schedules.

Let `R_bal` denote the original source-normalized residual sum restricted
to this band `S`. The theorem `actual_balanced_three_allocation_error_bound`
in `ZetaRieszCompleteOperators.lean` gives the independent comparison

$$
\left|R_{\mathrm{bal}}-
u^{N+1}\sum_{n\in S}\frac{t(t-L)}L
\frac{t^N}{N!}n^{-(3/2+iy)}\right|
\le C(N+1)r^N,\qquad r<1,
$$

where the checked constants are

$$
r=\frac{503}{1000}\frac{2048}{1023}e^{-1/140},\qquad
C=\frac43\frac{1509}{1000}
\operatorname{zetaMoebiusLogMajorantMass}(2049/2048).
$$

This is uniform in `N`, `K`, height `y`, and `0<=u<=exp(-11/16)`.
The mass constant is proved finite, but its numerical value is not evaluated
here. `tendsto_balanced_three_allocation_error` proves the vanishing error
for arbitrary moving supported subbands and heights. This applies the
existing balanced-companion saving to the corrected polynomial; it is not
a new estimate for the signed polynomial sum itself. The prime, pair-cutoff
and other original support masks remain in `S`.

## Coupling all prime counts

[`PrimeCountEuler.lean`](../RiemannGaussian/PrimeCountEuler.lean) proves the
genuine signed Euler product. For `|z|<=1`, `Re(s)>1`,

$$
F(z,s)=\sum_{n\ge1}\mu(n)z^{\omega(n)}n^{-s}
=\prod_p(1-zp^{-s})
=\exp\left(-\sum_{r\ge1}\frac{z^rP(rs)}r\right).
$$

The exponential equality and the absolutely convergent exchange of prime
and power sums are in
[`PrimeCountEulerExponential.lean`](../RiemannGaussian/PrimeCountEulerExponential.lean).
The `D` and `K=z partial_z` insertions are justified on actual infinite sums
in [`PrimeCountEulerMoments.lean`](../RiemannGaussian/PrimeCountEulerMoments.lean).
In particular differentiation in `z` at `1` uses a summable divisor-square
majorant on a full neighbourhood, not a formal interchange at a boundary.

Writing `A_N(z,s)=D^N F(z,s)/N!`, `hasSum_linear_all_counts` proves

$$
\sum_n c_{\mathrm{lin},L}(n)\frac{(\log n)^N}{N!}n^{-s}
=-(N+1)(K-1)A_{N+1}(1,s)
+\frac{(N+1)(N+2)}L(K-2)A_{N+2}(1,s).
$$

This is the proposed operator with all factorials and the Mobius sign
checked. Its extension outside `LinearClass` is a polynomial definition,
not a proved equality with the original Riesz coefficient.

There is a further analytic scope check: `generating_one` proves
`F(1,s)=1/zeta(s)` in the Euler half-plane. Its continued response has order
`-m_rho` at each nontrivial zero (`reciprocal_order_at_zero`). The previously
used unsigned squarefree response is `zeta(s)/zeta(2s)`; its larger
holomorphy domain cannot be substituted for that of `F(1,s)`. These facts do
not rule out cancellation in a suitable full differential expression, but
they do rule out claiming an independent bound merely from this product
identity.

Analytic diagnosis, **not an additional Lean theorem in this slice**:
the classical Mobius-inversion relation for `P` gives a local continuation
`P(s)=m_rho log(s-rho)+h(s)` near a right-half zero, on a slit neighbourhood.
The dilated terms `P(2s)` and `P(3s)` are analytic there. Newton's identity
therefore retains a leading `m_rho^3 log(s-rho)^3/6`; in particular the mixed
term `P(s)P(2s)` cannot be discarded as an independently analytic diagonal.
This is an inference from the standard relation, recorded for example in
equation (3.10) of [Chavez–Allawala](https://arxiv.org/pdf/2102.02280), not
an assertion that the raw prime series converges at the continued points.

The [Selberg–Delange framework](https://arxiv.org/abs/2010.12929) gives
asymptotics under additional hypotheses on the analytic factor accompanying
a power of zeta. It is a possible estimate framework, not a bound supplied
by the Euler identity alone. No such additional arithmetic estimate has
been discharged here.

## Truncated Selberg–Vaughan test

Define the overlap kernel already used in the repository by

$$
T_L(x,y)=L_+-(L-x)_+-(L-y)_++(L-x-y)_+.
$$

For `L>=0` the hinge defect is `-L+T_L(x,y)`. The exact constant-interior
identity is

$$
\sum_{d\mid n}\sum_{ab=d}\mu(a)\Lambda(b)=\Lambda(n).
$$

It cancels on squarefree composites. Consequently

$$
-\log n\,\mathcal R_L(n)
=\sum_{d\mid n}\sum_{ab=d}\mu(a)\Lambda(b)
T_L(\log a,\log b).
$$

[`squarefree_composite_overlap`](../RiemannGaussian/ZetaRieszTruncatedSymmetry.lean)
proves this, and `log_mul_riesz_eq_convolution` retains the prime-power
endpoint when the squarefree-composite hypothesis is absent. The existing
tent support theorem annihilates `log(ab)<=L`. It does not annihilate the
surviving `d=n=pqr` terms: the pair-saturated boxes have `log n>L`.

The remaining overlap is still signed by `mu(a)`. No matching theorem shows
that this entire transition is among the already paid wing/companion
errors. Positivity of the overlap kernel is not positivity of the sum.

## Next estimate and stop condition

The target remains a cofinal one-sided bound for the **actual**
`nondominantRemainder`, strong enough to beat its strict `-3/40` source.
This investigation has not supplied it.

The next estimate should address the signed overlap above on the actual
retained labels, keeping the phase `exp(-iy log n)`, the factor constraint
`ab|n`, and the physical cutoff together. The allocation can now be removed
on the stated balanced triple subband; it must remain elsewhere unless its
error is paid as well. Alternatively,
a completed differential expression must come with a quantitative signed
comparison controlling the pair hinges and allocation at source scale.
Window/dominant/off-mask bounds may be reused only after proving they apply
to those exact coefficients. A fixed-count bound must also control the
remaining counts before it can close the full contradiction.

Do not pursue further operator expansions solely because they are exact.
Without an independent numerical one-sided estimate or a proved `o(1)`
transfer error, they are infrastructure, not an arithmetic bounding
milestone. In particular, neither the source identity nor the reciprocal
pole audit is counted as progress in zero exclusion.
