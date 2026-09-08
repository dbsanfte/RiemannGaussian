# Gamma quadratics: exact gcd structure and reflected diagonal control

The active objective remains one independent signed inequality that beats
the original source, including all proved errors, for each hypothetical
zero right of one half. This slice controls the complete large-gcd part of
the original quadratic and the complete large-gcd diagonal of its reflected
product. It does not prove the needed inequality, an improved zero bound,
or RH.

The user's `RiemannGaussian_gamma_reflection_next_steer.md` supplied the
near-square, gcd, and reflection direction. Its reference head predates
the sharper factor-tail theorem at `9bf25326bba20407f9d7592662a79101c68f9755`.
The new proofs use the actual existing gamma carrier and original source.
No statement in the steering memo is assumed as a mathematical premise.

## Exact objects before estimates

Write `s = rho.1`, `sigma = Re(s)`, `chi_s = pairedEtaXiCompletionFactor s`,
and `rho# = conjugatePartner rho`, so `s# = 1 - conj(s)`.

`EtaGammaReflection.source_eq_completionNumerator` proves

\[
S_s=\chi_s\operatorname{pairedEtaFactor}(s)
   =s(1-s)\Gamma_{\mathbb R}(s).
\]

The nonzero normalization `N_s = s / pairedEtaFactor(s)` converts this to
the existing completed Laplace amplitude. The normalized source-energy
ratio is exactly the squared norm of the existing reflection multiplier.
`normalized_source_energy_eq_iff_re_eq_half` transports the previous
rigidity theorem: equality of those energies is equivalent to the critical
line. **The theorem supplies no arithmetic proof of that equality.**

Define the complete row

\[
R_{s,A}(m)=\sum_{c\ge1}\gamma_{s,A}(mc).
\]

`EtaGammaGcd.summable_norm_gammaCarrier` and
`summable_norm_gammaRow` discharge absolute convergence.
`cofactor_short_eq_sum_dvd`, `hasSum_dvd_gammaRow`, and
`smoothQuadratic_eq_sum_gammaRow` then prove the exact triple expansion

\[
Q_{s,A,U}=-\sum_{a,b\le U}\mu(a)\mu(b)R_{s,A}(ab),
\]

where both finite indices start at one and the positive cofactor has no
cutoff. There is no truncation or formal interchange of divergent sums.

`sum_square_eq_sum_gcd` partitions the finite square by `g = gcd(a,b)`.
Writing `a=gr`, `b=gt` retains `r,t <= U/g` and `Coprime r t`.
`smoothQuadratic_eq_sum_gcdBlock` identifies the resulting sum with the
original `smoothQuadratic` exactly.

The coefficient and scale identities are also retained:

\[
\begin{aligned}
\mu(gr)\mu(gt)
 &=\mathbf1_{(g,r)=(g,t)=1}\mu(g)^2\mu(r)\mu(t),\\
R_{s,A}(g^2rt)&=g^{-2s}R_{s,A/g^2}(rt).
\end{aligned}
\]

These are `moebius_common_factor` and `gammaRow_square_scale`.
`gcdBlock_eq_factor_mul_reducedCore` consequently gives

\[
B_{s,A,U}(g)=\mu(g)^2g^{-2s}
 K_{s,A/g^2,U/g}(g),
\]

where `reducedGcdCore` is the negative finite double sum of the complete
rows, with **all three** coprimality conditions. On squarefree `g`, the
remaining coefficient signs are exactly `mu(r) mu(t)`. No bound for `K`
at arbitrary physical scale is assumed.

## The complete large-gcd bound

For `A > 0`, `g >= 1`, and `g^2 >= 2A`, the entire reduced row is in the
exponentially damped range. `norm_gammaRow_large_le` proves

\[
\|R_{s,A}(m)\|\le16\|\chi_s\|m^{-\sigma}e^{-m/(2A)}
\quad(m\ge2A).
\]

At `m=g^2rt`, the exponential is bounded by `exp(-r/2) exp(-t/2)`.
Summing the complete two reduced factors, rather than assuming they are
bounded, gives `norm_gcdBlock_le`:

\[
\|B_{s,A,U}(g)\|\le64\|\chi_s\|g^{-2\sigma}.
\]

Thus, for `sigma > 1/2`, `G >= 1`, `G^2 >= 2A`, and any finite `U`,
`norm_largeGcd_le` proves

\[
\left\|\sum_{G<g\le U}B_{s,A,U}(g)\right\|
\le\frac{64\|\chi_s\|}{2\sigma-1}G^{1-2\sigma}.
\]

The exact split is `smoothQuadratic_eq_small_add_large`. In particular,
`norm_smallGcd_sub_smoothQuadratic_le` applies this allowance to the
original quadratic itself, not an unrelated model.

On `A=u^8`, `U=u^5`, `G=2u^4`, `u>=1`,
`norm_largeGcd_eighth_fifth_le` gives

\[
\|\mathrm{largeGcd}\|
\le\frac{64\|\chi_s\|}{2\sigma-1}u^{4-8\sigma}.
\]

`largeGcd_eighth_fifth_tendsto_zero` proves its decay for every fixed
actual zero with `sigma>1/2`. The exponent approaches zero and the
constant grows as `sigma` approaches one half; this is not a uniform
zero-free margin.

`EtaGammaQuadratic.norm_smoothQuadratic_eighth_sub_source_le` also proves
the complete near-square source budget, for `u>=2`:

\[
\|Q-S_s\|\le
2C_su^{-4-5\sigma}
+1024\|\chi_s\|u^{24}e^{-u^2/4}
+\frac{\|\chi_s\|(1+16\,2^{-\sigma})}{6u^{24}}.
\]

Here `C_s` is the existing `gammaMoebiusConstant`. The two short sums,
entire omitted cofactor, and both physical source endpoints are paid.
`smoothQuadratic_eighth_tendsto_source` holds at every actual nontrivial
zero. Combining it with the large-gcd decay gives
`smallGcd_eighth_fifth_tendsto_source`: the surviving smaller-gcd core
still carries the original nonzero source.

## What reflection really cancels

`partner_mul_conj_original_nat_cpow` proves
`d^(-s#) conj(d^(-s)) = 1/d` for positive integers. However, multiplying
two **actual** Moebius terms squares their arithmetic coefficient. Their
diagonal is `mu(d)^2/d` times the complete reflected gamma kernel, not
`mu(d)/d`. Signed harmonic Moebius cancellation therefore cannot simply be
inserted here.

For the actual gcd blocks, the common factor is a square. The checked
identity `gcdBlock_partner_mul_conj` is

\[
B_{s^\#,A,U}(g)\overline{B_{s,B,V}(g)}
=\frac{\mu(g)^2}{g^2}
 K_{s^\#,A/g^2,U/g}(g)\overline{K_{s,B/g^2,V/g}(g)}.
\]

The reciprocal-square coefficient is positive, but the reflected product
of cores is complex; the identity does not establish positivity.
`smoothQuadratic_partner_mul_conj` gives the **full** product of the two
original quadratics: this diagonal plus `gcdCrossOffDiagonal`, containing
every unequal-gcd interaction. Both completion phases and physical scales
remain explicit.

There is a further unconditional estimate for the actual diagonal tail.
For `G^2 >= 2A`, `G^2 >= 2B`, and `G>=1`,
`norm_gcdCrossDiagonalTail_le` proves

\[
\left\|\sum_{G<g\le U}
B_{s^\#,A,U}(g)\overline{B_{s,B,U}(g)}\right\|
\le\frac{4096\|\chi_{s^\#}\|\|\chi_s\|}{G}.
\]

Both complete blocks are bounded before their outer powers are combined:
`-2 Re(s#) - 2 Re(s) = -2`. This holds throughout the critical strip and
has no `1/(2 sigma-1)` singularity. For `A=B=u^8`, `U=u^5`, `G=2u^4`,
the bound is `2048 norm(chi_s#) norm(chi_s) u^(-4)`.
`gcdCrossDiagonalTail_eighth_tendsto_zero` proves the resulting limit.
This estimate concerns the common-gcd diagonal only; it does **not** bound
all rows and columns with a large gcd index.

## Remaining obligation and next experiment

The controlled ranges leave two specific signed objects: the original
smaller-gcd core, and the reflected product's unequal-gcd interactions
together with its smaller-gcd diagonal. No estimate in this slice makes
either object beat the source or forces the two normalized energies to
agree. A positive outer coefficient is insufficient for either claim.

The next audit should compute the **full** matrix of actual gcd blocks,
its reflected off-diagonal contribution, and its source normalization
before applying absolute values. Any candidate inequality must account
for the explicit source budget and all retained cross terms. A test that
only bounds the reciprocal-square diagonal cannot settle the objective.
If reflection merely restates the missing inverse-zeta cancellation,
this branch should be reported as a reduction with controlled tails,
and the terminal mechanism reconsidered.

The exact identities and inequalities above are Lean theorems. No claim
of priority over existing analytic number theory is made for these
auxiliary results.

## Verification

All four new modules passed direct elaboration with warnings treated as
errors. The focused build passed (`4435` jobs), followed by the complete
root build (`9725` jobs). All 14 verbose root declaration-lint checks and
the whole-project declaration lint passed. The 12 audited terminal
theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The compiled inventory has 878 project modules, 18724 declarations, and
16106 theorems, with zero project axioms and zero placeholder-dependent
declarations. The compiled-environment soundness generator passed;
`rhImplied` remains false.
