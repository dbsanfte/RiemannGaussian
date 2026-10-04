# What is still needed for the joined floor

This is an applicability check, not a new arithmetic payment. The floor
remains open, and this investigation assigns **zero new floor credit**.
The existing proofs, numerical snapshots and negative audits are unchanged.

The target is the existing, already source-normalized quantity

\[
\operatorname{Re}\mathrm{prefixPairDefect}(u,y,N_j)
\le \frac{399}{5000}+\varepsilon_j,
\qquad N_j\to\infty,\quad\varepsilon_j\to0,
\]

for every fixed \(|y|\ge54\) and \(1/2<u\le10001/20000\). There is no
additional factor \(u^{N+1}\) to apply to `prefixPairDefect`.
[The checked endpoint](../RiemannGaussian/ZetaRieszPairFloorAllMultiplicity.lean)
retains the arithmetic estimate as a premise. It would exclude all positive
analytic multiplicities in the strip \(\operatorname{Re}\rho\ge19999/20000\).
It does not prove that estimate.

## The exact algebra has already been spent

[The prefix convolution](../RiemannGaussian/ZetaRieszPairPrefixConvolution.lean)
cancels the unlogged order-zero endpoints before taking real parts.
[The joined quadratic](../RiemannGaussian/ZetaRieszPairJointQuadratic.lean)
keeps the remaining central, successor and logged-prefix orders, adds the
full Selberg trace and subtracts the repeated-prime diagonal exactly once.
The trace has positive scalar coefficients; it does not cancel another
central monomial. No further zero coefficients were found in the existing
exact coefficient collection.

The stronger integer identity is available:

\[
\Lambda\log+\Lambda*\Lambda=\mu*\log^2.
\]

[Its complex weighted form](../RiemannGaussian/SuzukiLogarithmicConvolution.lean)
preserves every phase. However, it is an equality rather than a signed
estimate for the coupled factorial weights. For example, at distinct
primes \(p,q\), the right side is \(2\log p\log q\), the same positive
coefficient as the ordered prime-pair convolution. It does not provide
an additional negative credit on that label.

The conditional exposed-zero calculation is consequently still
\(m^2(1-c_{\rm ret}(u))\). At the radius ceiling its simple-source value is
approximately \(0.079871797\), above \(0.0798\). That difference is a
contradiction margin, not an estimate of unpaid arithmetic mass.

## The earlier floor has no unspent aggregate reserve

The focused optional check
[`CheckRieszNoUnusedFloorCredit.lean`](../scripts/CheckRieszNoUnusedFloorCredit.lean)
also tests whether returning to the earlier whole-sum inequality could
recover a discarded fixed positive credit. Write \(N=N_j\) and

\[
G_j=\operatorname{Re}(u^{N+1}\mathrm{coreResponse}_j)
 +\operatorname{Re}\mathrm{prefixPairDefect}_N
 +\operatorname{Re}\mathrm{literalSelberg}_N.
\]

The check proves, independently of any zero hypothesis,

\[
|G_j|\le\mathrm{nativeSignedPeriodBudget}_j
 +\mathrm{prefixBudget}_{N_j}\longrightarrow0.
\]

It uses the existing **two-sided** native ledger and the exact signed
Selberg split, rather than just the later one-sided floor. Thus this
aggregate discrepancy cannot supply a fixed positive reserve, even along
a cofinal subsequence. Under the simple exposed-zero hypothesis the
Selberg term is already paid, leaving the same retained signed pair.

This does not assert that each earlier sector is nonnegative or small,
or deny possible cancellation inside the unpaid pair sum. It rules out
recovering a fixed aggregate credit from a gap already proved to vanish.
The four audit theorems pass the strict Lean check, all 14 namespace
linters and transitive axiom prints with only the standard axioms. No
arithmetic floor constant has improved.

## Literature inputs checked

| Input | What it supplies | Missing step for this carrier |
| --- | --- | --- |
| [Han, smooth weighted PNT and zero-free regions](https://arxiv.org/html/2505.23795v1), Theorem 1.1 | Transfers a supplied zero-free region into a smoothed error bound, and a supplied error bound back into a zero-free region | An independent error bound strong enough for the actual signed factorial sum |
| [Han, Theorems 1.2–1.3](https://arxiv.org/html/2505.23795v1) | Conditional implications from smoothed additive Goldbach averages | An established estimate, and a bridge from additive sums to the present multiplicative carrier |
| [Kaneko–Thorner, highly uniform PNT](https://arxiv.org/html/2203.09515v2) | Error estimates expressed through the available zero-free region for the covered L-functions | A stronger independent signed input; using the desired region here would be circular |
| [Tao, Banach-algebra PNT proof](https://terrytao.wordpress.com/2014/10/25/a-banach-algebra-proof-of-the-prime-number-theorem/) | Qualitative cancellation for fixed compact tests | A uniform quantitative estimate for the moving factorial test; this transplant was already rejected by the scoped rate audit |
| [Bochkov–Romanov, Theorem 2(1)](https://arxiv.org/html/2106.15949) | Ordinary-prime Euler products with arbitrary unit multiplicative coefficients and prescribed zeros in `21/40 < Re s < 1` | A bound must use the actual archimedean phase, rather than properties shared by arbitrary multiplicative phases |

These statements describe the hypotheses checked in these sources, not a
claim that every possible literature route has been ruled out. No new
theorem from these papers has been imported into Lean.

## Fixed phase is essential, but fixed-moment strictness is insufficient

[`ZetaPrimeGram.norm_neg_logDeriv_riemannZeta_lt_real_axis`](../RiemannGaussian/ZetaPrimeGram.lean)
proves strict contraction at a fixed safe abscissa and nonzero height. It
does not supply a contraction rate for the growing factorial orders, or a
signed bound for the joined quadratic. Do not spend that strict inequality
as an additional cofinal floor credit.

The Helson result above is a stronger applicability warning than a model
with generalized primes. It retains ordinary primes and unit multiplicative
coefficients. The integer Selberg identity also survives multiplication by
such coefficients. Prescribing a single simple zero at
`39999/40000 + 55i` gives normalized ordinary-prime logarithmic moments with
selected limit `-1`: the local logarithmic derivative supplies that residue,
and proper prime powers are analytic in `Re s > 1/2`.

Substitution into the **existing** joined evaluator then gives the same
source `1 - retainedCost(20001/40000)`, strictly above `399/5000` by
`ZetaRieszPairFloorAllMultiplicity.target_lt_multiple_source`. This is an
inference from the cited construction and the local coefficient argument;
the Helson construction and this transfer have **not** been formalized here.
It is not a counterexample for the literal carrier or its masks: the freely
chosen coefficients need not equal `n^(-iy)` for any fixed `y`.

Consequently, ordinary prime support, unit multiplicativity and the twisted
Selberg equality alone cannot justify the proposed complete-quadratic bound.
The actual phase additionally satisfies

\[
\frac{(n+1)^{-iy}}{n^{-iy}}
=\exp\!\left(-iy\log(1+1/n)\right),\qquad n\ge1.
\]

An estimate using this fixed-height additive regularity would need to retain
the signed arithmetic coefficients. No such estimate is supplied by the
Gram theorem or by this literature audit. There is zero new arithmetic
floor saving, and no zero exclusion.

Fixed-phase regularity by itself is already countertested in Lean.
`ZetaRieszSelbergRenewalAudit.array_eq_phaseMoment` retains one exact
`exp(-iy*T)` phase at **every** factorial order; its positive continuous
density also satisfies the full second-convolution identity. Nevertheless
`cofinal_generic_floor_impossible` rejects the desired cofinal bound for
that model. The frozen regression reaches approximately `0.079845024` at
order `1048576` and tends to `0.079871797`, rather than staying below
`0.0798`. These are model values, not actual-prime measurements or new
threshold certificates. The model's extra real pole and incorrect count
residue remain essential scope restrictions; see the
[checked countertest](zeta-riesz-selberg-renewal-audit.md).

Thus the next candidate must use the fixed phase **together with a further
literal ordinary-integer/prime constraint**. Merely adding phase smoothness
to positive continuous density and Selberg convolution does not repair the
argument. This review reuses existing results and adds no signed estimate
for the actual carrier.

## Quantitative gate

[The existing rate audit](zeta-riesz-selberg-spectral-rate.md) checks the full
radial integral, without freezing its saddle:

\[
u^{N+1}\int_0^\infty \frac{T^N}{N!}
 e^{-T/2}e^{-\delta T}\,dT
=\left(\frac{u}{1/2+\delta}\right)^{N+1}.
\]

At \(u=10001/20000\), \(\delta=1/20000\) gives one at every order, while
\(\delta=1/10000\) gives \((10001/10002)^{N+1}\). The latter would be a
sufficient geometric rate **if** the corresponding arithmetic estimate
were proved. It remains unproved. This is a gate for that positive-error
transport, not a necessary condition on every possible signed-floor proof.

The next useful result must therefore bound the complete signed ordinary-
prime sum, or prove an additional arithmetic correlation that yields a
strict saving for it. Another source transfer, selected-mode error payment,
finite prime sample or qualitative PNT reformulation supplies no such
saving. An estimate may retain signed cancellation instead of proving a
norm bound, but it must retain the actual factorial weights and phases.

The local preservation check revalidated all 382 source/artifact pins in
the 21 preceding Riesz audits. Their Lean sources and probe snapshots were
not changed. The new focused slack audit stays outside the root and CI;
it adds no wider gate or exhaustive verification.
