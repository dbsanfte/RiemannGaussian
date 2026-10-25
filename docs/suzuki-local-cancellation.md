# Local Suzuki cancellation: formalization and arithmetic frontier

23 October 2026. Local research slice; RH remains open.

The subsequent repository search is recorded in
[suzuki-local-cancellation-paths.md](suzuki-local-cancellation-paths.md).
It identifies a bounded-cost Vaughan specialization and a distinct-prime
covariance target. The detailed
[Vaughan follow-up](suzuki-local-cancellation-vaughan.md) distinguishes
compiled sampling estimates from the paper-level complete sector reduction.

This implements the cancellation and conditional transfer proposed in
[`RH_LOCAL_SUZUKI_CANCELLATION_RESEARCH.md`](../RH_LOCAL_SUZUKI_CANCELLATION_RESEARCH.md).
The original note is retained unchanged. The remaining arithmetic premise is
exactly its target (T), uniformly over real cutoffs:

\[
\forall\varepsilon>0\;\exists C_\varepsilon\ge0, X_\varepsilon\ge2\;
\forall X\ge X_\varepsilon,\qquad
G(X)\ge-C_\varepsilon X^\varepsilon.
\]

## Checked identities and transfer

Set \(h=\log2\), \(c=\sqrt2\), and
\(\tau(v)=\max(0,h-|v-h|)\). The Lean definitions use the actual von
Mangoldt function, every prime power, the literal logarithms, and finite
windows whose endpoints are proved exact. They identify

\[
A(X)=\sum_n\frac{\Lambda(n)}{\sqrt n}\tau(\log(n/X)),
\qquad G(X)=cA(X)-A(2X).
\]

The following files supply the proof chain:

| File | Checked content |
|---|---|
| [SuzukiLocalCancellation.lean](../RiemannGaussian/SuzukiLocalCancellation.lean) | Positive-hinge second difference; zero endpoint terms; exact common finite window; \(U(t)=4(c-1)^2e^{t/2}-A(e^t)\); \(G(e^t)=U(t+h)-cU(t)\); four signal coefficients \(-c,1+2c,-(2+c),1\). |
| [SuzukiLocalCancellationKernel.lean](../RiemannGaussian/SuzukiLocalCancellationKernel.lean) | Piecewise signed kernel, exponential-mode multiplier, nonvanishing for \(0<\Re\lambda<1/2\), and the compact kernel's complex transform. |
| [SuzukiLocalCancellationBoundary.lean](../RiemannGaussian/SuzukiLocalCancellationBoundary.lean) | Unconditional PNT boundary for the actual signal and second difference; real-cutoff interpolation; \(G(X)/\sqrt X\to0\). |
| [SuzukiLocalCancellationTransfer.lean](../RiemannGaussian/SuzukiLocalCancellationTransfer.lean) | Exact finite recurrence inversion and second-difference reconstruction; uniform real-time bounds, compact initial data, finite-head absorption; target (T) implies literal RH. |
| [SuzukiLocalCancellationPrimePowers.lean](../RiemannGaussian/SuzukiLocalCancellationPrimePowers.lean) | Uniform proper-prime-power deletion bound on the original signed window. |
| [SuzukiLocalCancellationCriterion.lean](../RiemannGaussian/SuzukiLocalCancellationCriterion.lean) | Equivalence of (T) with its ordinary-prime version, and that version's conditional implication to RH. |
| [SuzukiLocalCancellationPhysical.lean](../RiemannGaussian/SuzukiLocalCancellationPhysical.lean) | Actual physical kernel, its exact three branches, change of variables, and zero density integral. |
| [SuzukiLocalCancellationSampling.lean](../RiemannGaussian/SuzukiLocalCancellationSampling.lean) | Actual lattice sum bounded by \(53/\sqrt X\), all real spacings; small-factor Vaughan cross term bounded by \(318UV/\sqrt X\). |
| [SuzukiLocalCancellationMoment.lean](../RiemannGaussian/SuzukiLocalCancellationMoment.lean) | Exact first logarithmic moment \(J=-4h\sqrt2(\sqrt2-1)^2\), including the physical and scaled integrals. |
| [SuzukiLocalCancellationLogSampling.lean](../RiemannGaussian/SuzukiLocalCancellationLogSampling.lean) | Log-weighted lattice error and the actual small-factor Möbius/logarithm block with its harmonic main term retained. |
| [SuzukiLocalCancellationSharedPrime.lean](../RiemannGaussian/SuzukiLocalCancellationSharedPrime.lean) | Exact finite shared-prime Möbius divisor cancellation, strict cutoff completion, and pure-prime-power exception. |
| [SuzukiLocalCancellationPrimitiveBound.lean](../RiemannGaussian/SuzukiLocalCancellationPrimitiveBound.lean) | Existing seven-eighths theorem applied to the complete smoothed prime primitive with multiplicities and trivial-zero contribution. |
| [SuzukiLocalCancellationExplicitBound.lean](../RiemannGaussian/SuzukiLocalCancellationExplicitBound.lean) | Twice-Abel source identity, full smooth-main annihilation, uniform-envelope transfer, and \(3\sqrt X/(\log X)^2\) bound for \(\log X\ge4900\). |
| [SuzukiLocalCancellationArithmeticBound.lean](../RiemannGaussian/SuzukiLocalCancellationArithmeticBound.lean) | Explicit \(X^{3/8}\) absolute and one-sided bounds for the actual ordinary-prime sum, uniformly for all real \(X\ge1\). |

The terminal theorem is
`riemannHypothesis_of_suzukiLocalArithmeticComparison_subpolynomial_lower_bound`.
Its sole premise is (T). In particular, the boundary condition is **proved**,
not added as a second hypothesis. The final existing Suzuki--Landau theorem
is applied with orientation `a = -1`, so it needs an upper bound on the
original signal.

The boundary proof reuses the repository's unconditional weighted-mass PNT
and canonical-gap cancellation. Exact comparison with the finite mass
potential gives the logarithmic average at integer endpoints; its entropy
term tends to zero because the actual mass ratio tends to one. A two-sided
cell bound of 16 transfers to all real endpoints. This proves
`suzukiLocalSignal_div_exp_tendsto_zero` and then
`suzukiLocalSecondDifference_lattice_boundary`. No zero-location premise is
introduced in this argument.

The recurrence argument bounds finite sums and takes a proved boundary
limit. It never assumes absolute convergence of an uncontrolled forcing
series. Reconstruction uses a uniform exponential supersolution for all
residues modulo \(\log2\); it retains the finite initial interval.

## Established bounds

The strongest exponent for the **complete** \(G\) transferred in Lean by
this slice is the existing seven-eighths baseline:

\[
|G(X)|\le192\left(\frac{463}{5000}+\frac{\pi^2}{24}\right)X^{3/8},
\qquad X\ge1.
\]

For the actual ordinary-prime sum this gives the concrete one-sided bound

\[
\boxed{G_{\rm pr}(X)\ge-200X^{3/8}\qquad(X\ge1).}
\]

In fact the corresponding absolute bound is proved. The numerical constant
200 bounds the more precise coefficient
\(192(463/5000+\pi^2/24)+54(\sqrt2+1)\log2\).
The terminal theorem is
`suzukiLocalOrdinaryArithmeticComparison_lower_bound_two_hundred`.
This is an application of the repository's attributed external baseline,
not a new zero-free region or an improvement of its exponent. The external
baseline and provenance are in
[ZetaQuasiRHOpenAI.lean](../RiemannGaussian/ZetaQuasiRHOpenAI.lean).
It does not establish (T), which requires every positive exponent.

The proof first bounds the actual smoothed primitive error by
\((463/5000+\pi^2/24)e^{7t/8}\). An exact twice-Abel identity, including
all four derivative jumps and three band integrals, annihilates the whole
smooth main term and bounds the output by \(24Be^{-t/2}\) whenever the
primitive error is at most \(B\) on \([t,t+3\log2]\). This provides the
explicit transfer without an unproved desmoothing assumption.

Independently of that seven-eighths input, the existing smoothed PNT theorem
gives \(|G(X)|\le3\sqrt X/(\log X)^2\) for \(\log X\ge4900\).
The earlier qualitative result also remains available:

\[
G(X)=o(\sqrt X),\qquad X\to\infty\text{ through real values}.
\]

Its theorem is `suzukiLocalArithmeticComparison_div_sqrt_tendsto_zero`.
This confirms the note's qualitative PNT boundary.

For the exact ordinary-prime restriction, this slice proves the explicit
uniform bound

\[
|G(X)-G_{\rm pr}(X)|\le54(\sqrt2+1)\log2\qquad(X\ge1).
\]

The theorem is `abs_suzukiLocalArithmeticComparison_sub_ordinary_le`.
The proof uses the previously checked estimate
\(\psi(y)-\vartheta(y)\le18\sqrt y\), the original support
\([X,8X]\), and the bounded signed kernel. The constant is deliberately
coarse; no prime power is discarded without payment. The theorem
`suzukiLocalArithmetic_lower_bound_iff_ordinary` adjusts the exponent-dependent
constants explicitly.

## Research and overlap audit

The derivation's signs, endpoint conventions, homogeneous boundary,
real-cutoff uniformity, and orientation `a = -1` check out. The search did
not establish historical novelty for this fixed dyadic filter.

Suzuki's [*Aspects of the screw function corresponding to the Riemann
zeta-function*](https://arxiv.org/html/2206.03682v4), Theorem 1.1, supplies the
primary context for the completed signal and its convergent zero expansion.
His [*On variants of Chebyshev's conjecture*](https://link.springer.com/article/10.1007/s11139-025-01238-9),
Theorem 1 and Corollary 1, already give closely related one-sided criteria;
Theorem 2 treats another density-cancelled sum. The
[publisher correction](https://link.springer.com/article/10.1007/s11139-025-01289-y)
was included in the literature audit.

The attempted arithmetic operation was the exact convolution
\(\Lambda=\mu*\log\), applied to the two packets together:

\[
G(X)=\sum_{d\le8X}\mu(d)
 \sum_m\frac{\log m}{\sqrt{dm}}W(\log(dm/X)).
\]

In its continuous inner approximation, density cancellation removes the
\(\log(X/d)\) contribution, but leaves
\[
\frac{\sqrt X}{d}M_W'(1/2),\qquad
M_W'(1/2)=-4\sqrt2(\log2)(\sqrt2-1)^2.
\]
Thus the signed harmonic Möbius term and the complementary large-divisor
sum remain coupled. Taking separate absolute values does not prove the
required lower bound. This investigation produced no independent
improvement to the complete signed \(G\) beyond the existing baseline.
The physical lattice bounds, first moment, small-factor logarithm block,
small-factor cross block, and finite shared-prime cancellation are now Lean
theorems. The complete Vaughan rearrangement and estimates for its remaining
sectors are still paper derivations.

A sharper paper reduction now pays every proper-prime-power and shared-prime
sector within \(O(X^\varepsilon)\) by choosing
\(U=\lfloor X^{\min(1/4,2\varepsilon)}\rfloor\). The remaining expression is
\(J\sqrt X\sum_{d\le U}\mu(d)/d\) joined to the exact coprime ordinary-prime
Vaughan term. Its lower bound remains open; the factoring notes do not
supply the required signed correlation. See the
[explicit error ledger](suzuki-local-cancellation-vaughan.md).

The subsequent whole-target review found no valid bound for every positive
exponent and no exponent contraction approaching zero. Exact quotient
grouping produces a signed Möbius sum whose lattice profile changes sign;
completing those divisor fibres restores the original ordinary-prime sum
plus the already bounded corrections. Assuming that restored sum has a
subpower bound would be circular. The existing analytic feedback maps and
semiprime inverse/projection constructions do not discharge this remaining
premise. Bounds for selected product ranges do not establish the requested
whole-sum result; the research objective remains unmet.

## Validation

The reproducible scoped gate is
[CheckSuzukiLocalCancellation.lean](../scripts/CheckSuzukiLocalCancellation.lean).
It imports the frozen ordinary root and all fourteen new modules, runs every
enabled declaration linter on their declarations, and checks every
transitive axiom dependency, including private helpers. Its machine-readable
report is written to `.lake/suzuki-local-cancellation/audit.json`.

The targeted build and complete scoped audit passed: fourteen modules, 236
declarations and 215 theorems including generated helpers, with all 15
enabled declaration linters passing. Every transitive axiom dependency is
among `propext`, `Classical.choice`, and `Quot.sound`. The tracked Lean
placeholder scan and whitespace checks also passed.

Run the targeted build and audit with the pinned toolchain:

```sh
lake build RiemannGaussian.SuzukiLocalCancellationArithmeticBound RiemannGaussian.SuzukiLocalCancellationLogSampling RiemannGaussian.SuzukiLocalCancellationCriterion RiemannGaussian.SuzukiLocalCancellationSharedPrime --wfail
lake env lean -DwarningAsError=true scripts/CheckSuzukiLocalCancellation.lean
```

This is local supporting and conditional work. It does not register new
dashboard milestones or change the public RH status.
