# Investigation: Anthropic certificate and zero-free region improvements

Recorded 2026-09-13 from the side conversation. This note preserves two
independent research opportunities for later action. It does not change the
active RH strategy or report a newly compiled theorem. Source inspection was
read-only; the working tree includes uncommitted mathematical progress, and
no new Lean build or CI verification was performed for this investigation.

| Investigation | Existing foundation | Proposed advance |
| --- | --- | --- |
| Anthropic zero-proportion certificate | Two proved existential improvements over the imported Montgomery–Taylor simple-critical-zero benchmark | Strengthen the uniform correlation inequality and transfer the gain through the existing counting theorem |
| Zero-free region | Explicit adaptive Gaussian curve plus an eventual log-log component | Recover visible budget slack, then investigate adaptive detector parameters, bootstrapping and complementary published regions |

## 1. Further improvement of the Anthropic certificate

### What the repository already proves

Let `h = Zeta23.ThmD.HD 1`, the exact imported Montgomery–Taylor constant.
The source describes it numerically as approximately 0.6725; the project
also proves the exact comparison `2/3 < h`.

[Zeta23Baseline](RiemannGaussian/External/Zeta23Baseline.lean) imports the
actual zero-count results with attribution to the
[pinned upstream source](vendor/zeta23/UPSTREAM.md).
[Zeta23Benchmark](RiemannGaussian/External/Zeta23Benchmark.lean) proves the
comparison with two thirds.

The terminal theorem
`externalZeta23_montgomeryTaylor_uncapped_strictly_stronger` in
[Zeta23InverseSamplingEndgame](RiemannGaussian/External/Zeta23InverseSamplingEndgame.lean#L1779)
proves existence of constants `h < C0 < C1`, each satisfying

```math
\forall\varepsilon>0\;\exists T_0\;\forall T\ge T_0,\qquad
(C_i-\varepsilon)N(T,2T)\le N_0^{\mathrm{simple}}(T,2T).
```

Here `N` counts all nontrivial zeros with analytic multiplicity in the
window `T < Im(rho) <= 2T`. The numerator counts literal simple zeros on
`Re(rho)=1/2`. These are unconditional statements about zeta, with no
remaining RH or arithmetic hypothesis in the terminal theorem.

The gains are existential. They do not establish a new explicit percentage
such as 68%, and must not be presented as a `17/25` or `13/18` certificate.
No `13/18` certificate is established by this chain. Improvement over this
imported benchmark also does not establish a world record or novelty of the
underlying method; the three-point mechanism has
[related prior work](https://github.com/ainta/zeta-simple-zeros/blob/main/docs/proof.md#3-the-3-point-certificate).

### The information that produces the improvement

For two consecutive normalized gaps `a,b >= 0`, retain all three
correlations `K(a)`, `K(b)` and `K(a+b)` from the Montgomery–Taylor kernel.
Their arguments obey an additive constraint. The energy is

```math
E(a,b)=2\bigl(K(a)^2+K(b)^2+K(a+b)^2\bigr).
```

In [MontgomeryTaylorInverseSampling](RiemannGaussian/MontgomeryTaylorInverseSampling.lean):

- `montgomeryTaylorKernel_no_additive_zero_below_six_pi` proves that the
  three correlations cannot all vanish when `a+b <= 6*pi`.
- `exists_montgomeryTaylorTripleEnergy_floor` upgrades this to a positive
  uniform floor on the complete compact triangle.
- `exists_montgomeryTaylorTripleAffineCertificates_strict` produces the
  two comparable certificates from the same compact-floor witness.

The matrix argument retains a convex spectral remainder before replacing
it by diagonal information. It then retains energy in disjoint triples,
while averaging three shifted packings to control their span cost. Relevant
interfaces are
[the literal zero-side argument](RiemannGaussian/External/Zeta23InverseSamplingZeroSide.lean)
and [the packing theorem](RiemannGaussian/External/Zeta23InverseSamplingPacking.lean).
This is a concrete benefit of preserving joint information through the proof.

### A precise target for a stronger certificate

The existing uncapped endpoint accepts `0 < A <= 3/2`, `B > 0` and the
uniform inequality

```math
\forall a,b\ge0,\qquad A\le\frac34 E(a,b)+B(a+b).
```

It then supplies the zero-proportion constant

```math
C(A,B)=\frac{3h-4\pi B}{3-A}.
```

See `thmD_endpoint_affine_concrete_uncapped` in
[the endgame](RiemannGaussian/External/Zeta23InverseSamplingEndgame.lean#L1633).
The existing compact construction uses `B=A/(6*pi)`, giving

```math
C(A)=h+\frac{A(h-2/3)}{3-A}.
```

Lean already proves strict monotonicity in `A` within the stated range.
A larger *admissible* `A` therefore gives a larger certified proportion.
The coefficient is constrained by the uniform energy inequality; it is
not a free parameter that may be increased without proof. The general
endpoint also permits investigating other feasible pairs `(A,B)`.

Recommended investigation order:

1. Strengthen the uniform energy-versus-span inequality over **all** gap
   configurations, retaining the additive relation throughout. Seek an
   analytic characterization or lower bound, rather than coefficient hunting.
2. If that stalls, investigate larger blocks and stronger spectral
   remainders. Account for packing density, span costs and endpoint errors
   together; more entries do not automatically improve the final quotient.
3. Test relative phases and fourth moments against the actual Zeta23
   matrix. The repo has a
   [fourth-moment counting interface](RiemannGaussian/External/Zeta23FourthMomentCertificate.lean)
   and [quartic phase-colour identities](RiemannGaussian/External/Zeta23FourthMomentPhaseColour.lean).
   Their useful quantitative moment bounds still have to be proved and
   transported through the analytic endgame.

A useful obstruction is already formalized:
`phaseTwist_mul_reflection_eq_sq` in
[Zeta23PhaseTwistZeroSide](RiemannGaussian/External/Zeta23PhaseTwistZeroSide.lean#L82)
shows that a scalar Hermitian unit phase cancels from the reflected product.
Relative phases between distinct channels can survive, as shown by
`cubicPhase_mul_reflection`. Merely inserting a scalar phase is insufficient
to improve this part of the certificate.

Success means a terminal theorem for the literal zero counts, with every
analytic premise discharged and a proved strict comparison against the
chosen existing constant. When comparing existential constructions, retain
their common witness or prove a separate comparison; unrelated existential
constants cannot simply be declared ordered. An explicit rational percentage
would be useful for reporting, but is not the principal structural target.

The newer edge zero-free region does not automatically improve the
critical-line proportion. Likewise, an optimizer for a different phase cost
does not transfer without a theorem connecting that cost to this matrix.
This averaged counting target does not require first closing the global RH
signed-carrier bound.

## 2. Further improvement of the zero-free region

### Current proved region and scope

Put `H=abs(t)`, `L=log(H+2)` and

```math
\mathcal C(L)=L+2052\log L+30240,\qquad
d(t)=\min\left\{\frac1{450000},\frac{221}{250\mathcal C(L)}\right\}.
```

For `H >= 10^6`, every nontrivial zero satisfies
`d(t) < Re(rho) < 1-d(t)`. Literal zeta nonvanishing also includes the
closed right edge. The explicit curve has no upper height ceiling.
See `exact_strip_min` and `nonvanishing` in
[ZetaGaussianRetainedRegion](RiemannGaussian/ZetaGaussianRetainedRegion.lean)
and [the complete cost explanation](docs/zeta-gaussian-retained-region.md).

The proved union also contains an eventual component of width
`A*log(log(H))/log(H)` for every fixed
`0 < A < 22*pi/(1525*log(2))`. Its threshold `T(A)` is coefficient-dependent
and has not been numerically evaluated. See
[ZetaLogLogZeroFree](RiemannGaussian/ZetaLogLogZeroFree.lean).
Preserve both height conditions when taking the maximum of these widths.

### Immediate candidate: recover the final budget slack

This is an informal deduction from existing estimates, **not a new compiled
zero-free theorem**.

For the existing admissible phase family and `q >= 1`,
`ZetaGaussianRetainedCost.budget_le` gives

```math
\mathrm{budget}\le36922q+\frac{\mathcal C(L)}{36}.
```

A hypothetical zero within width `1/(450000*q)` forces the budget to be
at least `48000*q`, using
`ZetaGaussianAllHeight.selected_source_lower` and the full source inequality.
The [cost](RiemannGaussian/ZetaGaussianRetainedCost.lean#L132) and
[source](RiemannGaussian/ZetaGaussianAllHeight.lean#L29) are already proved.

The displayed region uses `mathcal C(L) <= 397800*q`, producing budget
`<= 47972*q`. But the same estimates give a strict contradiction whenever

```math
\mathcal C(L)\le Dq,\qquad
D<36(48000-36922)=398808.
```

For example, choose

```math
D=398800,\qquad q(t)=\max\{1,\mathcal C(L)/398800\}.
```

Then the budget is at most `(48000-2/9)*q`, still strictly below the source.
The corresponding candidate width is

```math
d_{\mathrm{new}}(t)=
\min\left\{\frac1{450000},\frac{997}{1125\mathcal C(L)}\right\}.
```

Where both curves use their decreasing branches, the width ratio is exactly
`398800/397800 = 1994/1989`, an increase of approximately **0.2514%**.
The maximum plateau width stays `1/450000`; its range extends slightly.
Using `D=398808` would remove the strict surplus and is not justified by
these estimates alone. This is a small budget improvement, not new
arithmetic cancellation or a change in the asymptotic shape.

The next proof task would generalize the final cost criterion, instantiate
the new dilation, prove containment and strict improvement on the correct
height range, and recover the literal nonvanishing and eventual-union
theorems. Any larger squarefree Cauchy radius needs its own downstream
transport; it must not be silently substituted into older theorems.

### Larger research opportunities

1. **Optimize the complete detector budget over its analytic parameters.**
   The displayed curve fixes order `k=9`, Gaussian scale `B=4*w^2` and
   center shift `x=w/1000`. The upstream
   [complete phase-family theorem](RiemannGaussian/ZetaGaussianStripPhaseFamily.lean)
   permits other orders, scales and shifts, subject to its geometry and
   analytic hypotheses. Derive a general source-minus-cost criterion and
   investigate a height-dependent choice. Keep the existing proved phase
   family initially; optimizing this detector is distinct from hunting for
   ideal phase coefficients. Preserve the signed corrections and favorable
   zero contributions before estimating them. Larger gains are plausible,
   but no quantitative improvement from this route was established here.

2. **Bootstrap from the region already known to be zero-free.**
   Investigate whether it allows stronger boundary estimates or detector
   evaluation farther inside the strip, then prove a quantitative map from
   an input width to an improved output width. Such iteration is used in
   [Bellotti–Trudgian–Yang, Section 2, arXiv:2603.21490v1](https://arxiv.org/html/2603.21490v1#S2).
   For our machinery, all continuation, zero-avoidance, divisor and boundary
   estimates would need to be paid. The theorem should identify both a
   genuine gain and any limiting width; iteration is not an automatic route
   to the critical line.

3. **Formalize complementary published regions and combine their domains.**
   Vinogradov–Korobov widths have shape
   `c/((log H)^(2/3)*(log log H)^(1/3))`. For positive fixed constants this
   eventually exceeds either of our current asymptotic shapes. See the
   [primary zero-free-region paper](https://arxiv.org/html/2306.10680v1) and
   the [repository literature audit](docs/zero-free-literature-frontier.md).
   Existing comparisons of benchmark functions are not imports of their
   analytic proofs. A genuine Lean integration must discharge those proofs,
   preserve their heights and edge conventions, and then take the maximum
   of eligible widths. This would enlarge formalized coverage; independent
   mathematical novelty and record comparisons are separate questions.

For substantial original work, prioritize the general Gaussian parameter
budget and then test bootstrapping. For a small initial proof slice, the
`D=398800` slack calculation has a precise target and an already complete
upstream analytic chain.

## Resuming either investigation

Recheck the live source and [proof inventory](docs/proof-status.json) before
starting: this note is a dated snapshot, not evergreen theorem metadata.
Follow [AGENTS.md](AGENTS.md) and the user's current commit instructions for
any later implementation and validation. Promote a proposed improvement to
the README or explorer only after the actual terminal theorem and applicable
audits pass; preserve external attribution and the exact quantitative scope.

Both investigations offer regional or averaged progress without first
settling the remaining interior signed arithmetic bound. Neither finding
closes that bound or proves RH.
