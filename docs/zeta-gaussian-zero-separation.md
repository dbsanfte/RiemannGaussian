# Finite Gaussian zero groups and boundary separation

[ZetaGaussianZeroSeparation](../RiemannGaussian/ZetaGaussianZeroSeparation.lean)
keeps a complete finite group of zeros in the phase-family inequality.
Their distinct heights survive until a quadratic cosine estimate controls
the displacement cost. This yields explicit restrictions on nearby zeros,
with every arithmetic premise discharged. The universal zero-free curve
and the remaining independent signed prime bound are unchanged.

## The actual zero-count and isolation statements

Write

```math
d(t)=\min\left\{\frac1{450000},\frac{32}{45\log(|t|+2)}\right\}.
```

For every central height `|t|>=1000000`, the closed right rectangle is

```math
\mathcal R_t^+=\{\rho=\beta+i\gamma:\quad
1-\beta\le2d(t),\quad |\gamma-t|\le d(t)/2\}.
```

`right_sum_le_one` proves, for every finite set `S` of actual nontrivial
zeros in that rectangle,

```math
\sum_{\rho\in S}\operatorname{mult}(\rho)\le1.
```

`left_sum_le_one` proves the same statement when the horizontal condition
is `beta<=2*d(t)`. The width is evaluated at the central height, not
separately at each member's height. There is no upper height ceiling.
Theorems `eq_of_mem_right_rectangle` and `eq_of_mem_left_rectangle`
give uniqueness directly. These rectangles can contain one simple zero;
they are not additional zero-free regions.

For two distinct actual zeros in the common right layer of depth `2*d(t)`,
with `t` the first zero's height, `ordinate_separation` gives
`abs(gamma-t)>d(t)/2`.

The stronger geometric consequence `distance_separation` applies to every
other nontrivial zero, without a location condition on that other zero:

```math
\begin{gathered}
\rho=\beta+it,\quad |t|\ge10^6,\quad
\min\{\beta,1-\beta\}\le\frac32d(t),\quad \tau\ne\rho
\\
\Longrightarrow\quad |\tau-\rho|>d(t)/2.
\end{gathered}
```

Any hypothetical neighbor at distance at most `d(t)/2` would put both
zeros in the same rectangle. Thus the conclusion follows from the full
multiplicity count. `inverse_distance_bound` also proves

```math
\frac1{|\tau-\rho|}<\frac2{d(t)}.
```

This bounds each inverse-distance factor used in zero isolation. It does
not by itself bound a growing product, its number of factors, transformed
spectral-coordinate denominators, or the coefficients of a whole filter.
The subsequent [complete filter-cost theorem](zeta-zero-filter-cost.md)
discharges these costs for the original pole-jet filter in the right
isolation layer using exact Mahler identities and a global Poisson count.
The independent signed prime bound remains open.

## The information retained in the proof

The theorem
[`finite_source_add_mixedWork_le_exactBudget`](../RiemannGaussian/ZetaGaussianStripPhaseFamily.lean)
generalizes the existing aligned singleton argument to an arbitrary
finite zero set and central height. For every eligible countable phase
family it keeps

```math
a_1\sum_{\rho\in S}\mathcal Q_{B,\eta,s}(\rho)
+\mathcal W_{\rm Gaussian}
+\mathcal W_{\rm Euler}
+\mathcal W_{\rm boundary}
\le\mathcal B_{\rm exact}.
```

Here `Q` is the original compensated source, including actual multiplicity,
the complete Gaussian-cotangent contribution and its own shifted Poisson
reserve. Each zero retains its complex displacement `s-rho`. All three
prime responses retain their shared phase kernel; their nonnegativity is
used only in the downstream scalar count. The old singleton theorem now
follows by specialization of this more general statement.

[GaussianComplexDisplacement](../RiemannGaussian/GaussianComplexDisplacement.lean)
proves a general estimate for the original half-line transform

```math
H_B(z)=\int_0^\infty e^{-Bu^2-zu}\,du,\qquad
B>0,\quad \Re z\ge0:
```

```math
\Re H_B(z)\ge H_B(\Re z)
-\frac{(\Im z)^2}{4B}H_B(0).
```

The proof integrates the global cosine inequality `cos(v)>=1-v^2/2`.
The exact second Gaussian moment follows from the existing full complex
integration-by-parts recurrence. Every integral is proved integrable; the
real projection and integral interchange are justified explicitly.

The analytic cotangent-minus-pole correction has lower real bound
`-1/eta` on the complete right half-disc of radius `eta`. The half-disc
minimum principle proves this without separating two singular terms at
the removed center. Combining the two estimates retains the large positive
Gaussian mass for zeros away from the central ordinate.

## Explicit budget and scope

Use the existing parameters

```math
q\ge1,\quad w=\frac1{450000q},\quad x=w/1000,
\quad B=4w^2,\quad\eta=\delta_9+x.
```

For horizontal depth at most `2*w` and vertical displacement at most `w/2`,
`compensated_lower` proves a contribution of at least `80000*q` per unit
of actual multiplicity. The first phase coefficient is at least `79/250`.
Two units therefore contribute at least `50560*q`, exceeding the complete
independent budget `47500*q`. The bound holds for every family satisfying
the existing coefficient, mass and frequency-cost enclosures. The exact
contact family supplies those premises; no new coefficient search is used.

Choosing `q=max(1,log(abs(t)+2)/320000)` gives the displayed function `d(t)`.
The [multiplicity theorem](zeta-gaussian-multiplicity-depth.md) still has
its larger simplicity-only layer of depth `(13/6)*d(t)`. The new rectangle
and isolation conclusions have their own, smaller horizontal depths.
No comparison with external separation theorems or historical novelty
claim is made here.

The independent signed prime floor needed for the RH contradiction is
still open. This slice removes the possibility of arbitrarily close
distinct zeros in the stated layer and controls individual inverse-distance
factors. It does not establish cancellation between prime windows or
exclude an isolated simple zero.

## Validation and navigation

Both new modules are root-imported. Verification covers strict direct
elaboration, focused and full builds, whole-project declaration lint,
terminal axiom audits, compiled status generation, source scans and the
generated family index. The explorer's `Separation` endpoint exposes both
rectangle counts and the inverse-distance theorem, with source lines and
transitive axiom audits. Its default endpoint remains the universal
zero-free curve. This work remains local under the commit hold.
