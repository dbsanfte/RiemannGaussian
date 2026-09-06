# Eta overlap, signed endpoint corrections, and heat matrices

The user authorized implementation of this package on 2026-09-06, following
the completed [first eta heat program](rh-overnight-theorem-plan.md).
The aim is new auxiliary Lean mathematics combining the actual eta support,
phase colour, Gaussian heat, and mixed finite matrices. This is not a
zero-proportion certificate program. Priority of the proposed combined
results has not been established.

Every mathematical statement below is a target unless the implementation
ledger links to a checked theorem. Integrals use the literal alternating eta
intervals, with genuine measurability and integrability proofs. No assumed
averaging or second-order asymptotic premise qualifies as implementation.

## Implementation ledger

| Part | Checked result | Remaining work |
| --- | --- | --- |
| 1. Actual arithmetic overlap | [Exact eta/periodic-colour identity](../RiemannGaussian/EtaAlternatingReal.lean), [real-scale cell and primitive estimates](../RiemannGaussian/EtaOverlapAveraging.lean), [Wallis integral](../RiemannGaussian/EtaOverlapWallis.lean), [quantitative infinite-tail evaluation](../RiemannGaussian/EtaOverlapTail.lean), and [exact transport back to the logarithmic eta tail](../RiemannGaussian/EtaLogTailWallis.lean). | Complete for the scalar arithmetic tail; retain it as input to the weighted law. |
| 2. Two-endpoint finite part | [Scalar finite part](../RiemannGaussian/EtaLogFinitePart.lean), [uniform harmonic quadrature](../RiemannGaussian/EtaLogBoundaryFinitePart.lean), [weighted-tail freezing](../RiemannGaussian/EtaLogWeightedTail.lean), [cutoff decomposition](../RiemannGaussian/EtaLogWeightedEndpoint.lean), [uniform fixed-endpoint remainder](../RiemannGaussian/EtaLogTwoEndpoint.lean), and [full complex two-endpoint limit with scale offset](../RiemannGaussian/EtaLogTwoEndpointLimit.lean). | Complete; the actual second-order Gaussian application is now checked in part 3. |
| 3. Signed heat reflection | [Actual polynomial-phase finite part](../RiemannGaussian/EtaPolynomialMismatchFinitePart.lean), [global bound after subtraction](../RiemannGaussian/EtaWeightedFinitePartBound.lean), [damped complex domination and limit](../RiemannGaussian/EtaPolynomialFinitePartDomination.lean), [logarithmic endpoint profile](../RiemannGaussian/EtaPolynomialHeatProfile.lean), [full second-order heat law](../RiemannGaussian/EtaPolynomialHeatFinitePart.lean), and [signed reflection](../RiemannGaussian/EtaPolynomialHeatReflection.lean). | Complete. Preserve the signed law in every mixed matrix entry. |
| 4. Full mixed matrix | Not yet proved. | Apply the second-order law to every mixed entry, preserving the signed endpoint decomposition and any dimension cost. |
| 5. Completed-current audit | The [previous review](rh-overnight-signed-flux-review.md) identifies a support mismatch and missing completion/moment estimates. | Audit one exact proposed pairing with the new signed heat object. A remaining conjecture-strength estimate must be left open explicitly. |

Part 1 proves, for every real `0 < epsilon ≤ 1` and `0 < a ≤ 1`,

\[
\left|\int_a^\infty
 \frac{(A(y/\epsilon+y)-A(y/\epsilon))^2}{y^2}\,dy
 -\left[1-\log(\pi/2)-\log a\right]\right|
 \le \frac{4\epsilon}{a}+\frac{\epsilon}{a^2}.
\]

Here `A(x) = 1` exactly when `ceil(x)` is even. This right-closed convention
matches the eta intervals at their endpoints. The precise compiled terminal
theorem is `integral_Ioi_etaRescaledOverlap_div_sq_error_le`; at `a = 1`
the error is at most `5 * epsilon`. The proof retains the exact signed
integration-by-parts identity
`integral_etaOverlapError_div_sq_eq_primitive` upstream of the bound.

The scalar specialization of part 2 is now proved by
`pairedEtaMismatch_half_finite_part_tendsto`:

\[
 D_{1/2}(r)/r-\log(1/r)\longrightarrow\gamma_E-\log(\pi/2)
 \quad(r\to0^+).
\]

The proof retains a quantitative harmonic remainder at the existing cutoff:
with `epsilon = exp(r)-1` and `M = floor(1/(2r))`, the difference between
`D_(1/2)(r)/epsilon + log(epsilon)` and
`harmonic(M)-log(M)-log(pi/2)` is at most `32*epsilon` for `0 < r ≤ 1/8`.
Changing normalization back to `r` includes a separate proof that the
singular logarithmic correction vanishes. Constant complex tests inherit
the limit exactly.

Nonconstant complex tests now have the following uniform decomposition,
proved by `pairedEtaWeightedMismatch_cutoff_endpoint_error_le`. For
`0 < r ≤ 1/8`, `R > 0`, `epsilon = exp(r)-1`, and the same actual cutoff `M`,

\[
 \epsilon^{-1}W(r,R,F)=\int_0^{\log(M+1)}F(t/R)\,dt
 +(H_M-1-\log(M+1))F(0)
 +(1-\log(\pi/2)-\log(\epsilon M))F(\log M/R)+E,
\]

with `norm(E) ≤ 8K/R + 32*epsilon*B` whenever `F` is `K`-Lipschitz and
`norm(F(x)) ≤ B` everywhere. This uses a `3K/R` harmonic quadrature remainder,
the actual tail's `K/(R*M)` freezing estimate, and its scalar Wallis value.
The cutoff is now cancelled exactly by
`pairedEtaShiftBoundaryCutoff_endpoint_cancel`. With `d_r = log(1/r)-R`
and `A_M = harmonic(M)-1-log(M+1)`, the stronger theorem
`pairedEtaWeightedMismatch_endpoint_error_le` gives

\[
 \left\|r^{-1}W-R\int_0^1F-A_MF(0)-(c_1+d_r)F(1)\right\|
 \le rB(140+R+|d_r|)+(K/R)(76+12d_r^2).
\]

For any positive real displacements `r -> 0`, scales `R -> infinity`, and
offset `log(1/r)-R -> d`,
`pairedEtaWeightedMismatch_two_endpoint_tendsto` proves

\[
 r^{-1}W-R\int_0^1F\longrightarrow c_0F(0)+(c_1+d)F(1).
\]

The critical case and the exponential parametrization are separate compiled
corollaries. In particular,
`pairedEtaWeightedMismatch_exp_scaled_finite_part_tendsto` retains the
`-log(v)` upper-endpoint term for every fixed `v > 0` when
`r = exp(-R)*v`. These complete parts 1 and 2. The actual phase comparison at scale `h` and Gaussian domination after
subtraction are now proved, as detailed below. They use quantitative error
bounds, rather than subtracting two first-order limits.

## 1. Arithmetic averaging on the actual carrier

Let `chi` indicate the union of `(log(2n+1), log(2n+2)]`. The substitutions
`x = exp(t)`, `epsilon = exp(r)-1`, and `y = epsilon*x` turn its mismatch into

\[
 g_\epsilon(y)=(A(y/\epsilon+y)-A(y/\epsilon))^2.
\]

The exact period average is the triangular wave `q`, equal to `y` on
`[0,1]`, `2-y` on `[1,2]`, and periodic with period two. The mismatch is
periodic with period one in its observation coordinate. Freezing the slow
displacement on a cell of length `epsilon` gives error at most
`2 * epsilon^2`, uniformly in the cell origin. Summing complete cells and
retaining the last incomplete cell gives

\[
 \left|\int_a^b(g_\epsilon-q)\right|
 \le 2\epsilon(b-a)+\epsilon.
\]

Integration by parts against `y^-2` gives the infinite-tail estimate above.
The constant follows from exact consecutive-cell integration and Mathlib's
Wallis product theorem. This works for all sufficiently small real scales,
not just a rational sequence of dilation ratios.

## 2. Complex weighted two-endpoint correction

Use the existing `pairedEtaWeightedMismatch` definition

\[
 W(r,R,F)=\int_0^\infty e^{-t}(\chi(t+r)-\chi(t))^2 F(t/R)\,dt.
\]

For `r = exp(-R)` and bounded Lipschitz `F : R -> C`, prove

\[
 \frac{W(r,R,F)}r-R\int_0^1F(z)\,dz
 \longrightarrow c_0F(0)+c_1F(1),\qquad
 c_0=\gamma_E-1,\quad c_1=1-\log(\pi/2).
\]

First establish the scalar specialization, then an estimate uniform in
families with fixed test bound and Lipschitz constant. Keep the finite
crossing sum and complex infinite tail separate until their cutoff terms
cancel. The current first-order `O(r)` remainder does not evaluate this
finite part.

## 3. Quadratic/cubic phase and signed heat reflection

Set `R = log(1/h)`, `sigma = 1/2 + lambda/R`, and

\[
 \phi_h(t)=\kappa t/h+b t^2/(2hR)+\alpha t^3/(hR^2),\qquad
 a(z)=\kappa+bz+3\alpha z^2.
\]

Reflection `a_rev(z)=a(1-z)` sends the parameters to
`(kappa+b+3*alpha, -b-6*alpha, alpha)`. The quadratic term makes this family
closed under reflection.

Write `Lambda_(lambda,a)(h)` for the actual support/gap heat integral with
this tilt and phase. Prove

\[
 \Lambda_{\lambda,a}(h)=hR\mathcal K_{\lambda,a}
       +h\mathcal L_{\lambda,a}+o(h),
\]

\[
 \mathcal K_{\lambda,a}=\frac1{\sqrt\pi}\int_0^\infty
 v e^{-v^2/4}\int_0^1e^{-2\lambda z}\cos(v a(z))\,dz\,dv,
\]

\[
 \mathcal L_{\lambda,a}=c_0\Psi(a(0))+
 e^{-2\lambda}[c_1\Psi(a(1))-\Omega(a(1))],
\]

where `Psi(s)` is the existing Gaussian cosine profile and

\[
 \Omega(s)=\frac1{\sqrt\pi}\int_0^\infty
 v e^{-v^2/4}\log(v)\cos(sv)\,dv.
\]

The logarithmic Gaussian moment is required because
`log(1/(hv)) = R-log(v)`. Prove phase comparison and domination after
subtraction at scale `h`; two `o(hR)` statements cannot supply `o(h)`.

The reflected combination
`B_h = Lambda_(lambda,a)(h) - exp(-2*lambda)*Lambda_(-lambda,a_rev)(h)`
has exactly cancelling leading profiles. The target is

\[
 B_h/h\longrightarrow J(a(0))-e^{-2\lambda}J(a(1)),\qquad
 J=(c_0-c_1)\Psi+\Omega.
\]

The phase comparison and pointwise finite part are now checked. With
`h = exp(-R)`, `R >= 1`, `R >= 4*abs(lambda)`, and `v >= 0`,
`pairedEtaPhaseMismatch_polynomial_test_error_le` bounds the difference
between the actual complex displacement and the bounded polynomial test by

\[
 h e^{4|\lambda|}\left[\frac{v^2(|b|+|\alpha|(6+v))}{R}+3h\right].
\]

The local phase error retains `h/R`; the two omitted time tails retain
`h^2`. Hence `pairedEtaPhaseMismatch_polynomial_finite_part_tendsto`
proves the actual complex displacement finite part for every fixed `v > 0`.
The extension has the explicit Lipschitz constant
`exp(4*abs(lambda)) * (2*abs(lambda) + abs(v)*(abs(b)+12*abs(alpha)))`.
The exact test reflection is
`pairedEtaPolynomialBoundaryTest_reflection`.

The complete Gaussian passage is now proved. The global weighted majorant
`norm_pairedEtaWeightedMismatch_finite_part_le` holds for every `v > 0`,
including the region `exp(-R)*v > 1/8`. Combining it with the phase error and
moving damping gives an explicit cubic polynomial majorant, integrable
against the heat Gaussian. The full complex damped finite part is retained
upstream of its real projection. The logarithmic Gaussian moment is proved
integrable even at zero, and its exact signed contribution is evaluated.

The terminal theorem
`pairedEtaSupportGapGaussianLeakage_polynomial_finite_part_tendsto` proves
the second-order heat law in the original positive width. The leading
profile reflection is an exact integral identity. Consequently
`pairedEtaSignedPolynomialHeat_tendsto` proves the signed endpoint limit
above. These complete part 3; no positivity is inferred for this signed
combination, and the xi completion multiplier has not been substituted by
the logarithmic reflection weight.

## 4. Mixed matrix and 5. completed-current audit

Use differences of phase parameters to preserve every mixed entry of a
fixed finite family. Retain the signed matrix; subtracting the leading Gram
does not establish positive semidefiniteness. Any matrix-norm estimate must
retain its dependence on the family size.

The reflection factor `exp(-2*lambda)` comes from logarithmic time. It is
not the xi completion multiplier. The literal higher-multiplicity current
lives on support times support, where a single support/gap mismatch is zero.
An exact two-transition or polarized Dirichlet-form pairing must retain
completion weights, adjacent centered moments, ordinate colour, cutoff,
and the distinct multiplicity-one head. A representation alone does not
prove the required `(2N+1)`-weighted summability estimate.

Fixed-horizontal-tilt asymptotics and nonlinear Gram conditioning are reserve
targets. They do not replace the arithmetic finite part or signed heat law.

## Verification and publication

Each coherent slice must pass the focused warning-as-error build, root
imports, whole-project declaration lint, terminal axiom audit, full build,
generated inventory, placeholder scan, and whitespace checks. Commit through
the tracked hook, push, and require successful CI at that exact SHA before
starting the next slice. Keep this ledger and the README's two research
status sections current. No `13/18` certificate or RH proof is claimed.
