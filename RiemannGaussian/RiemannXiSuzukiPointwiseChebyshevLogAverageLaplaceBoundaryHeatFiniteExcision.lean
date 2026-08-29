import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatFiniteRegularization

/-!
# Finite-divisor Cauchy--Green assembly for arithmetic boundary heat

The bounded-height xi divisor has already been replaced by one analytic
remainder plus a finite sum of exact principal parts.  This file assembles
those components at the level of rectangular Cauchy--Green identities.

The analytic remainder satisfies ordinary Cauchy--Green.  Every principal
part satisfies the checked one-puncture improper identity, and finite sums
preserve its limit for one common shrinking parameter.  The resulting object
is explicitly called the *termwise regularized area*: equality with one
geometrically perforated rectangle is a separate theorem and is not assumed
here.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-! ## Generic boundary linearity and congruence -/

/-- Boundary integrability is preserved by pointwise addition. -/
theorem rectangularBoundaryIntegrable_add
    {l r b u : ℝ} {f g : ℂ → ℂ}
    (hf : rectangularBoundaryIntegrable l r b u f)
    (hg : rectangularBoundaryIntegrable l r b u g) :
    rectangularBoundaryIntegrable l r b u (fun z => f z + g z) := by
  exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

/-- An arbitrary rectangular boundary integral is additive under the exact
side-integrability assumptions. -/
theorem rectangularBoundaryIntegral_add
    (l r b u : ℝ) {f g : ℂ → ℂ}
    (hf : rectangularBoundaryIntegrable l r b u f)
    (hg : rectangularBoundaryIntegrable l r b u g) :
    rectangularBoundaryIntegral l r b u (fun z => f z + g z) =
      rectangularBoundaryIntegral l r b u f +
        rectangularBoundaryIntegral l r b u g := by
  unfold rectangularBoundaryIntegral
  rw [intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

/-- Two functions with identical values on the four parametrized sides have
the same rectangular boundary integral.  No interior equality is needed. -/
theorem rectangularBoundaryIntegral_congr_of_eq_on_sides
    (l r b u : ℝ) (f g : ℂ → ℂ)
    (hbottom : ∀ a ∈ [[l, r]],
      f ((a : ℂ) + (b : ℂ) * Complex.I) =
        g ((a : ℂ) + (b : ℂ) * Complex.I))
    (htop : ∀ a ∈ [[l, r]],
      f ((a : ℂ) + (u : ℂ) * Complex.I) =
        g ((a : ℂ) + (u : ℂ) * Complex.I))
    (hright : ∀ y ∈ [[b, u]],
      f ((r : ℂ) + (y : ℂ) * Complex.I) =
        g ((r : ℂ) + (y : ℂ) * Complex.I))
    (hleft : ∀ y ∈ [[b, u]],
      f ((l : ℂ) + (y : ℂ) * Complex.I) =
        g ((l : ℂ) + (y : ℂ) * Complex.I)) :
    rectangularBoundaryIntegral l r b u f =
      rectangularBoundaryIntegral l r b u g := by
  have hb : (∫ a : ℝ in l..r,
      f ((a : ℂ) + (b : ℂ) * Complex.I)) =
      ∫ a : ℝ in l..r,
        g ((a : ℂ) + (b : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr hbottom
  have ht : (∫ a : ℝ in l..r,
      f ((a : ℂ) + (u : ℂ) * Complex.I)) =
      ∫ a : ℝ in l..r,
        g ((a : ℂ) + (u : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr htop
  have hr : (∫ y : ℝ in b..u,
      f ((r : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ in b..u,
        g ((r : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr hright
  have hl : (∫ y : ℝ in b..u,
      f ((l : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y : ℝ in b..u,
        g ((l : ℂ) + (y : ℂ) * Complex.I) :=
    intervalIntegral.integral_congr hleft
  unfold rectangularBoundaryIntegral
  rw [hb, ht, hr, hl]

/-! ## Cauchy--Green for the analytic remainder -/

/-- The smooth heat kernel times an arbitrary analytic remainder. -/
def suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
    (x tau : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiChebyshevLaplaceBoundaryHeatKernel x tau z * F z

/-- The explicit Cauchy--Green source of the heat-weighted analytic
remainder. -/
def suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
    (x tau : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau z * F z

/-- When the remainder is complex analytic, only the heat kernel contributes
to the product's Cauchy--Green source. -/
theorem complexCauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
    (x tau : ℝ) {F : ℂ → ℂ} {p : ℂ}
    (hF : AnalyticAt ℂ F p) :
    complexCauchyGreenSource
        (suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
          x tau F) p =
      suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
        x tau F p := by
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
    suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
  rw [complexCauchyGreenSource_mul_of_differentiableAt_complex
    (differentiableAt_real_suzukiChebyshevLaplaceBoundaryHeatKernel
      x tau p) hF.differentiableAt]
  exact congrArg (fun q : ℂ => q * F p)
    (cauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatKernel x tau p)

/-- Exact ordinary Cauchy--Green identity for the heat kernel times a
function analytic throughout the closed rectangle. -/
theorem suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder_rectangularCauchyGreen
    (x tau l r b u : ℝ) (F : ℂ → ℂ)
    (hF : ∀ p ∈ [[l, r]] ×ℂ [[b, u]], AnalyticAt ℂ F p) :
    rectangularBoundaryIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
          x tau F) =
      rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
          x tau F) := by
  let R : Set ℂ := [[l, r]] ×ℂ [[b, u]]
  let H :=
    suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder x tau F
  let G :=
    suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource x tau F
  have hFOn : AnalyticOnNhd ℂ F R := hF
  have hd : DifferentiableOn ℝ H R := by
    intro p hp
    exact
      (differentiableAt_real_suzukiChebyshevLaplaceBoundaryHeatKernel
          x tau p).differentiableWithinAt.mul
        ((hFOn p hp).differentiableAt.restrictScalars ℝ).differentiableWithinAt
  have hcompact : IsCompact R :=
    isCompact_uIcc.reProdIm isCompact_uIcc
  have hG : IntegrableOn G R := by
    exact
      ((continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
          x tau).continuousOn.mul hFOn.continuousOn).integrableOn_compact
        hcompact
  have hi : IntegrableOn (fun p : ℂ => complexCauchyGreenSource H p) R :=
    hG.congr_fun (fun p hp => by
      simpa [H, G] using
        (complexCauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
          x tau (hFOn p hp)).symm) hcompact.measurableSet
  have hboundary :=
    Complex.integral_boundary_rect_of_differentiableOn_real
      H ((l : ℂ) + (b : ℂ) * Complex.I)
        ((r : ℂ) + (u : ℂ) * Complex.I) (by simpa [R] using hd) (by
          simpa [R, complexCauchyGreenSource] using hi)
  calc
    rectangularBoundaryIntegral l r b u H =
        rectangularAreaIntegral l r b u
          (fun p => complexCauchyGreenSource H p) := by
      simpa [H, rectangularBoundaryIntegral, rectangularAreaIntegral,
        sub_eq_add_neg, complexCauchyGreenSource] using hboundary
    _ = rectangularAreaIntegral l r b u G := by
      unfold rectangularAreaIntegral
      apply intervalIntegral.integral_congr
      intro a ha
      apply intervalIntegral.integral_congr
      intro y hy
      simpa [H, G] using
        complexCauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
          x tau (hFOn (a + y * Complex.I) ⟨by simpa using ha,
            by simpa using hy⟩)

/-- The heat-weighted analytic remainder is integrable on all four sides of
any rectangle throughout which the remainder is analytic. -/
theorem rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
    (x tau l r b u : ℝ) (F : ℂ → ℂ)
    (hF : ∀ p ∈ [[l, r]] ×ℂ [[b, u]], AnalyticAt ℂ F p) :
    rectangularBoundaryIntegrable l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
        x tau F) := by
  apply rectangularBoundaryIntegrable_of_continuousOn_reProdIm
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
  exact
    (differentiable_real_suzukiChebyshevLaplaceBoundaryHeatKernel
        x tau).continuous.continuousOn.mul
      (show AnalyticOnNhd ℂ F ([[l, r]] ×ℂ [[b, u]]) from hF).continuousOn

/-- A heat-weighted principal part is integrable on the boundary of every
rectangle whose interior strictly contains its pole. -/
theorem rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_of_mem
    (x tau : ℝ) (L c : ℂ) (l r b u : ℝ)
    (hl : l < c.re) (hr : c.re < r)
    (hb : b < c.im) (hu : c.im < u) :
    rectangularBoundaryIntegrable l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c) := by
  have hK :=
    (differentiable_real_suzukiChebyshevLaplaceBoundaryHeatKernel
      x tau).continuous
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((hK.comp (by fun_prop)).mul
      (continuous_simplePoleKernel_horizontal L c
        (by linarith : b ≠ c.im))).intervalIntegrable _ _
  · exact ((hK.comp (by fun_prop)).mul
      (continuous_simplePoleKernel_horizontal L c
        (by linarith : u ≠ c.im))).intervalIntegrable _ _
  · exact ((hK.comp (by fun_prop)).mul
      (continuous_simplePoleKernel_vertical L c
        (by linarith : r ≠ c.re))).intervalIntegrable _ _
  · exact ((hK.comp (by fun_prop)).mul
      (continuous_simplePoleKernel_vertical L c
        (by linarith : l ≠ c.re))).intervalIntegrable _ _

/-! ## The termwise finite regularized area -/

/-- Common-radius sum of the four-rectangle improper-area approximations for
all genuine principal parts in one finite xi window.  This is a termwise
regularization; it is not definitionally a single multiply perforated region. -/
def suzukiChebyshevLaplaceBoundaryHeatFinitePrincipalPartAreaApproximation
    (x tau T l r b u q : ℝ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    rectangularAreaIntegralOutsideCenteredSquare l r b u
      (suzukiChebyshevLaplaceZeroCoordinate rho) q
      (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource x tau
        (analyticZetaZeroMultiplicity rho : ℂ)
        (suzukiChebyshevLaplaceZeroCoordinate rho))

/-- The analytic-remainder area plus the common-radius finite principal-part
area approximation. -/
def suzukiChebyshevLaplaceBoundaryHeatFiniteRegularizedAreaApproximation
    (x tau T l r b u q : ℝ) (F : ℂ → ℂ) : ℂ :=
  rectangularAreaIntegral l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
        x tau F) +
    suzukiChebyshevLaplaceBoundaryHeatFinitePrincipalPartAreaApproximation
      x tau T l r b u q

/-- Exact finite-divisor termwise regularized Cauchy--Green identity.  Lean
constructs an analytic remainder `F` on the complete finite slab.  If the
chosen outer rectangle lies in that slab and strictly contains every zero in
the finite window, then the common-radius regularized area converges to the
actual arithmetic outer boundary minus `2*pi*i` times the complete finite
heat-residue sum.

This theorem does not identify the termwise regularization with a single
multiply perforated area; that geometric equivalence remains separate. -/
theorem exists_tendsto_suzukiChebyshevLaplaceBoundaryHeatFiniteRegularizedAreaApproximation
    (x tau l r b u : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hrectangle : [[l, r]] ×ℂ [[b, u]] ⊆
      suzukiChebyshevLaplaceFiniteSlab T)
    (hinside : ∀ rho ∈ spectralZetaZeroWindow T,
      l < (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).re < r ∧
      b < (suzukiChebyshevLaplaceZeroCoordinate rho).im ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).im < u) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ suzukiChebyshevLaplaceFiniteSlab T,
        AnalyticAt ℂ F z) ∧
      Tendsto
        (fun q : ℝ =>
          suzukiChebyshevLaplaceBoundaryHeatFiniteRegularizedAreaApproximation
            x tau T l r b u q F)
        (𝓝[>] 0)
        (𝓝 (rectangularBoundaryIntegral l r b u
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
          (2 * Real.pi * Complex.I) *
            ∑ rho ∈ spectralZetaZeroWindow T,
              suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                  (suzukiChebyshevLaplaceZeroCoordinate rho) *
                (analyticZetaZeroMultiplicity rho : ℂ))) := by
  let W := spectralZetaZeroWindow T
  let P : NontrivialZetaZero → ℂ → ℂ := fun rho =>
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau
      (analyticZetaZeroMultiplicity rho : ℂ)
      (suzukiChebyshevLaplaceZeroCoordinate rho)
  obtain ⟨F, hF, hdecomp⟩ :=
    exists_suzukiChebyshevLaplaceBoundaryHeatWeightedResponse_finitePrincipalPartDecomposition
      x tau hT
  let H : ℂ → ℂ :=
    suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder x tau F
  let PSum : ℂ → ℂ := fun z => ∑ rho ∈ W, P rho z
  have hFRectangle : ∀ z ∈ [[l, r]] ×ℂ [[b, u]], AnalyticAt ℂ F z :=
    fun z hz => hF z (hrectangle hz)
  have hHCG : rectangularBoundaryIntegral l r b u H =
      rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
          x tau F) := by
    simpa [H] using
      suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder_rectangularCauchyGreen
        x tau l r b u F hFRectangle
  have hHInt : rectangularBoundaryIntegrable l r b u H := by
    simpa [H] using
      rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
        x tau l r b u F hFRectangle
  have hPInt : ∀ rho ∈ W,
      rectangularBoundaryIntegrable l r b u (P rho) := by
    intro rho hrho
    have hi := hinside rho (by simpa [W] using hrho)
    simpa [P] using
      rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_of_mem
        x tau (analyticZetaZeroMultiplicity rho : ℂ)
          (suzukiChebyshevLaplaceZeroCoordinate rho) l r b u
          hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hPSumInt : rectangularBoundaryIntegrable l r b u PSum := by
    simpa [PSum] using
      rectangularBoundaryIntegrable_finsetSum l r b u W P hPInt
  have hnotBottom (a : ℝ) :
      (a : ℂ) + (b : ℂ) * Complex.I ∉
        suzukiChebyshevLaplaceZeroWindow T := by
    intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, heq⟩
    have him : (suzukiChebyshevLaplaceZeroCoordinate rho).im = b := by
      simpa using congrArg Complex.im heq
    linarith [(hinside rho hrho).2.2.1]
  have hnotTop (a : ℝ) :
      (a : ℂ) + (u : ℂ) * Complex.I ∉
        suzukiChebyshevLaplaceZeroWindow T := by
    intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, heq⟩
    have him : (suzukiChebyshevLaplaceZeroCoordinate rho).im = u := by
      simpa using congrArg Complex.im heq
    linarith [(hinside rho hrho).2.2.2]
  have hnotRight (y : ℝ) :
      (r : ℂ) + (y : ℂ) * Complex.I ∉
        suzukiChebyshevLaplaceZeroWindow T := by
    intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, heq⟩
    have hre : (suzukiChebyshevLaplaceZeroCoordinate rho).re = r := by
      simpa using congrArg Complex.re heq
    linarith [(hinside rho hrho).2.1]
  have hnotLeft (y : ℝ) :
      (l : ℂ) + (y : ℂ) * Complex.I ∉
        suzukiChebyshevLaplaceZeroWindow T := by
    intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, heq⟩
    have hre : (suzukiChebyshevLaplaceZeroCoordinate rho).re = l := by
      simpa using congrArg Complex.re heq
    linarith [(hinside rho hrho).1]
  have hboundaryCongr : rectangularBoundaryIntegral l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) =
      rectangularBoundaryIntegral l r b u (fun z => PSum z + H z) := by
    apply rectangularBoundaryIntegral_congr_of_eq_on_sides
    · intro a ha
      simpa [PSum, P, H,
        suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder] using
        hdecomp ((a : ℂ) + (b : ℂ) * Complex.I) (hnotBottom a)
    · intro a ha
      simpa [PSum, P, H,
        suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder] using
        hdecomp ((a : ℂ) + (u : ℂ) * Complex.I) (hnotTop a)
    · intro y hy
      simpa [PSum, P, H,
        suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder] using
        hdecomp ((r : ℂ) + (y : ℂ) * Complex.I) (hnotRight y)
    · intro y hy
      simpa [PSum, P, H,
        suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder] using
        hdecomp ((l : ℂ) + (y : ℂ) * Complex.I) (hnotLeft y)
  have hboundaryDecomp : rectangularBoundaryIntegral l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) =
      (∑ rho ∈ W, rectangularBoundaryIntegral l r b u (P rho)) +
        rectangularBoundaryIntegral l r b u H := by
    calc
      _ = rectangularBoundaryIntegral l r b u (fun z => PSum z + H z) :=
        hboundaryCongr
      _ = rectangularBoundaryIntegral l r b u PSum +
          rectangularBoundaryIntegral l r b u H :=
        rectangularBoundaryIntegral_add l r b u hPSumInt hHInt
      _ = _ := by
        rw [show rectangularBoundaryIntegral l r b u PSum =
            ∑ rho ∈ W, rectangularBoundaryIntegral l r b u (P rho) by
          simpa [PSum] using
            rectangularBoundaryIntegral_finsetSum l r b u W P hPInt]
  have hprincipalLimit : Tendsto
      (fun q : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatFinitePrincipalPartAreaApproximation
          x tau T l r b u q)
      (𝓝[>] 0)
      (𝓝 (∑ rho ∈ W, (
        rectangularBoundaryIntegral l r b u (P rho) -
          (2 * Real.pi * Complex.I) *
            (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                (suzukiChebyshevLaplaceZeroCoordinate rho) *
              (analyticZetaZeroMultiplicity rho : ℂ))))) := by
    unfold suzukiChebyshevLaplaceBoundaryHeatFinitePrincipalPartAreaApproximation
    exact tendsto_finsetSum W fun rho hrho => by
      have hi := hinside rho (by simpa [W] using hrho)
      simpa [P] using
        tendsto_rectangularAreaIntegralOutsideCenteredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
          x tau l r b u (analyticZetaZeroMultiplicity rho : ℂ)
            (suzukiChebyshevLaplaceZeroCoordinate rho)
            hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
  have hareaConst : Tendsto
      (fun _ : ℝ => rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
          x tau F))
      (𝓝[>] 0)
      (𝓝 (rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
          x tau F))) := tendsto_const_nhds
  have hfullLimit := hareaConst.add hprincipalLimit
  change Tendsto
      (fun q : ℝ =>
        suzukiChebyshevLaplaceBoundaryHeatFiniteRegularizedAreaApproximation
          x tau T l r b u q F)
      (𝓝[>] 0)
      (𝓝 (rectangularAreaIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
            x tau F) +
        ∑ rho ∈ W, (
          rectangularBoundaryIntegral l r b u (P rho) -
            (2 * Real.pi * Complex.I) *
              (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                  (suzukiChebyshevLaplaceZeroCoordinate rho) *
                (analyticZetaZeroMultiplicity rho : ℂ))))) at hfullLimit
  have hvalue : rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource
          x tau F) +
      (∑ rho ∈ W, (
        rectangularBoundaryIntegral l r b u (P rho) -
          (2 * Real.pi * Complex.I) *
            (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                (suzukiChebyshevLaplaceZeroCoordinate rho) *
              (analyticZetaZeroMultiplicity rho : ℂ)))) =
      rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        (2 * Real.pi * Complex.I) *
          ∑ rho ∈ W, (
            suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                (suzukiChebyshevLaplaceZeroCoordinate rho) *
              (analyticZetaZeroMultiplicity rho : ℂ)) := by
    rw [← hHCG, Finset.sum_sub_distrib, Finset.mul_sum, hboundaryDecomp]
    ring
  rw [hvalue] at hfullLimit
  refine ⟨F, hF, ?_⟩
  simpa [W] using hfullLimit

end

end RiemannGaussian
