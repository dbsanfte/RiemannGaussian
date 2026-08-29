import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatExcision

/-!
# Simple-pole excision for arithmetic boundary heat

Finite divisor excision will regularize the pole-cleared arithmetic response
by subtracting a finite sum of principal parts.  This file proves the exact
one-puncture Cauchy--Pompeiu interface needed for every summand of that finite
sum.

For the non-holomorphic heat kernel `K` and an arbitrary simple pole
`L / (z - c)`, Lean proves Cauchy--Green on rectangles avoiding `c`, computes
the shrinking-square contribution as `2 * pi * i * K(c) * L`, and identifies
the corresponding improper four-rectangle area limit.  No area integrability
through the pole and no exchange of limits is assumed.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Metric Set
open scoped Interval Topology

/-! ## The heat-weighted principal part -/

/-- The smooth boundary-heat kernel times an arbitrary simple principal
part. -/
def suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
    (x tau : ℝ) (L c : ℂ) (z : ℂ) : ℂ :=
  suzukiChebyshevLaplaceBoundaryHeatKernel x tau z *
    simplePoleKernel L c z

/-- The Cauchy--Green source of the heat-weighted principal part away from
its pole. -/
def suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
    (x tau : ℝ) (L c : ℂ) (z : ℂ) : ℂ :=
  suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource x tau z *
    simplePoleKernel L c z

/-- The heat-weighted principal part is continuous away from its pole. -/
theorem continuousOn_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
    (x tau : ℝ) (L c : ℂ) :
    ContinuousOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c)
      ({c} : Set ℂ)ᶜ := by
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
  exact
    (differentiable_real_suzukiChebyshevLaplaceBoundaryHeatKernel
        x tau).continuous.continuousOn.mul
      (differentiableOn_simplePoleKernel_of_not_mem L c (by simp)).continuousOn

/-- A continuous function on a closed rectangle is integrable on all four
parametrized sides. -/
theorem rectangularBoundaryIntegrable_of_continuousOn_reProdIm
    {l r b u : ℝ} {f : ℂ → ℂ}
    (hf : ContinuousOn f ([[l, r]] ×ℂ [[b, u]])) :
    rectangularBoundaryIntegrable l r b u f := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousOn.intervalIntegrable
    simpa [Function.comp_def] using hf.comp
      (by fun_prop : ContinuousOn
        (fun a : ℝ => (a : ℂ) + (b : ℂ) * Complex.I) [[l, r]])
      (fun a ha => ⟨by simpa using ha, by simp⟩)
  · apply ContinuousOn.intervalIntegrable
    simpa [Function.comp_def] using hf.comp
      (by fun_prop : ContinuousOn
        (fun a : ℝ => (a : ℂ) + (u : ℂ) * Complex.I) [[l, r]])
      (fun a ha => ⟨by simpa using ha, by simp⟩)
  · apply ContinuousOn.intervalIntegrable
    simpa [Function.comp_def] using hf.comp
      (by fun_prop : ContinuousOn
        (fun y : ℝ => (r : ℂ) + (y : ℂ) * Complex.I) [[b, u]])
      (fun y hy => ⟨by simp, by simpa using hy⟩)
  · apply ContinuousOn.intervalIntegrable
    simpa [Function.comp_def] using hf.comp
      (by fun_prop : ContinuousOn
        (fun y : ℝ => (l : ℂ) + (y : ℂ) * Complex.I) [[b, u]])
      (fun y hy => ⟨by simp, by simpa using hy⟩)

/-- On a rectangle avoiding its pole, the heat-weighted principal part is
integrable on all four sides. -/
theorem rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
    (x tau : ℝ) (L c : ℂ) (l r b u : ℝ)
    (hdomain : [[l, r]] ×ℂ [[b, u]] ⊆ ({c} : Set ℂ)ᶜ) :
    rectangularBoundaryIntegrable l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c) := by
  exact rectangularBoundaryIntegrable_of_continuousOn_reProdIm
    ((continuousOn_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
      x tau L c).mono hdomain)

/-- Away from the pole, only the non-holomorphic heat kernel contributes to
the Cauchy--Green source of the weighted principal part. -/
theorem complexCauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
    (x tau : ℝ) (L c : ℂ) {p : ℂ} (hp : p ≠ c) :
    complexCauchyGreenSource
        (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c) p =
      suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
        x tau L c p := by
  have hprincipal : DifferentiableAt ℂ (simplePoleKernel L c) p := by
    unfold simplePoleKernel
    exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr hp)).differentiableAt
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
  rw [complexCauchyGreenSource_mul_of_differentiableAt_complex
    (differentiableAt_real_suzukiChebyshevLaplaceBoundaryHeatKernel
      x tau p) hprincipal]
  exact congrArg (fun q : ℂ => q * simplePoleKernel L c p)
    (cauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatKernel x tau p)

/-- Exact Cauchy--Green formula for a heat-weighted simple pole on every
rectangle avoiding the pole. -/
theorem suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_rectangularCauchyGreen
    (x tau : ℝ) (L c : ℂ) (l r b u : ℝ)
    (hdomain : [[l, r]] ×ℂ [[b, u]] ⊆ ({c} : Set ℂ)ᶜ) :
    rectangularBoundaryIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c) =
      rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
          x tau L c) := by
  let R : Set ℂ := [[l, r]] ×ℂ [[b, u]]
  let F := suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c
  let G := suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource x tau L c
  have hprincipal : DifferentiableOn ℂ (simplePoleKernel L c) R :=
    differentiableOn_simplePoleKernel_of_not_mem L c (by
      intro hc
      exact (hdomain hc) (by simp))
  have hd : DifferentiableOn ℝ F R := by
    intro p hp
    exact
      (differentiableAt_real_suzukiChebyshevLaplaceBoundaryHeatKernel
          x tau p).differentiableWithinAt.mul
        ((hprincipal p hp).restrictScalars ℝ)
  have hcompact : IsCompact R :=
    isCompact_uIcc.reProdIm isCompact_uIcc
  have hG : IntegrableOn G R := by
    exact
      (continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
          x tau).continuousOn.mul hprincipal.continuousOn |>
        ContinuousOn.integrableOn_compact hcompact
  have hi : IntegrableOn (fun p : ℂ => complexCauchyGreenSource F p) R :=
    hG.congr_fun (fun p hp => by
      simpa [F, G] using
        (complexCauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
          x tau L c (fun hpc => (hdomain hp) (by rw [hpc]; simp))).symm)
      hcompact.measurableSet
  have hboundary :=
    Complex.integral_boundary_rect_of_differentiableOn_real
      F ((l : ℂ) + (b : ℂ) * Complex.I)
        ((r : ℂ) + (u : ℂ) * Complex.I) (by simpa [R] using hd) (by
          simpa [R, complexCauchyGreenSource] using hi)
  calc
    rectangularBoundaryIntegral l r b u F =
        rectangularAreaIntegral l r b u
          (fun p => complexCauchyGreenSource F p) := by
      simpa [F, rectangularBoundaryIntegral, rectangularAreaIntegral,
        sub_eq_add_neg, complexCauchyGreenSource] using hboundary
    _ = rectangularAreaIntegral l r b u G := by
      unfold rectangularAreaIntegral
      apply intervalIntegral.integral_congr
      intro a ha
      apply intervalIntegral.integral_congr
      intro y hy
      simpa [F, G] using
        complexCauchyGreenSource_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
          x tau L c (fun hpc => by
            have hp : (a + y * Complex.I : ℂ) ∈ R := by
              exact ⟨by simpa using ha, by simpa using hy⟩
            exact (hdomain hp) (by rw [hpc]; simp))

/-! ## Shrinking-square residue -/

/-- The heat-weighted principal part is integrable on every positive-radius
square centered at its pole. -/
theorem rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_centeredSquare
    (x tau : ℝ) (L c : ℂ) {q : ℝ} (hq : 0 < q) :
    rectangularBoundaryIntegrable
      (c.re - q) (c.re + q) (c.im - q) (c.im + q)
      (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c) := by
  have hK :=
    (differentiable_real_suzukiChebyshevLaplaceBoundaryHeatKernel
      x tau).continuous
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((hK.comp (by fun_prop)).mul
      (continuous_simplePoleKernel_horizontal L c
        (by linarith : c.im - q ≠ c.im))).intervalIntegrable _ _
  · exact ((hK.comp (by fun_prop)).mul
      (continuous_simplePoleKernel_horizontal L c
        (by linarith : c.im + q ≠ c.im))).intervalIntegrable _ _
  · exact ((hK.comp (by fun_prop)).mul
      (continuous_simplePoleKernel_vertical L c
        (by linarith : c.re + q ≠ c.re))).intervalIntegrable _ _
  · exact ((hK.comp (by fun_prop)).mul
      (continuous_simplePoleKernel_vertical L c
        (by linarith : c.re - q ≠ c.re))).intervalIntegrable _ _

/-- Multiplying the weighted principal part by `z-c` recovers the exact
moving heat coefficient. -/
theorem tendsto_sub_mul_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
    (x tau : ℝ) (L c : ℂ) :
    Tendsto
      (fun z : ℂ => (z - c) *
        suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c z)
      (𝓝[≠] c)
      (𝓝 (suzukiChebyshevLaplaceBoundaryHeatKernel x tau c * L)) := by
  have hK : Tendsto
      (suzukiChebyshevLaplaceBoundaryHeatKernel x tau)
      (𝓝[≠] c)
      (𝓝 (suzukiChebyshevLaplaceBoundaryHeatKernel x tau c)) :=
    (differentiableAt_real_suzukiChebyshevLaplaceBoundaryHeatKernel
      x tau c).continuousAt.tendsto.mono_left inf_le_left
  apply (hK.mul tendsto_const_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hzc : z ≠ c := by simpa using hz
  unfold suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole simplePoleKernel
  field_simp [sub_ne_zero.mpr hzc]

/-- Shrinking square boundaries of a heat-weighted principal part recover
its exact moving residue. -/
theorem tendsto_rectangularBoundaryIntegral_centeredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
    (x tau : ℝ) (L c : ℂ) :
    Tendsto
      (fun q : ℝ => rectangularBoundaryIntegral
        (c.re - q) (c.re + q) (c.im - q) (c.im + q)
        (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c))
      (𝓝[>] 0)
      (𝓝 ((2 * Real.pi * Complex.I) *
        (suzukiChebyshevLaplaceBoundaryHeatKernel x tau c * L))) := by
  apply
    tendsto_rectangularBoundaryIntegral_centeredSquare_nhdsGT_zero_of_tendsto_sub_mul
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact
      rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_centeredSquare
        x tau L c hq
  · exact
      tendsto_sub_mul_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
        x tau L c

/-! ## One-principal-part rectangular excision -/

/-- Exact fixed-radius Cauchy--Green identity for one heat-weighted principal
part.  Four pole-free rectangles fill the outer rectangle minus the centered
square, and their internal boundary segments cancel. -/
theorem suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_onePunctureSquareCauchyGreen
    (x tau l r b u q : ℝ) (L c : ℂ)
    (hq : 0 < q)
    (hl : l < c.re - q) (hr : c.re + q < r)
    (hb : b < c.im - q) (hu : c.im + q < u) :
    rectangularBoundaryIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c) =
      rectangularAreaIntegralOutsideCenteredSquare l r b u c q
          (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
            x tau L c) +
        rectangularBoundaryIntegral
          (c.re - q) (c.re + q) (c.im - q) (c.im + q)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
            x tau L c) := by
  let F := suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c
  let G :=
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource x tau L c
  have houterDiff :
      ([[l, r]] ×ℂ [[b, u]]) \ {c} ⊆ ({c} : Set ℂ)ᶜ := by
    intro z hz
    exact hz.2
  obtain ⟨hleftDomain, hbottomDomain, htopDomain, hrightDomain⟩ :=
    fourRectanglesOutsideCenteredSquare_subset_of_rectangle_diff_singleton_subset
      l r b u c q hq hl hr hb hu houterDiff
  have hleftInt : rectangularBoundaryIntegrable l (c.re - q) b u F := by
    simpa [F] using
      rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
        x tau L c l (c.re - q) b u hleftDomain
  have hbottomInt : rectangularBoundaryIntegrable
      (c.re - q) (c.re + q) b (c.im - q) F := by
    simpa [F] using
      rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
        x tau L c (c.re - q) (c.re + q) b (c.im - q) hbottomDomain
  have htopInt : rectangularBoundaryIntegrable
      (c.re - q) (c.re + q) (c.im + q) u F := by
    simpa [F] using
      rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
        x tau L c (c.re - q) (c.re + q) (c.im + q) u htopDomain
  have hrightInt : rectangularBoundaryIntegrable
      (c.re + q) r b u F := by
    simpa [F] using
      rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
        x tau L c (c.re + q) r b u hrightDomain
  have hsquareInt : rectangularBoundaryIntegrable
      (c.re - q) (c.re + q) (c.im - q) (c.im + q) F := by
    simpa [F] using
      rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_centeredSquare
        x tau L c hq
  have hdecomp :=
    rectangularBoundaryIntegral_eq_fourPieces_add_centeredSquare
      l r b u c q F hleftInt hbottomInt hsquareInt htopInt hrightInt
  have hleftCG : rectangularBoundaryIntegral l (c.re - q) b u F =
      rectangularAreaIntegral l (c.re - q) b u G := by
    simpa [F, G] using
      suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_rectangularCauchyGreen
        x tau L c l (c.re - q) b u hleftDomain
  have hbottomCG : rectangularBoundaryIntegral
      (c.re - q) (c.re + q) b (c.im - q) F =
      rectangularAreaIntegral
        (c.re - q) (c.re + q) b (c.im - q) G := by
    simpa [F, G] using
      suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_rectangularCauchyGreen
        x tau L c (c.re - q) (c.re + q) b (c.im - q) hbottomDomain
  have htopCG : rectangularBoundaryIntegral
      (c.re - q) (c.re + q) (c.im + q) u F =
      rectangularAreaIntegral
        (c.re - q) (c.re + q) (c.im + q) u G := by
    simpa [F, G] using
      suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_rectangularCauchyGreen
        x tau L c (c.re - q) (c.re + q) (c.im + q) u htopDomain
  have hrightCG : rectangularBoundaryIntegral (c.re + q) r b u F =
      rectangularAreaIntegral (c.re + q) r b u G := by
    simpa [F, G] using
      suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_rectangularCauchyGreen
        x tau L c (c.re + q) r b u hrightDomain
  rw [hdecomp, hleftCG, hbottomCG, htopCG, hrightCG]
  simp only [rectangularAreaIntegralOutsideCenteredSquare]
  ring

/-- The improper four-rectangle area integral of one heat-weighted principal
part exists and equals its outer boundary integral minus the exact moving
residue.  This statement does not assume integrability at the pole. -/
theorem tendsto_rectangularAreaIntegralOutsideCenteredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
    (x tau l r b u : ℝ) (L c : ℂ)
    (hl : l < c.re) (hr : c.re < r)
    (hb : b < c.im) (hu : c.im < u) :
    Tendsto
      (fun q : ℝ =>
        rectangularAreaIntegralOutsideCenteredSquare l r b u c q
          (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
            x tau L c))
      (𝓝[>] 0)
      (𝓝 (rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c) -
        (2 * Real.pi * Complex.I) *
          (suzukiChebyshevLaplaceBoundaryHeatKernel x tau c * L))) := by
  let F := suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau L c
  let G :=
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource x tau L c
  have hsquare :=
    tendsto_rectangularBoundaryIntegral_centeredSquare_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
      x tau L c
  have hlimit : Tendsto
      (fun q : ℝ => rectangularBoundaryIntegral l r b u F -
        rectangularBoundaryIntegral
          (c.re - q) (c.re + q) (c.im - q) (c.im + q) F)
      (𝓝[>] 0)
      (𝓝 (rectangularBoundaryIntegral l r b u F -
        (2 * Real.pi * Complex.I) *
          (suzukiChebyshevLaplaceBoundaryHeatKernel x tau c * L))) := by
    simpa [F] using tendsto_const_nhds.sub hsquare
  have hleftRange : Ioo (0 : ℝ) (c.re - l) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (sub_pos.mpr hl)
  have hrightRange : Ioo (0 : ℝ) (r - c.re) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (sub_pos.mpr hr)
  have hbottomRange : Ioo (0 : ℝ) (c.im - b) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (sub_pos.mpr hb)
  have htopRange : Ioo (0 : ℝ) (u - c.im) ∈ 𝓝[>] 0 :=
    Ioo_mem_nhdsGT (sub_pos.mpr hu)
  apply hlimit.congr'
  filter_upwards [hleftRange, hrightRange, hbottomRange, htopRange]
      with q hql hqr hqb hqu
  have hexact :=
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_onePunctureSquareCauchyGreen
      x tau l r b u q L c hql.1
        (by linarith [hql.2]) (by linarith [hqr.2])
        (by linarith [hqb.2]) (by linarith [hqu.2])
  dsimp [F, G] at hexact ⊢
  rw [hexact]
  ring

end

end RiemannGaussian
