import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatCommonHoleComparison

/-!
# Selected finite Cauchy--Green identity for boundary heat

The parameter-free finite identity for the complete symmetric xi divisor can
hide the sign information needed for RH.  This file retains only the shifted
zeros with negative real coordinate, equivalently the existing upper
spectral selector.  The real part of their finite heat-residue total is
nonnegative, and the presence of any selected zero makes it strictly
positive.

The proof first decomposes the actual arithmetic area-minus-boundary defect
into a sum of individual principal-part defects whenever every finite-window
zero is either strictly inside or genuinely outside the rectangle.  A
filtered theorem then assigns exact residues only to the chosen interior
divisor and proves ordinary zero-residue Cauchy--Green identities for all
exterior terms.  Specializing to a rectangle whose right edge is strictly
negative automatically places every nonselected zero outside.

The resulting public identity equates the sign-controlled selected finite heat
sum with an explicit arithmetic boundary-minus-bulk functional.  The finite
sums also converge to the already-checked RH-equivalent boundary-heat total.
No large-height vanishing or zero-location conclusion is asserted here.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-! ## The positive selected finite residue window -/

/-- The finite boundary-heat residue sum over the genuine symmetric xi window.
The residue definition itself selects exactly the negative-real shifted
half-divisor and vanishes on every other zero. -/
def suzukiChebyshevLaplaceBoundaryHeatResidueWindow
    (x tau T : ℝ) : ℂ :=
  ∑ rho ∈ spectralZetaZeroWindow T,
    suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho

/-- The selector inside the residue definition is exactly the existing upper
spectral finite window, so the finite total is visibly a sum of positive-side
heat coefficients times analytic multiplicities. -/
theorem suzukiChebyshevLaplaceBoundaryHeatResidueWindow_eq_selected
    (x tau T : ℝ) :
    suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T =
      ∑ rho ∈ spectralUpperZetaZeroWindow T,
        suzukiChebyshevLaplaceBoundaryHeatKernel x tau
            (suzukiChebyshevLaplaceZeroCoordinate rho) *
          (analyticZetaZeroMultiplicity rho : ℂ) := by
  unfold suzukiChebyshevLaplaceBoundaryHeatResidueWindow
    spectralUpperZetaZeroWindow
  simp only [suzukiChebyshevLaplaceBoundaryHeatResidue,
    suzukiChebyshevLaplaceZeroCoordinate_re_neg_iff_upper]
  rw [Finset.sum_filter]

/-- Every selected finite boundary-heat residue window has nonnegative real
part. -/
theorem suzukiChebyshevLaplaceBoundaryHeatResidueWindow_re_nonneg
    (x tau T : ℝ) :
    0 ≤ (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T).re := by
  unfold suzukiChebyshevLaplaceBoundaryHeatResidueWindow
  rw [Complex.re_sum]
  simp only [suzukiChebyshevLaplaceBoundaryHeatResidue_eq_riemannXi,
    riemannXiUpperHyperbolicBoundaryHeatResidue, Complex.ofReal_re]
  exact Finset.sum_nonneg fun rho _ =>
    zetaUpperHyperbolicBoundaryHeatSummand_nonneg x tau rho

/-- If the finite window contains one selected off-axis zero, then its
boundary-heat residue total has strictly positive real part. -/
theorem suzukiChebyshevLaplaceBoundaryHeatResidueWindow_re_pos_of_mem_upper
    (x tau T : ℝ) {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralUpperZetaZeroWindow T) :
    0 < (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T).re := by
  unfold suzukiChebyshevLaplaceBoundaryHeatResidueWindow
  rw [Complex.re_sum]
  simp only [suzukiChebyshevLaplaceBoundaryHeatResidue_eq_riemannXi,
    riemannXiUpperHyperbolicBoundaryHeatResidue, Complex.ofReal_re]
  apply Finset.sum_pos'
  · exact fun sigma _ =>
      zetaUpperHyperbolicBoundaryHeatSummand_nonneg x tau sigma
  · refine ⟨rho, (mem_spectralUpperZetaZeroWindow.mp hrho).1, ?_⟩
    exact zetaUpperHyperbolicBoundaryHeatSummand_pos x tau rho
      (mem_spectralUpperZetaZeroWindow.mp hrho).2

/-- At positive proper time the selected finite residue windows converge to
the complete complex boundary-heat total, whose vanishing is equivalent to
RH. -/
theorem tendsto_suzukiChebyshevLaplaceBoundaryHeatResidueWindow
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau) atTop
      (𝓝 (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ)) := by
  change Tendsto (fun T : ℝ => ∑ rho ∈ spectralZetaZeroWindow T,
    suzukiChebyshevLaplaceBoundaryHeatResidue x tau rho) atTop _
  have h :=
    (hasSum_suzukiChebyshevLaplaceBoundaryHeatResidue x htau).comp
      tendsto_spectralZetaZeroWindow_atTop
  apply h.congr'
  filter_upwards with T
  rfl

/-! ## Finite divisor defect decomposition -/

/-- If every zero in a complete finite window is either strictly inside or
genuinely outside an ordered rectangle, the actual arithmetic
area-minus-boundary defect is exactly the sum of the corresponding
principal-part area-minus-boundary defects.  One common analytic remainder
is used simultaneously for the response and its source. -/
theorem suzukiChebyshevLaplaceBoundaryHeat_finiteArea_sub_boundary_eq_sum_principalDefects
    (x tau l r b u : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hlr : l ≤ r) (hbu : b ≤ u)
    (hrectangle : [[l, r]] ×ℂ [[b, u]] ⊆
      suzukiChebyshevLaplaceFiniteSlab T)
    (hposition : ∀ rho ∈ spectralZetaZeroWindow T,
      (l < (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
        (suzukiChebyshevLaplaceZeroCoordinate rho).re < r ∧
        b < (suzukiChebyshevLaplaceZeroCoordinate rho).im ∧
        (suzukiChebyshevLaplaceZeroCoordinate rho).im < u) ∨
      suzukiChebyshevLaplaceZeroCoordinate rho ∉
        [[l, r]] ×ℂ [[b, u]]) :
    rectangularAreaIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) -
        rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) =
      ∑ rho ∈ spectralZetaZeroWindow T,
        (rectangularAreaIntegral l r b u
            (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource x tau
              (analyticZetaZeroMultiplicity rho : ℂ)
              (suzukiChebyshevLaplaceZeroCoordinate rho)) -
          rectangularBoundaryIntegral l r b u
            (suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau
              (analyticZetaZeroMultiplicity rho : ℂ)
              (suzukiChebyshevLaplaceZeroCoordinate rho))) := by
  let R : Set ℂ := [[l, r]] ×ℂ [[b, u]]
  let W := spectralZetaZeroWindow T
  let P : NontrivialZetaZero → ℂ → ℂ := fun rho =>
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau
      (analyticZetaZeroMultiplicity rho : ℂ)
      (suzukiChebyshevLaplaceZeroCoordinate rho)
  let PS : NontrivialZetaZero → ℂ → ℂ := fun rho =>
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource x tau
      (analyticZetaZeroMultiplicity rho : ℂ)
      (suzukiChebyshevLaplaceZeroCoordinate rho)
  obtain ⟨F, hF, hresponse, hsource⟩ :=
    exists_suzukiChebyshevLaplaceBoundaryHeatWeighted_finitePrincipalPartDecompositions
      x tau hT
  let H : ℂ → ℂ :=
    suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder x tau F
  let HS : ℂ → ℂ :=
    suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainderSource x tau F
  let PSum : ℂ → ℂ := fun z => ∑ rho ∈ W, P rho z
  let PSSum : ℂ → ℂ := fun z => ∑ rho ∈ W, PS rho z
  have hcompact : IsCompact R :=
    isCompact_uIcc.reProdIm isCompact_uIcc
  have hFRectangle : ∀ z ∈ R, AnalyticAt ℂ F z :=
    fun z hz => hF z (hrectangle hz)
  have hPBoundaryInt : ∀ rho ∈ W,
      rectangularBoundaryIntegrable l r b u (P rho) := by
    intro rho hrho
    rcases hposition rho (by simpa [W] using hrho) with hi | hout
    · simpa [P] using
        rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_of_mem
          x tau (analyticZetaZeroMultiplicity rho : ℂ)
            (suzukiChebyshevLaplaceZeroCoordinate rho) l r b u
            hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
    · apply
        rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole
      intro z hz hzc
      apply hout
      have hzc' : z = suzukiChebyshevLaplaceZeroCoordinate rho := by
        simpa using hzc
      rw [← hzc']
      exact hz
  have hPSumBoundaryInt : rectangularBoundaryIntegrable l r b u PSum := by
    simpa [PSum] using
      rectangularBoundaryIntegrable_finsetSum l r b u W P hPBoundaryInt
  have hHBoundaryInt : rectangularBoundaryIntegrable l r b u H := by
    simpa [H, R] using
      rectangularBoundaryIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder
        x tau l r b u F hFRectangle
  have hnotBottom (a : ℝ) (ha : a ∈ [[l, r]]) :
      (a : ℂ) + (b : ℂ) * Complex.I ∉
        suzukiChebyshevLaplaceZeroWindow T := by
    intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, heq⟩
    rcases hposition rho hrho with hi | hout
    · have him : (suzukiChebyshevLaplaceZeroCoordinate rho).im = b := by
        simpa using congrArg Complex.im heq
      linarith [hi.2.2.1]
    · apply hout
      rw [heq]
      exact ⟨by simpa using ha, by simp⟩
  have hnotTop (a : ℝ) (ha : a ∈ [[l, r]]) :
      (a : ℂ) + (u : ℂ) * Complex.I ∉
        suzukiChebyshevLaplaceZeroWindow T := by
    intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, heq⟩
    rcases hposition rho hrho with hi | hout
    · have him : (suzukiChebyshevLaplaceZeroCoordinate rho).im = u := by
        simpa using congrArg Complex.im heq
      linarith [hi.2.2.2]
    · apply hout
      rw [heq]
      exact ⟨by simpa using ha, by simp⟩
  have hnotRight (y : ℝ) (hy : y ∈ [[b, u]]) :
      (r : ℂ) + (y : ℂ) * Complex.I ∉
        suzukiChebyshevLaplaceZeroWindow T := by
    intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, heq⟩
    rcases hposition rho hrho with hi | hout
    · have hre : (suzukiChebyshevLaplaceZeroCoordinate rho).re = r := by
        simpa using congrArg Complex.re heq
      linarith [hi.2.1]
    · apply hout
      rw [heq]
      exact ⟨by simp, by simpa using hy⟩
  have hnotLeft (y : ℝ) (hy : y ∈ [[b, u]]) :
      (l : ℂ) + (y : ℂ) * Complex.I ∉
        suzukiChebyshevLaplaceZeroWindow T := by
    intro hz
    rcases Finset.mem_image.mp hz with ⟨rho, hrho, heq⟩
    rcases hposition rho hrho with hi | hout
    · have hre : (suzukiChebyshevLaplaceZeroCoordinate rho).re = l := by
        simpa using congrArg Complex.re heq
      linarith [hi.1]
    · apply hout
      rw [heq]
      exact ⟨by simp, by simpa using hy⟩
  have hboundaryCongr : rectangularBoundaryIntegral l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) =
      rectangularBoundaryIntegral l r b u (fun z => PSum z + H z) := by
    apply rectangularBoundaryIntegral_congr_of_eq_on_sides
    · intro a ha
      simpa [PSum, P, H] using
        hresponse ((a : ℂ) + (b : ℂ) * Complex.I) (hnotBottom a ha)
    · intro a ha
      simpa [PSum, P, H] using
        hresponse ((a : ℂ) + (u : ℂ) * Complex.I) (hnotTop a ha)
    · intro y hy
      simpa [PSum, P, H] using
        hresponse ((r : ℂ) + (y : ℂ) * Complex.I) (hnotRight y hy)
    · intro y hy
      simpa [PSum, P, H] using
        hresponse ((l : ℂ) + (y : ℂ) * Complex.I) (hnotLeft y hy)
  have hboundaryDecomp : rectangularBoundaryIntegral l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) =
      (∑ rho ∈ W, rectangularBoundaryIntegral l r b u (P rho)) +
        rectangularBoundaryIntegral l r b u H := by
    calc
      _ = rectangularBoundaryIntegral l r b u (fun z => PSum z + H z) :=
        hboundaryCongr
      _ = rectangularBoundaryIntegral l r b u PSum +
          rectangularBoundaryIntegral l r b u H :=
        rectangularBoundaryIntegral_add l r b u
          hPSumBoundaryInt hHBoundaryInt
      _ = _ := by
        rw [show rectangularBoundaryIntegral l r b u PSum =
            ∑ rho ∈ W, rectangularBoundaryIntegral l r b u (P rho) by
          simpa [PSum] using
            rectangularBoundaryIntegral_finsetSum l r b u W P
              hPBoundaryInt]
  have hPSInt : ∀ rho ∈ W, IntegrableOn (PS rho) R volume := by
    intro rho hrho
    exact
      (locallyIntegrable_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource
        x tau (analyticZetaZeroMultiplicity rho : ℂ)
          (suzukiChebyshevLaplaceZeroCoordinate rho)).integrableOn_isCompact
        hcompact
  have hPSSumInt : IntegrableOn PSSum R volume := by
    change Integrable PSSum (volume.restrict R)
    simpa [PSSum] using integrable_finsetSum W hPSInt
  have hHSInt : IntegrableOn HS R volume := by
    exact
      ((continuous_suzukiChebyshevLaplaceBoundaryHeatCauchyGreenSource
          x tau).continuousOn.mul
        (show AnalyticOnNhd ℂ F R from hFRectangle).continuousOn).integrableOn_compact
        hcompact
  have hactualInt : IntegrableOn
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)
      R volume := by
    simpa [R] using
      integrableOn_suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource_finiteRectangle
        x tau l r b u hT hrectangle
  have hsourceAE : ∀ᵐ z ∂volume.restrict R,
      suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau z =
        PSSum z + HS z := by
    filter_upwards [ae_restrict_of_ae
      ((suzukiChebyshevLaplaceZeroWindow T).finite_toSet.countable.ae_notMem
        volume)] with z hz
    simpa [PSSum, PS, HS, W] using hsource z hz
  have hsetAreaDecomp :
      (∫ z in R,
        suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau z
        ∂volume) =
      (∫ z in R, PSSum z ∂volume) +
        ∫ z in R, HS z ∂volume := by
    rw [integral_congr_ae hsourceAE]
    exact integral_add hPSSumInt hHSInt
  have hHSArea : rectangularAreaIntegral l r b u HS =
      ∫ z in R, HS z ∂volume := by
    simpa [R] using rectangularAreaIntegral_eq_setIntegral
      hlr hbu HS hHSInt
  have hPSAreas :
      (∑ rho ∈ W, rectangularAreaIntegral l r b u (PS rho)) =
        ∑ rho ∈ W, ∫ z in R, PS rho z ∂volume := by
    apply Finset.sum_congr rfl
    intro rho hrho
    simpa [R] using rectangularAreaIntegral_eq_setIntegral
      hlr hbu (PS rho) (hPSInt rho hrho)
  have hPSSumArea :
      (∫ z in R, PSSum z ∂volume) =
        ∑ rho ∈ W, ∫ z in R, PS rho z ∂volume := by
    simpa [PSSum] using integral_finsetSum W hPSInt
  have hareaDecomp : rectangularAreaIntegral l r b u
      (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) =
      rectangularAreaIntegral l r b u HS +
        ∑ rho ∈ W, rectangularAreaIntegral l r b u (PS rho) := by
    rw [rectangularAreaIntegral_eq_setIntegral hlr hbu _ hactualInt,
      hsetAreaDecomp, hPSSumArea, ← hHSArea, ← hPSAreas]
    ring
  have hHCG : rectangularBoundaryIntegral l r b u H =
      rectangularAreaIntegral l r b u HS := by
    simpa [H, HS, R] using
      suzukiChebyshevLaplaceBoundaryHeatWeightedAnalyticRemainder_rectangularCauchyGreen
        x tau l r b u F hFRectangle
  change rectangularAreaIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) -
        rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) =
      ∑ rho ∈ W, (rectangularAreaIntegral l r b u (PS rho) -
        rectangularBoundaryIntegral l r b u (P rho))
  rw [hareaDecomp, hboundaryDecomp, ← hHCG,
    Finset.sum_sub_distrib]
  ring

/-- A chosen sub-divisor of the complete finite xi window contributes exactly
its heat residues when every chosen zero is strictly inside and every
unchosen zero is outside the rectangle.  Exterior principal parts satisfy
ordinary Cauchy--Green and contribute zero defect. -/
theorem suzukiChebyshevLaplaceBoundaryHeat_finiteCauchyGreen_of_selectedFinset
    (x tau l r b u : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hlr : l ≤ r) (hbu : b ≤ u)
    (S : Finset NontrivialZetaZero)
    (hS : S ⊆ spectralZetaZeroWindow T)
    (hrectangle : [[l, r]] ×ℂ [[b, u]] ⊆
      suzukiChebyshevLaplaceFiniteSlab T)
    (hinside : ∀ rho ∈ S,
      l < (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).re < r ∧
      b < (suzukiChebyshevLaplaceZeroCoordinate rho).im ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).im < u)
    (houtside : ∀ rho ∈ spectralZetaZeroWindow T, rho ∉ S →
      suzukiChebyshevLaplaceZeroCoordinate rho ∉
        [[l, r]] ×ℂ [[b, u]]) :
    rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) =
      rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        (2 * Real.pi * Complex.I) *
          ∑ rho ∈ S,
            suzukiChebyshevLaplaceBoundaryHeatKernel x tau
                (suzukiChebyshevLaplaceZeroCoordinate rho) *
              (analyticZetaZeroMultiplicity rho : ℂ) := by
  let W := spectralZetaZeroWindow T
  let P : NontrivialZetaZero → ℂ → ℂ := fun rho =>
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole x tau
      (analyticZetaZeroMultiplicity rho : ℂ)
      (suzukiChebyshevLaplaceZeroCoordinate rho)
  let PS : NontrivialZetaZero → ℂ → ℂ := fun rho =>
    suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource x tau
      (analyticZetaZeroMultiplicity rho : ℂ)
      (suzukiChebyshevLaplaceZeroCoordinate rho)
  let Q : NontrivialZetaZero → ℂ := fun rho =>
    suzukiChebyshevLaplaceBoundaryHeatKernel x tau
        (suzukiChebyshevLaplaceZeroCoordinate rho) *
      (analyticZetaZeroMultiplicity rho : ℂ)
  let C : ℂ := 2 * Real.pi * Complex.I
  have hposition : ∀ rho ∈ spectralZetaZeroWindow T,
      (l < (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
        (suzukiChebyshevLaplaceZeroCoordinate rho).re < r ∧
        b < (suzukiChebyshevLaplaceZeroCoordinate rho).im ∧
        (suzukiChebyshevLaplaceZeroCoordinate rho).im < u) ∨
      suzukiChebyshevLaplaceZeroCoordinate rho ∉
        [[l, r]] ×ℂ [[b, u]] := by
    intro rho hrho
    by_cases hs : rho ∈ S
    · exact Or.inl (hinside rho hs)
    · exact Or.inr (houtside rho hrho hs)
  have hdefect :=
    suzukiChebyshevLaplaceBoundaryHeat_finiteArea_sub_boundary_eq_sum_principalDefects
      x tau l r b u hT hlr hbu hrectangle hposition
  have hterm : ∀ rho ∈ W,
      rectangularAreaIntegral l r b u (PS rho) -
          rectangularBoundaryIntegral l r b u (P rho) =
        if rho ∈ S then -(C * Q rho) else 0 := by
    intro rho hrho
    by_cases hs : rho ∈ S
    · rw [if_pos hs]
      have hi := hinside rho hs
      have hid :=
        rectangularAreaIntegral_suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePoleSource_eq_boundary_sub_residue
          x tau l r b u (analyticZetaZeroMultiplicity rho : ℂ)
            (suzukiChebyshevLaplaceZeroCoordinate rho)
            hi.1 hi.2.1 hi.2.2.1 hi.2.2.2
      change rectangularAreaIntegral l r b u (PS rho) -
          rectangularBoundaryIntegral l r b u (P rho) = -(C * Q rho)
      rw [hid]
      simp only [P, Q, C]
      ring
    · rw [if_neg hs]
      have hout := houtside rho (by simpa [W] using hrho) hs
      have hdomain : [[l, r]] ×ℂ [[b, u]] ⊆
          ({suzukiChebyshevLaplaceZeroCoordinate rho} : Set ℂ)ᶜ := by
        intro z hz hzc
        apply hout
        have hzc' : z = suzukiChebyshevLaplaceZeroCoordinate rho := by
          simpa using hzc
        rw [← hzc']
        exact hz
      have hcg :=
        suzukiChebyshevLaplaceBoundaryHeatWeightedSimplePole_rectangularCauchyGreen
          x tau (analyticZetaZeroMultiplicity rho : ℂ)
            (suzukiChebyshevLaplaceZeroCoordinate rho) l r b u hdomain
      change rectangularAreaIntegral l r b u (PS rho) -
          rectangularBoundaryIntegral l r b u (P rho) = 0
      rw [hcg]
      simp only [PS]
      ring
  have hfilter : W.filter (fun rho => rho ∈ S) = S := by
    ext rho
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.2
    · intro hs
      exact ⟨by simpa [W] using hS hs, hs⟩
  have hsum :
      (∑ rho ∈ W,
        (rectangularAreaIntegral l r b u (PS rho) -
          rectangularBoundaryIntegral l r b u (P rho))) =
        -(C * ∑ rho ∈ S, Q rho) := by
    calc
      _ = ∑ rho ∈ W, if rho ∈ S then -(C * Q rho) else 0 := by
        apply Finset.sum_congr rfl
        exact hterm
      _ = ∑ rho ∈ W.filter (fun rho => rho ∈ S), -(C * Q rho) := by
        rw [Finset.sum_filter]
      _ = ∑ rho ∈ S, -(C * Q rho) := by
        rw [hfilter]
      _ = -(C * ∑ rho ∈ S, Q rho) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
  change rectangularAreaIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) -
        rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) =
      ∑ rho ∈ W, (rectangularAreaIntegral l r b u (PS rho) -
        rectangularBoundaryIntegral l r b u (P rho)) at hdefect
  rw [hsum] at hdefect
  change rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) =
      rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        C * ∑ rho ∈ S, Q rho
  calc
    _ = (rectangularAreaIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) -
        rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau)) +
        rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) := by ring
    _ = -(C * ∑ rho ∈ S, Q rho) +
        rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) := by
      rw [hdefect]
    _ = _ := by ring

/-! ## The selected negative-real half-strip -/

/-- On a finite rectangle with strictly negative right edge, every
nonselected shifted xi zero is automatically outside.  If the rectangle
strictly contains the selected finite window, its actual through-divisor area
is the arithmetic boundary minus `2*pi*i` times the positive selected
boundary-heat residue window. -/
theorem suzukiChebyshevLaplaceBoundaryHeat_selectedFiniteCauchyGreen
    (x tau l r b u : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hlr : l ≤ r) (hbu : b ≤ u) (hr : r < 0)
    (hrectangle : [[l, r]] ×ℂ [[b, u]] ⊆
      suzukiChebyshevLaplaceFiniteSlab T)
    (hinside : ∀ rho ∈ spectralUpperZetaZeroWindow T,
      l < (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).re < r ∧
      b < (suzukiChebyshevLaplaceZeroCoordinate rho).im ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).im < u) :
    rectangularAreaIntegral l r b u
        (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) =
      rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        (2 * Real.pi * Complex.I) *
          suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T := by
  have hS : spectralUpperZetaZeroWindow T ⊆ spectralZetaZeroWindow T := by
    intro rho hrho
    exact (mem_spectralUpperZetaZeroWindow.mp hrho).1
  have houtside : ∀ rho ∈ spectralZetaZeroWindow T,
      rho ∉ spectralUpperZetaZeroWindow T →
      suzukiChebyshevLaplaceZeroCoordinate rho ∉
        [[l, r]] ×ℂ [[b, u]] := by
    intro rho hrho hnot hc
    have hnupper : ¬0 < (zetaSpectralCoordinate rho.1).im := by
      intro hupper
      exact hnot (mem_spectralUpperZetaZeroWindow.mpr ⟨hrho, hupper⟩)
    have hnre : ¬(suzukiChebyshevLaplaceZeroCoordinate rho).re < 0 := by
      intro hre
      exact hnupper
        ((suzukiChebyshevLaplaceZeroCoordinate_re_neg_iff_upper rho).mp hre)
    have hre0 : 0 ≤ (suzukiChebyshevLaplaceZeroCoordinate rho).re :=
      le_of_not_gt hnre
    have hcoordLe : (suzukiChebyshevLaplaceZeroCoordinate rho).re ≤ r := by
      rw [uIcc_of_le hlr] at hc
      exact hc.1.2
    linarith
  have hselected :=
    suzukiChebyshevLaplaceBoundaryHeat_finiteCauchyGreen_of_selectedFinset
    x tau l r b u hT hlr hbu (spectralUpperZetaZeroWindow T)
    hS hrectangle hinside houtside
  rw [← suzukiChebyshevLaplaceBoundaryHeatResidueWindow_eq_selected
    x tau T] at hselected
  exact hselected

/-- The selected finite identity in detector-first orientation: the positive
finite heat-residue window, multiplied by `2*pi*i`, is exactly the explicit
arithmetic outer-boundary minus through-divisor bulk functional. -/
theorem suzukiChebyshevLaplaceBoundaryHeat_selectedFiniteResidue_eq_boundary_sub_area
    (x tau l r b u : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hlr : l ≤ r) (hbu : b ≤ u) (hr : r < 0)
    (hrectangle : [[l, r]] ×ℂ [[b, u]] ⊆
      suzukiChebyshevLaplaceFiniteSlab T)
    (hinside : ∀ rho ∈ spectralUpperZetaZeroWindow T,
      l < (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).re < r ∧
      b < (suzukiChebyshevLaplaceZeroCoordinate rho).im ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).im < u) :
    (2 * Real.pi * Complex.I) *
        suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau T =
      rectangularBoundaryIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        rectangularAreaIntegral l r b u
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) := by
  rw [suzukiChebyshevLaplaceBoundaryHeat_selectedFiniteCauchyGreen
    x tau l r b u hT hlr hbu hr hrectangle hinside]
  ring

end

end RiemannGaussian
