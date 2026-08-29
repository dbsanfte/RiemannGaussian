import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedFinite
import RiemannGaussian.GaussianXiQuantitativeContour

/-!
# Canonical expanding rectangles for selected boundary heat

The finite selected Cauchy--Green theorem requires a rectangle strictly
containing every selected zero in its height window.  This file constructs
such rectangles without leaving geometric choices as hypotheses.

The horizontal endpoints are explicit midpoints between the finite minimum
and maximum selected real coordinates and the two edges of the shifted
critical strip.  The vertical endpoints use the existing quantitative
spectral truncations, which tend to infinity and avoid every zero height.
Thus every selected finite window lies strictly inside its canonical
rectangle, while the complete rectangle remains in the slab on which the
finite principal-part decomposition is valid.

On these rectangles, Lean proves that the arithmetic boundary-minus-bulk
functional converges to `2*pi*i` times the complete boundary-heat detector.
Consequently its convergence to zero is equivalent to RH.  This is a checked
closure interface, not a proof that the arithmetic functional vanishes; that
estimate remains the open conjecture-strength step.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- The finite set of real coordinates of the selected shifted xi zeros in
the spectral height window `T`. -/
def selectedLaplaceRealCoordinateWindow (T : ℝ) : Finset ℝ :=
  (spectralUpperZetaZeroWindow T).image fun rho =>
    (suzukiChebyshevLaplaceZeroCoordinate rho).re

/-- The least selected real coordinate, with `0` inserted as the empty-window
sentinel. -/
def selectedLaplaceLowerAnchor (T : ℝ) : ℝ :=
  let S := insert 0 (selectedLaplaceRealCoordinateWindow T)
  S.min' (by simp [S])

/-- The greatest selected real coordinate, with `-1/2` inserted as the
empty-window sentinel. -/
def selectedLaplaceUpperAnchor (T : ℝ) : ℝ :=
  let S := insert (-(1 / 2 : ℝ)) (selectedLaplaceRealCoordinateWindow T)
  S.max' (by simp [S])

/-- The midpoint between the left critical-strip edge and the selected lower
anchor. -/
def selectedLaplaceLeftBoundary (T : ℝ) : ℝ :=
  (-(1 / 2 : ℝ) + selectedLaplaceLowerAnchor T) / 2

/-- The midpoint between the selected upper anchor and the critical line. -/
def selectedLaplaceRightBoundary (T : ℝ) : ℝ :=
  selectedLaplaceUpperAnchor T / 2

/-- Every shifted nontrivial zeta zero lies strictly to the right of
`Re p = -1/2`. -/
lemma selectedLaplaceZeroCoordinate_re_gt_neg_half
    (rho : NontrivialZetaZero) :
    -(1 / 2 : ℝ) < (suzukiChebyshevLaplaceZeroCoordinate rho).re := by
  unfold suzukiChebyshevLaplaceZeroCoordinate
  norm_num [Complex.sub_re]
  have hre := NontrivialZetaZero.zero_lt_re rho
  linarith

/-- Membership in the selected upper spectral window puts the shifted zero
strictly to the left of the critical line. -/
lemma selectedLaplaceZeroCoordinate_re_lt_zero_of_mem
    {T : ℝ} {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralUpperZetaZeroWindow T) :
    (suzukiChebyshevLaplaceZeroCoordinate rho).re < 0 := by
  apply (suzukiChebyshevLaplaceZeroCoordinate_re_neg_iff_upper rho).mpr
  exact (mem_spectralUpperZetaZeroWindow.mp hrho).2

/-- The selected lower anchor remains strictly inside the shifted critical
strip. -/
lemma selectedLaplaceLowerAnchor_gt_neg_half (T : ℝ) :
    -(1 / 2 : ℝ) < selectedLaplaceLowerAnchor T := by
  let S := insert 0 (selectedLaplaceRealCoordinateWindow T)
  have hmem : S.min' (by simp [S]) ∈ S := Finset.min'_mem _ _
  rw [show selectedLaplaceLowerAnchor T = S.min' (by simp [S]) by
    rfl]
  dsimp only [S] at hmem ⊢
  simp only [Finset.mem_insert] at hmem
  rcases hmem with hzero | hcoord
  · rw [hzero]
    norm_num
  · rcases Finset.mem_image.mp hcoord with ⟨rho, hrho, hvalue⟩
    rw [← hvalue]
    exact selectedLaplaceZeroCoordinate_re_gt_neg_half rho

/-- The inserted zero bounds the selected lower anchor from above. -/
lemma selectedLaplaceLowerAnchor_le_zero (T : ℝ) :
    selectedLaplaceLowerAnchor T ≤ 0 := by
  unfold selectedLaplaceLowerAnchor
  exact Finset.min'_le _ 0 (by simp)

/-- The selected lower anchor is no greater than any selected coordinate. -/
lemma selectedLaplaceLowerAnchor_le_coordinate
    {T : ℝ} {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralUpperZetaZeroWindow T) :
    selectedLaplaceLowerAnchor T ≤
      (suzukiChebyshevLaplaceZeroCoordinate rho).re := by
  unfold selectedLaplaceLowerAnchor selectedLaplaceRealCoordinateWindow
  apply Finset.min'_le
  simp only [Finset.mem_insert, Finset.mem_image]
  exact Or.inr ⟨rho, hrho, rfl⟩

/-- The selected upper anchor remains strictly left of the critical line. -/
lemma selectedLaplaceUpperAnchor_lt_zero (T : ℝ) :
    selectedLaplaceUpperAnchor T < 0 := by
  let S := insert (-(1 / 2 : ℝ)) (selectedLaplaceRealCoordinateWindow T)
  have hmem : S.max' (by simp [S]) ∈ S := Finset.max'_mem _ _
  rw [show selectedLaplaceUpperAnchor T = S.max' (by simp [S]) by
    rfl]
  dsimp only [S] at hmem ⊢
  simp only [Finset.mem_insert] at hmem
  rcases hmem with hhalf | hcoord
  · rw [hhalf]
    norm_num
  · rcases Finset.mem_image.mp hcoord with ⟨rho, hrho, hvalue⟩
    rw [← hvalue]
    exact selectedLaplaceZeroCoordinate_re_lt_zero_of_mem hrho

/-- The inserted `-1/2` sentinel bounds the selected upper anchor below. -/
lemma neg_half_le_selectedLaplaceUpperAnchor (T : ℝ) :
    -(1 / 2 : ℝ) ≤ selectedLaplaceUpperAnchor T := by
  unfold selectedLaplaceUpperAnchor
  exact Finset.le_max' _ (-(1 / 2 : ℝ)) (by simp)

/-- Every selected coordinate is no greater than the selected upper
anchor. -/
lemma selectedLaplaceCoordinate_le_upperAnchor
    {T : ℝ} {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralUpperZetaZeroWindow T) :
    (suzukiChebyshevLaplaceZeroCoordinate rho).re ≤
      selectedLaplaceUpperAnchor T := by
  unfold selectedLaplaceUpperAnchor selectedLaplaceRealCoordinateWindow
  apply Finset.le_max'
  simp only [Finset.mem_insert, Finset.mem_image]
  exact Or.inr ⟨rho, hrho, rfl⟩

/-- The canonical left boundary lies strictly inside the left edge of the
shifted critical strip. -/
lemma selectedLaplaceLeftBoundary_gt_neg_half (T : ℝ) :
    -(1 / 2 : ℝ) < selectedLaplaceLeftBoundary T := by
  unfold selectedLaplaceLeftBoundary
  have h := selectedLaplaceLowerAnchor_gt_neg_half T
  linarith

/-- The canonical right boundary lies strictly left of the critical line. -/
lemma selectedLaplaceRightBoundary_lt_zero (T : ℝ) :
    selectedLaplaceRightBoundary T < 0 := by
  unfold selectedLaplaceRightBoundary
  have h := selectedLaplaceUpperAnchor_lt_zero T
  linarith

/-- The two canonical horizontal endpoints are ordered, including for an
empty selected window. -/
lemma selectedLaplaceLeftBoundary_le_rightBoundary (T : ℝ) :
    selectedLaplaceLeftBoundary T ≤ selectedLaplaceRightBoundary T := by
  unfold selectedLaplaceLeftBoundary selectedLaplaceRightBoundary
  have hl := selectedLaplaceLowerAnchor_le_zero T
  have hr := neg_half_le_selectedLaplaceUpperAnchor T
  linarith

/-- The canonical left boundary is strictly left of every selected
coordinate. -/
lemma selectedLaplaceLeftBoundary_lt_coordinate
    {T : ℝ} {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralUpperZetaZeroWindow T) :
    selectedLaplaceLeftBoundary T <
      (suzukiChebyshevLaplaceZeroCoordinate rho).re := by
  unfold selectedLaplaceLeftBoundary
  have hhalf := selectedLaplaceZeroCoordinate_re_gt_neg_half rho
  have hanchor := selectedLaplaceLowerAnchor_le_coordinate hrho
  linarith

/-- Every selected coordinate is strictly left of the canonical right
boundary. -/
lemma selectedLaplaceCoordinate_lt_rightBoundary
    {T : ℝ} {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralUpperZetaZeroWindow T) :
    (suzukiChebyshevLaplaceZeroCoordinate rho).re <
      selectedLaplaceRightBoundary T := by
  unfold selectedLaplaceRightBoundary
  have hzero := selectedLaplaceZeroCoordinate_re_lt_zero_of_mem hrho
  have hanchor := selectedLaplaceCoordinate_le_upperAnchor hrho
  linarith

/-- Each quantitative separated height is nonnegative. -/
lemma quantitativeSpectralBoundaryTruncation_nonneg (n : ℕ) :
    0 ≤ quantitativeSpectralBoundaryTruncation n := by
  exact (Nat.cast_nonneg n).trans
    (quantitativeSpectralBoundaryTruncation_spec n).1.le

/-- The canonical rectangle at a quantitative separated height stays inside
the positive shifted-coordinate slab where the complete finite divisor is
available. -/
lemma quantitativeSelectedLaplaceRectangle_subset_finiteSlab (n : ℕ) :
    [[selectedLaplaceLeftBoundary
          (quantitativeSpectralBoundaryTruncation n),
        selectedLaplaceRightBoundary
          (quantitativeSpectralBoundaryTruncation n)]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]] ⊆
      suzukiChebyshevLaplaceFiniteSlab
        (quantitativeSpectralBoundaryTruncation n) := by
  let T := quantitativeSpectralBoundaryTruncation n
  have hT : 0 ≤ T := quantitativeSpectralBoundaryTruncation_nonneg n
  have hlr : selectedLaplaceLeftBoundary T ≤
      selectedLaplaceRightBoundary T :=
    selectedLaplaceLeftBoundary_le_rightBoundary T
  have hbu : -T ≤ T := by linarith
  intro z hz
  rw [uIcc_of_le hlr, uIcc_of_le hbu] at hz
  constructor
  · have hzre : -(1 / 2 : ℝ) < z.re :=
      (selectedLaplaceLeftBoundary_gt_neg_half T).trans_le hz.1.1
    rw [Complex.add_re]
    norm_num
    linarith
  · exact (abs_le.mpr hz.2)

/-- Every selected zero in a quantitative height window lies strictly inside
its canonical rectangle.  Quantitative zero separation makes both vertical
inequalities strict. -/
lemma quantitativeSelectedLaplaceWindow_strictly_inside (n : ℕ)
    {rho : NontrivialZetaZero}
    (hrho : rho ∈ spectralUpperZetaZeroWindow
      (quantitativeSpectralBoundaryTruncation n)) :
    selectedLaplaceLeftBoundary
          (quantitativeSpectralBoundaryTruncation n) <
        (suzukiChebyshevLaplaceZeroCoordinate rho).re ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).re <
        selectedLaplaceRightBoundary
          (quantitativeSpectralBoundaryTruncation n) ∧
      -quantitativeSpectralBoundaryTruncation n <
        (suzukiChebyshevLaplaceZeroCoordinate rho).im ∧
      (suzukiChebyshevLaplaceZeroCoordinate rho).im <
        quantitativeSpectralBoundaryTruncation n := by
  let T := quantitativeSpectralBoundaryTruncation n
  have hT : 0 ≤ T := quantitativeSpectralBoundaryTruncation_nonneg n
  have hwindow : rho ∈ spectralZetaZeroWindow T :=
    (mem_spectralUpperZetaZeroWindow.mp hrho).1
  have habsLe : |(zetaSpectralCoordinate rho.1).re| ≤ T :=
    (mem_spectralZetaZeroWindow hT rho).mp hwindow
  have habsNe : |(zetaSpectralCoordinate rho.1).re| ≠ T := by
    exact quantitativeSpectralBoundaryTruncation_zeroFree n rho
  have habsLt : |(zetaSpectralCoordinate rho.1).re| < T :=
    lt_of_le_of_ne habsLe habsNe
  have him : |(suzukiChebyshevLaplaceZeroCoordinate rho).im| < T := by
    rw [suzukiChebyshevLaplaceZeroCoordinate_im_eq_spectral_re]
    exact habsLt
  exact ⟨selectedLaplaceLeftBoundary_lt_coordinate hrho,
    selectedLaplaceCoordinate_lt_rightBoundary hrho,
    (abs_lt.mp him).1, (abs_lt.mp him).2⟩

/-- The selected finite Cauchy--Green identity on the canonical rectangle,
with no remaining geometric hypotheses or boundary choices. -/
theorem quantitativeSelectedLaplaceBoundaryHeat_finiteCauchyGreen
    (x tau : ℝ) (n : ℕ) :
    (2 * Real.pi * Complex.I) *
        suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau
          (quantitativeSpectralBoundaryTruncation n) =
      rectangularBoundaryIntegral
          (selectedLaplaceLeftBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (selectedLaplaceRightBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        rectangularAreaIntegral
          (selectedLaplaceLeftBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (selectedLaplaceRightBoundary
            (quantitativeSpectralBoundaryTruncation n))
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) := by
  let T := quantitativeSpectralBoundaryTruncation n
  apply
    suzukiChebyshevLaplaceBoundaryHeat_selectedFiniteResidue_eq_boundary_sub_area
      x tau
      (selectedLaplaceLeftBoundary T)
      (selectedLaplaceRightBoundary T) (-T) T
  · exact quantitativeSpectralBoundaryTruncation_nonneg n
  · exact selectedLaplaceLeftBoundary_le_rightBoundary T
  · linarith [quantitativeSpectralBoundaryTruncation_nonneg n]
  · exact selectedLaplaceRightBoundary_lt_zero T
  · exact quantitativeSelectedLaplaceRectangle_subset_finiteSlab n
  · intro rho hrho
    exact quantitativeSelectedLaplaceWindow_strictly_inside n hrho

/-- Along the canonical cofinal zero-free rectangles, the actual arithmetic
boundary-minus-bulk functional converges to `2*pi*i` times the complete
selected boundary-heat total. -/
theorem tendsto_quantitativeSelectedLaplaceBoundarySubArea
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        rectangularBoundaryIntegral
            (selectedLaplaceLeftBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (selectedLaplaceRightBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (-quantitativeSpectralBoundaryTruncation n)
            (quantitativeSpectralBoundaryTruncation n)
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
          rectangularAreaIntegral
            (selectedLaplaceLeftBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (selectedLaplaceRightBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (-quantitativeSpectralBoundaryTruncation n)
            (quantitativeSpectralBoundaryTruncation n)
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau))
      atTop
      (𝓝 ((2 * Real.pi * Complex.I) *
        (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ))) := by
  have hwindow :=
    (tendsto_suzukiChebyshevLaplaceBoundaryHeatResidueWindow x htau).comp
      tendsto_quantitativeSpectralBoundaryTruncation_atTop
  have hscaled : Tendsto
      (fun n : ℕ => (2 * Real.pi * Complex.I) *
        suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau
          (quantitativeSpectralBoundaryTruncation n))
      atTop
      (𝓝 ((2 * Real.pi * Complex.I) *
        (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ))) := by
    simpa only [Function.comp_apply] using
      (tendsto_const_nhds.mul hwindow : Tendsto
        (fun n : ℕ => (2 * Real.pi * Complex.I) *
          (suzukiChebyshevLaplaceBoundaryHeatResidueWindow x tau ∘
            quantitativeSpectralBoundaryTruncation) n)
        atTop
        (𝓝 ((2 * Real.pi * Complex.I) *
          (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ))))
  apply hscaled.congr'
  filter_upwards with n
  exact quantitativeSelectedLaplaceBoundaryHeat_finiteCauchyGreen x tau n

/-- Vanishing of the canonical expanding arithmetic boundary-minus-bulk
functional is equivalent to RH.  The difficult direction remaining for the
project is an unconditional proof of this displayed limit. -/
theorem tendsto_quantitativeSelectedLaplaceBoundarySubArea_zero_iff_rh
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        rectangularBoundaryIntegral
            (selectedLaplaceLeftBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (selectedLaplaceRightBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (-quantitativeSpectralBoundaryTruncation n)
            (quantitativeSpectralBoundaryTruncation n)
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
          rectangularAreaIntegral
            (selectedLaplaceLeftBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (selectedLaplaceRightBoundary
              (quantitativeSpectralBoundaryTruncation n))
            (-quantitativeSpectralBoundaryTruncation n)
            (quantitativeSpectralBoundaryTruncation n)
            (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau))
      atTop (𝓝 0) ↔ RiemannHypothesis := by
  have hlimit :=
    tendsto_quantitativeSelectedLaplaceBoundarySubArea x htau
  constructor
  · intro hzero
    have hscaledZero :
        (2 * Real.pi * Complex.I) *
          (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ) = 0 :=
      tendsto_nhds_unique hlimit hzero
    have hscale : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      exact mul_ne_zero (by norm_num [Real.pi_ne_zero]) Complex.I_ne_zero
    have htotalComplex :
        (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ) = 0 :=
      (mul_eq_zero.mp hscaledZero).resolve_left hscale
    have htotal : riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      Complex.ofReal_eq_zero.mp htotalComplex
    exact
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
        x htau).mp htotal
  · intro hRH
    have htotal : riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
        x htau).mpr hRH
    simpa only [htotal, Complex.ofReal_zero, mul_zero] using hlimit

end

end RiemannGaussian
