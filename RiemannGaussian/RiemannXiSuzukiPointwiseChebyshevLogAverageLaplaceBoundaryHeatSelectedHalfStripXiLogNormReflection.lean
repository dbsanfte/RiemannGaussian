import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedHalfStripXiLogNormGradient

/-!
# Reflect the left xi log-norm heat boundary

The xi functional equation together with conjugation symmetry makes the
shifted log-norm potential `U(a,y)` even in its real coordinate. Its horizontal
derivative and the real heat kernel are both odd, so their boundary product is
even. This module uses those checked symmetries to reflect the selected left
boundary from negative `p` into the positive shifted half-strip.

The reflected boundary lies strictly between `1 / 4` and `1 / 2`; its actual
completed-xi real coordinate lies between `3 / 4` and `1` and tends to `1`.
Replacing the left boundary by this positive-coordinate integral leaves the
full boundary-minus-gradient scalar unchanged and preserves its unnormalized
limit to the nonnegative detector.

This is an exact functional-equation reduction, not a vanishing estimate. The
reflected points still approach `Re s = 1` from below rather than entering the
absolute Dirichlet-series half-plane.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- The shifted xi log-norm potential is even in its real coordinate, by the
xi functional equation and conjugation symmetry. -/
theorem shiftedRiemannXiLogNorm_neg_realCoordinate (a y : ℝ) :
    shiftedRiemannXiLogNorm (-a) y = shiftedRiemannXiLogNorm a y := by
  unfold shiftedRiemannXiLogNorm
  let z : ℂ := (((a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  have hreflect :
      (((-a + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * Complex.I) =
        1 - starRingEnd ℂ z := by
    dsimp [z]
    apply Complex.ext
    · simp
      ring
    · simp
  rw [hreflect, riemannXi_one_sub, riemannXi_conj, norm_conj]

/-- The totalized horizontal derivative of the even shifted xi log-norm
potential is odd in the real coordinate. -/
theorem deriv_shiftedRiemannXiLogNorm_neg_realCoordinate (a y : ℝ) :
    deriv (fun u : ℝ => shiftedRiemannXiLogNorm u y) (-a) =
      -deriv (fun u : ℝ => shiftedRiemannXiLogNorm u y) a := by
  have hfun :
      (fun u : ℝ => shiftedRiemannXiLogNorm (-u) y) =
        fun u : ℝ => shiftedRiemannXiLogNorm u y := by
    funext u
    exact shiftedRiemannXiLogNorm_neg_realCoordinate u y
  have hder := congrArg (fun f : ℝ → ℝ => deriv f a) hfun
  have hneg := deriv_comp_neg
    (f := fun u : ℝ => shiftedRiemannXiLogNorm u y) (x := a)
  rw [hneg] at hder
  linarith

/-- The real boundary-heat kernel is odd in the shifted real coordinate. -/
theorem suzukiChebyshevLaplaceBoundaryHeatRealKernel_neg_realCoordinate (x tau a y : ℝ) :
    suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau (-a) y =
      -suzukiChebyshevLaplaceBoundaryHeatRealKernel x tau a y := by
  unfold suzukiChebyshevLaplaceBoundaryHeatRealKernel
  ring_nf

/-- The product of the two odd factors—the real heat kernel and the horizontal
xi log-norm derivative—is even in the shifted real coordinate. -/
theorem suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand_neg_realCoordinate (x tau a y : ℝ) :
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
        x tau (-a) y =
      suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
        x tau a y := by
  unfold suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand
  rw [suzukiChebyshevLaplaceBoundaryHeatRealKernel_neg_realCoordinate,
    deriv_shiftedRiemannXiLogNorm_neg_realCoordinate]
  ring

/-- The reflection of every selected left boundary lies strictly inside the
positive shifted interval `(1 / 4, 1 / 2)`. -/
theorem selectedLaplaceReflectedLeftBoundary_spec (n : ℕ) :
    1 / 4 < -selectedLaplaceSeparatedLeftBoundary n ∧
      -selectedLaplaceSeparatedLeftBoundary n < 1 / 2 := by
  have hs := selectedLaplaceSeparatedLeftBoundary_spec n
  have hw := selectedLaplaceEdgeWidth_le_quarter n
  constructor
  · linarith
  · linarith

/-- The reflected selected left boundaries tend to the shifted coordinate
`1 / 2` from below. -/
theorem tendsto_selectedLaplaceReflectedLeftBoundary :
    Tendsto (fun n : ℕ => -selectedLaplaceSeparatedLeftBoundary n)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := tendsto_selectedLaplaceSeparatedLeftBoundary_neg_half
  simpa only [neg_neg] using h.neg

/-- The completed-xi real coordinate corresponding to the reflected selected
left shifted boundary. -/
def selectedLaplaceReflectedLeftXiRealCoordinate (n : ℕ) : ℝ :=
  1 / 2 - selectedLaplaceSeparatedLeftBoundary n

/-- Every reflected completed-xi boundary coordinate lies strictly between
`3 / 4` and `1`. -/
theorem selectedLaplaceReflectedLeftXiRealCoordinate_spec (n : ℕ) :
    3 / 4 < selectedLaplaceReflectedLeftXiRealCoordinate n ∧
      selectedLaplaceReflectedLeftXiRealCoordinate n < 1 := by
  have hs := selectedLaplaceReflectedLeftBoundary_spec n
  unfold selectedLaplaceReflectedLeftXiRealCoordinate
  constructor
  · linarith
  · linarith

/-- The reflected completed-xi boundary coordinates tend to `1` from below. -/
theorem tendsto_selectedLaplaceReflectedLeftXiRealCoordinate :
    Tendsto selectedLaplaceReflectedLeftXiRealCoordinate atTop (𝓝 (1 : ℝ)) := by
  have h := tendsto_selectedLaplaceReflectedLeftBoundary
  have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hadd := hc.add h
  convert hadd using 1
  · rfl
  · norm_num

/-- The boundary-minus-gradient scalar with its near-`s = 0` left boundary
reflected to the positive shifted side by xi symmetry. -/
def separatedSelectedLaplaceXiLogNormReflectedGradientScalarHeat (x tau : ℝ) (n : ℕ) : ℝ :=
  (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
      quantitativeSpectralBoundaryTruncation n,
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau
      (selectedLaplaceSeparatedRightBoundary n) y) -
  (∫ y : ℝ in -quantitativeSpectralBoundaryTruncation n..
      quantitativeSpectralBoundaryTruncation n,
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand x tau
      (-selectedLaplaceSeparatedLeftBoundary n) y) -
  ∫ p : ℂ in
      ([[selectedLaplaceSeparatedLeftBoundary n,
          selectedLaplaceSeparatedRightBoundary n]] ×ℂ
        [[-quantitativeSpectralBoundaryTruncation n,
          quantitativeSpectralBoundaryTruncation n]]),
    suzukiChebyshevLaplaceBoundaryHeatXiLogNormGradientIntegrand
      x tau p.re p.im

/-- Reflecting the left xi log-norm boundary leaves the finite-stage
boundary-minus-gradient scalar exactly unchanged. -/
theorem separatedSelectedLaplaceXiLogNormGradientScalarHeat_eq_reflected (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceXiLogNormGradientScalarHeat x tau n =
      separatedSelectedLaplaceXiLogNormReflectedGradientScalarHeat x tau n := by
  unfold separatedSelectedLaplaceXiLogNormGradientScalarHeat
    separatedSelectedLaplaceXiLogNormReflectedGradientScalarHeat
  congr 2
  apply intervalIntegral.integral_congr
  intro y hy
  exact (suzukiChebyshevLaplaceBoundaryHeatXiLogNormBoundaryIntegrand_neg_realCoordinate x tau
    (selectedLaplaceSeparatedLeftBoundary n) y).symm

/-- The reflected positive-coordinate boundary-minus-gradient scalar retains
the unnormalized limit to `2 * pi` times the complete detector. -/
theorem tendsto_separatedSelectedLaplaceXiLogNormReflectedGradientScalarHeat
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto (separatedSelectedLaplaceXiLogNormReflectedGradientScalarHeat x tau) atTop
      (𝓝 (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have hlimit :=
    tendsto_separatedSelectedLaplaceXiLogNormGradientScalarHeat x htau
  apply hlimit.congr'
  exact Eventually.of_forall fun n => separatedSelectedLaplaceXiLogNormGradientScalarHeat_eq_reflected x tau n

end

end RiemannGaussian
