import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLogAverageLaplaceBoundaryHeatSelectedHalfStripLimit

/-!
# Four-side decomposition of the genuine near-edge heat functional

The global near-edge identity is useful for estimates only if none of its
geometrically distinct terms are hidden inside one rectangle integral.  This
file introduces oriented bottom, top, right, and left side integrals whose sum
is definitionally the counterclockwise rectangular boundary integral.  It then
specializes those four terms, together with the Cauchy--Green bulk, to the
separated selected half-strip exhaustion.

The resulting five-term arithmetic functional is proved exactly equal to the
finite selected heat-residue sum at every stage.  Its real part is zero, its
imaginary part is nonnegative and detects any selected zero already inside the
rectangle, and it converges without normalization to `2*pi` times the complete
positive heat detector.  No individual side or bulk estimate is asserted;
those are the next arithmetic obligations.
-/

namespace RiemannGaussian

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Interval Topology

/-- The bottom side of a rectangle with its counterclockwise orientation. -/
def rectangularBottomBoundaryIntegral
    (l r b : ℝ) (f : ℂ → ℂ) : ℂ :=
  ∫ a : ℝ in l..r, f ((a : ℂ) + (b : ℂ) * Complex.I)

/-- The top side of a rectangle with its counterclockwise orientation. -/
def rectangularTopBoundaryIntegral
    (l r u : ℝ) (f : ℂ → ℂ) : ℂ :=
  -(∫ a : ℝ in l..r, f ((a : ℂ) + (u : ℂ) * Complex.I))

/-- The right side of a rectangle with its counterclockwise orientation. -/
def rectangularRightBoundaryIntegral
    (r b u : ℝ) (f : ℂ → ℂ) : ℂ :=
  Complex.I *
    ∫ y : ℝ in b..u, f ((r : ℂ) + (y : ℂ) * Complex.I)

/-- The left side of a rectangle with its counterclockwise orientation. -/
def rectangularLeftBoundaryIntegral
    (l b u : ℝ) (f : ℂ → ℂ) : ℂ :=
  -Complex.I *
    ∫ y : ℝ in b..u, f ((l : ℂ) + (y : ℂ) * Complex.I)

/-- A rectangular boundary integral is the sum of its four separately
oriented sides. -/
theorem rectangularBoundaryIntegral_eq_four_oriented_sides
    (l r b u : ℝ) (f : ℂ → ℂ) :
    rectangularBoundaryIntegral l r b u f =
      rectangularBottomBoundaryIntegral l r b f +
        rectangularTopBoundaryIntegral l r u f +
        rectangularRightBoundaryIntegral r b u f +
        rectangularLeftBoundaryIntegral l b u f := by
  unfold rectangularBoundaryIntegral rectangularBottomBoundaryIntegral
    rectangularTopBoundaryIntegral rectangularRightBoundaryIntegral
    rectangularLeftBoundaryIntegral
  ring

/-- The oriented bottom horizontal heat-response integral on the separated
near-edge rectangle at stage `n`. -/
def separatedSelectedLaplaceBottomBoundaryHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularBottomBoundaryIntegral
    (selectedLaplaceSeparatedLeftBoundary n)
    (selectedLaplaceSeparatedRightBoundary n)
    (-quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau)

/-- The oriented top horizontal heat-response integral on the separated
near-edge rectangle at stage `n`. -/
def separatedSelectedLaplaceTopBoundaryHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularTopBoundaryIntegral
    (selectedLaplaceSeparatedLeftBoundary n)
    (selectedLaplaceSeparatedRightBoundary n)
    (quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau)

/-- The oriented near-critical-line vertical heat-response integral at stage
`n`. -/
def separatedSelectedLaplaceRightBoundaryHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularRightBoundaryIntegral
    (selectedLaplaceSeparatedRightBoundary n)
    (-quantitativeSpectralBoundaryTruncation n)
    (quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau)

/-- The oriented near-`Re p=-1/2` vertical heat-response integral at stage
`n`. -/
def separatedSelectedLaplaceLeftBoundaryHeat
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularLeftBoundaryIntegral
    (selectedLaplaceSeparatedLeftBoundary n)
    (-quantitativeSpectralBoundaryTruncation n)
    (quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau)

/-- The Cauchy--Green bulk source over the separated near-edge rectangle at
stage `n`. -/
def separatedSelectedLaplaceBoundaryHeatBulk
    (x tau : ℝ) (n : ℕ) : ℂ :=
  rectangularAreaIntegral
    (selectedLaplaceSeparatedLeftBoundary n)
    (selectedLaplaceSeparatedRightBoundary n)
    (-quantitativeSpectralBoundaryTruncation n)
    (quantitativeSpectralBoundaryTruncation n)
    (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau)

/-- The four oriented heat-response sides minus the corresponding
Cauchy--Green bulk. -/
def separatedSelectedLaplaceBoundaryHeatFunctional
    (x tau : ℝ) (n : ℕ) : ℂ :=
  separatedSelectedLaplaceBottomBoundaryHeat x tau n +
    separatedSelectedLaplaceTopBoundaryHeat x tau n +
    separatedSelectedLaplaceRightBoundaryHeat x tau n +
    separatedSelectedLaplaceLeftBoundaryHeat x tau n -
    separatedSelectedLaplaceBoundaryHeatBulk x tau n

/-- The decomposed five-term functional is exactly the original rectangular
boundary-minus-area functional. -/
theorem separatedSelectedLaplaceBoundaryHeatFunctional_eq_boundary_sub_area
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceBoundaryHeatFunctional x tau n =
      rectangularBoundaryIntegral
          (selectedLaplaceSeparatedLeftBoundary n)
          (selectedLaplaceSeparatedRightBoundary n)
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponse x tau) -
        rectangularAreaIntegral
          (selectedLaplaceSeparatedLeftBoundary n)
          (selectedLaplaceSeparatedRightBoundary n)
          (-quantitativeSpectralBoundaryTruncation n)
          (quantitativeSpectralBoundaryTruncation n)
          (suzukiChebyshevLaplaceBoundaryHeatWeightedResponseSource x tau) := by
  rw [rectangularBoundaryIntegral_eq_four_oriented_sides]
  rfl

/-- At every stage, the decomposed arithmetic functional is exactly `2*pi*i`
times the filtered selected heat-residue sum. -/
theorem separatedSelectedLaplaceBoundaryHeatFunctional_eq_residueWindow
    (x tau : ℝ) (n : ℕ) :
    separatedSelectedLaplaceBoundaryHeatFunctional x tau n =
      (2 * Real.pi * Complex.I) *
        separatedSelectedBoundaryHeatResidueWindow x tau n := by
  rw [separatedSelectedLaplaceBoundaryHeatFunctional_eq_boundary_sub_area]
  exact
    (separatedSelectedLaplaceBoundaryHeat_residueWindow_eq_boundary_sub_area
      x tau n).symm

/-- The decomposed arithmetic functional has zero real part at every stage. -/
theorem separatedSelectedLaplaceBoundaryHeatFunctional_re_eq_zero
    (x tau : ℝ) (n : ℕ) :
    (separatedSelectedLaplaceBoundaryHeatFunctional x tau n).re = 0 := by
  rw [separatedSelectedLaplaceBoundaryHeatFunctional_eq_residueWindow,
    Complex.mul_re]
  rw [separatedSelectedBoundaryHeatResidueWindow_im_eq_zero]
  norm_num

/-- The imaginary part of the decomposed arithmetic functional is `2*pi`
times the real selected heat-residue sum. -/
theorem separatedSelectedLaplaceBoundaryHeatFunctional_im_eq_two_pi_mul
    (x tau : ℝ) (n : ℕ) :
    (separatedSelectedLaplaceBoundaryHeatFunctional x tau n).im =
      2 * Real.pi *
        (separatedSelectedBoundaryHeatResidueWindow x tau n).re := by
  rw [separatedSelectedLaplaceBoundaryHeatFunctional_eq_residueWindow,
    Complex.mul_im]
  norm_num

/-- The imaginary part of the decomposed arithmetic functional is
nonnegative at every stage. -/
theorem separatedSelectedLaplaceBoundaryHeatFunctional_im_nonneg
    (x tau : ℝ) (n : ℕ) :
    0 ≤ (separatedSelectedLaplaceBoundaryHeatFunctional x tau n).im := by
  rw [separatedSelectedLaplaceBoundaryHeatFunctional_im_eq_two_pi_mul]
  exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
    (separatedSelectedBoundaryHeatResidueWindow_re_nonneg x tau n)

/-- The imaginary part of the decomposed arithmetic functional is strictly
positive whenever the stage contains a selected zero. -/
theorem separatedSelectedLaplaceBoundaryHeatFunctional_im_pos_of_mem
    (x tau : ℝ) (n : ℕ) {rho : NontrivialZetaZero}
    (hrho : rho ∈ separatedSelectedZetaZeroWindow n) :
    0 < (separatedSelectedLaplaceBoundaryHeatFunctional x tau n).im := by
  rw [separatedSelectedLaplaceBoundaryHeatFunctional_im_eq_two_pi_mul]
  exact mul_pos (mul_pos (by norm_num) Real.pi_pos)
    (separatedSelectedBoundaryHeatResidueWindow_re_pos_of_mem x tau n hrho)

/-- The five-term near-edge arithmetic functional converges to `2*pi*i`
times the complete upper boundary-heat total. -/
theorem tendsto_separatedSelectedLaplaceBoundaryHeatFunctional
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto (separatedSelectedLaplaceBoundaryHeatFunctional x tau) atTop
      (𝓝 ((2 * Real.pi * Complex.I) *
        (riemannXiUpperHyperbolicBoundaryHeatTotal x tau : ℂ))) := by
  have hlimit := tendsto_separatedSelectedLaplaceBoundarySubArea x htau
  apply hlimit.congr'
  filter_upwards with n
  exact
    (separatedSelectedLaplaceBoundaryHeatFunctional_eq_boundary_sub_area
      x tau n).symm

/-- The nonnegative imaginary part of the decomposed near-edge arithmetic
functional converges, without height normalization, to `2*pi` times the
complete upper boundary-heat total. -/
theorem tendsto_separatedSelectedLaplaceBoundaryHeatFunctional_im
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        (separatedSelectedLaplaceBoundaryHeatFunctional x tau n).im)
      atTop
      (𝓝 (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  have hlimit :=
    tendsto_separatedSelectedLaplaceBoundaryHeatFunctional x htau
  have him := Complex.continuous_im.continuousAt.tendsto.comp hlimit
  convert him using 1
  · rfl
  · norm_num

/-- Convergence of the decomposed nonnegative near-edge scalar to zero is
equivalent to RH.  This is a closure reformulation: the theorem does not prove
the required zero limit. -/
theorem tendsto_separatedSelectedLaplaceBoundaryHeatFunctional_im_zero_iff_rh
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        (separatedSelectedLaplaceBoundaryHeatFunctional x tau n).im)
      atTop (𝓝 0) ↔ RiemannHypothesis := by
  have hlimit :=
    tendsto_separatedSelectedLaplaceBoundaryHeatFunctional_im x htau
  constructor
  · intro hzero
    have hscaled :
        2 * Real.pi * riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      tendsto_nhds_unique hlimit hzero
    have hscale : 2 * Real.pi ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    have htotal : riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      (mul_eq_zero.mp hscaled).resolve_left hscale
    exact
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
        x htau).mp htotal
  · intro hRH
    have htotal : riemannXiUpperHyperbolicBoundaryHeatTotal x tau = 0 :=
      (riemannXiUpperHyperbolicBoundaryHeatTotal_eq_zero_iff_rh
        x htau).mpr hRH
    simpa only [htotal, mul_zero] using hlimit

end

end RiemannGaussian
