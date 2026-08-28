import RiemannGaussian.RiemannXiSuzukiCarrierCayleyLaplaceEnergy

/-!
# Shifted Suzuki traces for the Cayley-Laplace frontier

This file unfolds the genuine Suzuki coefficient inside the half-line
Laplace realization. The exact identities

`g_t(alpha) exp(-i alpha s) = g_(t+s)(alpha) - g_s(alpha)`

and

`g_t(alpha) exp(i alpha s) = g_(t-s)(alpha) - g_(-s)(alpha)`

are proved for the continuously extended screw coefficient, including its
removable value at `alpha = 0`. They turn every finite upper or lower Laplace
synthesis into a difference of shifted-time Suzuki trace windows.

For genuine coefficient tails, each previously isolated Laplace energy is
therefore exactly the squared `L²(0,∞)` Cauchy distance between two trace
increments. The corresponding trace-Cauchy conditions are proved equivalent
to the two Laplace-energy conditions and, together with the real-axis
remainder, sufficient for the original coefficient-tail frontier. No trace
convergence is asserted here.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Topology lp

namespace RiemannGaussian

noncomputable section

/-- The raw screw exponential converts addition of real times into
multiplication. -/
theorem spectralScrewExponential_add
    (t s : ℝ) (alpha : ℂ) :
    spectralScrewExponential (t + s) alpha =
      spectralScrewExponential t alpha *
        spectralScrewExponential s alpha := by
  unfold spectralScrewExponential
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Multiplying Suzuki's extended coefficient by a forward screw exponential
is exactly a difference of two time translates. -/
theorem suzukiSpectralScrewCoefficient_mul_exponential
    (t s : ℝ) (alpha : ℂ) :
    suzukiSpectralScrewCoefficient t alpha *
        spectralScrewExponential s alpha =
      suzukiSpectralScrewCoefficient (t + s) alpha -
        suzukiSpectralScrewCoefficient s alpha := by
  by_cases halpha : alpha = 0
  · subst alpha
    simp [spectralScrewExponential]
    ring
  · rw [suzukiSpectralScrewCoefficient_of_ne_zero t halpha,
      suzukiSpectralScrewCoefficient_of_ne_zero (t + s) halpha,
      suzukiSpectralScrewCoefficient_of_ne_zero s halpha,
      spectralScrewExponential_add]
    field_simp [halpha]
    ring

/-- Multiplying Suzuki's extended coefficient by the reverse screw
exponential is exactly the corresponding backward time-translate
difference. -/
theorem suzukiSpectralScrewCoefficient_mul_reverseExponential
    (t s : ℝ) (alpha : ℂ) :
    suzukiSpectralScrewCoefficient t alpha *
        Complex.exp (Complex.I * alpha * (s : ℂ)) =
      suzukiSpectralScrewCoefficient (t - s) alpha -
        suzukiSpectralScrewCoefficient (-s) alpha := by
  have hexp : Complex.exp (Complex.I * alpha * (s : ℂ)) =
      spectralScrewExponential (-s) alpha := by
    unfold spectralScrewExponential
    congr 1
    push_cast
    ring
  rw [hexp, suzukiSpectralScrewCoefficient_mul_exponential]
  congr 2

/-- The normalized, Cayley-weighted Suzuki coefficient of one genuine xi
node at real time `t`. -/
def suzukiXiCarrierCayleyTimeCoefficient
    (t : ℝ) (rho : NontrivialZetaZero) : ℂ :=
  ((suzukiXiZeroNormalization rho : ℂ) *
      zetaSuzukiSpectralCoefficientFeature t rho) *
    suzukiXiCarrierCayleyNodeParameter rho

/-- Multiplying one weighted coefficient by its upper Laplace mode produces
the exact backward shifted-time coefficient difference. -/
theorem suzukiXiCarrierCayleyTimeCoefficient_mul_upperLaplaceFeature
    (t s : ℝ) (rho : NontrivialZetaZero) :
    suzukiXiCarrierCayleyTimeCoefficient t rho *
        suzukiXiCarrierUpperLaplaceFeature
          (zetaSpectralCoordinate rho.1) s =
      (Real.sqrt 2 : ℂ) *
        (suzukiXiCarrierCayleyTimeCoefficient (t - s) rho - suzukiXiCarrierCayleyTimeCoefficient (-s) rho) := by
  unfold suzukiXiCarrierCayleyTimeCoefficient suzukiXiCarrierUpperLaplaceFeature
    zetaSuzukiSpectralCoefficientFeature
  calc
    (((suzukiXiZeroNormalization rho : ℂ) *
            ((Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) *
              suzukiSpectralScrewCoefficient t
                (zetaSpectralCoordinate rho.1))) *
          suzukiXiCarrierCayleyNodeParameter rho) *
        ((Real.sqrt 2 : ℂ) *
          Complex.exp (Complex.I * zetaSpectralCoordinate rho.1 * (s : ℂ))) =
      (Real.sqrt 2 : ℂ) *
        (((suzukiXiZeroNormalization rho : ℂ) *
            (Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) *
            suzukiXiCarrierCayleyNodeParameter rho) *
          (suzukiSpectralScrewCoefficient t
              (zetaSpectralCoordinate rho.1) *
            Complex.exp
              (Complex.I * zetaSpectralCoordinate rho.1 * (s : ℂ)))) := by
        ring
    _ = (Real.sqrt 2 : ℂ) *
        (((suzukiXiZeroNormalization rho : ℂ) *
            (Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) *
            suzukiXiCarrierCayleyNodeParameter rho) *
          (suzukiSpectralScrewCoefficient (t - s)
              (zetaSpectralCoordinate rho.1) -
            suzukiSpectralScrewCoefficient (-s)
              (zetaSpectralCoordinate rho.1))) := by
        rw [suzukiSpectralScrewCoefficient_mul_reverseExponential]
    _ = (Real.sqrt 2 : ℂ) *
        ((((suzukiXiZeroNormalization rho : ℂ) *
              ((Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) *
                suzukiSpectralScrewCoefficient (t - s)
                  (zetaSpectralCoordinate rho.1))) *
            suzukiXiCarrierCayleyNodeParameter rho) -
          (((suzukiXiZeroNormalization rho : ℂ) *
              ((Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) *
                suzukiSpectralScrewCoefficient (-s)
                  (zetaSpectralCoordinate rho.1))) *
            suzukiXiCarrierCayleyNodeParameter rho)) := by ring

/-- Multiplying one weighted coefficient by its lower Laplace mode produces
the exact forward shifted-time coefficient difference. -/
theorem suzukiXiCarrierCayleyTimeCoefficient_mul_lowerLaplaceFeature
    (t s : ℝ) (rho : NontrivialZetaZero) :
    suzukiXiCarrierCayleyTimeCoefficient t rho *
        suzukiXiCarrierLowerLaplaceFeature
          (zetaSpectralCoordinate rho.1) s =
      (Real.sqrt 2 : ℂ) *
        (suzukiXiCarrierCayleyTimeCoefficient (t + s) rho - suzukiXiCarrierCayleyTimeCoefficient s rho) := by
  unfold suzukiXiCarrierCayleyTimeCoefficient suzukiXiCarrierLowerLaplaceFeature
    zetaSuzukiSpectralCoefficientFeature
  rw [show Complex.exp
      (-Complex.I * zetaSpectralCoordinate rho.1 * (s : ℂ)) =
      spectralScrewExponential s (zetaSpectralCoordinate rho.1) by rfl]
  calc
    (((suzukiXiZeroNormalization rho : ℂ) *
            ((Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) *
              suzukiSpectralScrewCoefficient t
                (zetaSpectralCoordinate rho.1))) *
          suzukiXiCarrierCayleyNodeParameter rho) *
        ((Real.sqrt 2 : ℂ) *
          spectralScrewExponential s (zetaSpectralCoordinate rho.1)) =
      (Real.sqrt 2 : ℂ) *
        (((suzukiXiZeroNormalization rho : ℂ) *
            (Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) *
            suzukiXiCarrierCayleyNodeParameter rho) *
          (suzukiSpectralScrewCoefficient t
              (zetaSpectralCoordinate rho.1) *
            spectralScrewExponential s
              (zetaSpectralCoordinate rho.1))) := by
        ring
    _ = (Real.sqrt 2 : ℂ) *
        (((suzukiXiZeroNormalization rho : ℂ) *
            (Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) *
            suzukiXiCarrierCayleyNodeParameter rho) *
          (suzukiSpectralScrewCoefficient (t + s)
              (zetaSpectralCoordinate rho.1) -
            suzukiSpectralScrewCoefficient s
              (zetaSpectralCoordinate rho.1))) := by
        rw [suzukiSpectralScrewCoefficient_mul_exponential]
    _ = (Real.sqrt 2 : ℂ) *
        ((((suzukiXiZeroNormalization rho : ℂ) *
              ((Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) *
                suzukiSpectralScrewCoefficient (t + s)
                  (zetaSpectralCoordinate rho.1))) *
            suzukiXiCarrierCayleyNodeParameter rho) -
          (((suzukiXiZeroNormalization rho : ℂ) *
              ((Real.sqrt (analyticZetaZeroMultiplicity rho : ℝ) : ℂ) *
                suzukiSpectralScrewCoefficient s
                  (zetaSpectralCoordinate rho.1))) *
            suzukiXiCarrierCayleyNodeParameter rho)) := by ring

private theorem upperSynthesis_offAxisPart
    (c : NontrivialZetaZero →₀ ℂ) (s : ℝ) :
    suzukiXiCarrierCayleyUpperLaplaceSynthesis
        (suzukiXiCarrierCayleyOffAxisPart c) s =
      suzukiXiCarrierCayleyUpperLaplaceSynthesis c s := by
  unfold suzukiXiCarrierCayleyUpperLaplaceSynthesis
    suzukiXiCarrierCayleyUpperLaplaceSummand
    suzukiXiCarrierCayleyOffAxisWeightedCoefficient
    suzukiXiCarrierCayleyOffAxisPart
  rw [Finsupp.support_filter]
  simp only [Finsupp.filter_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · have hne : (zetaSpectralCoordinate rho.1).im ≠ 0 := ne_of_gt hupper
    simp only [if_pos hupper, if_pos hne]
  · simp only [if_neg hupper, ite_self]

private theorem lowerSynthesis_offAxisPart
    (c : NontrivialZetaZero →₀ ℂ) (s : ℝ) :
    suzukiXiCarrierCayleyLowerLaplaceSynthesis
        (suzukiXiCarrierCayleyOffAxisPart c) s =
      suzukiXiCarrierCayleyLowerLaplaceSynthesis c s := by
  unfold suzukiXiCarrierCayleyLowerLaplaceSynthesis
    suzukiXiCarrierCayleyLowerLaplaceSummand
    suzukiXiCarrierCayleyOffAxisWeightedCoefficient
    suzukiXiCarrierCayleyOffAxisPart
  rw [Finsupp.support_filter]
  simp only [Finsupp.filter_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hlower : (zetaSpectralCoordinate rho.1).im < 0
  · have hne : (zetaSpectralCoordinate rho.1).im ≠ 0 := ne_of_lt hlower
    simp only [if_pos hlower, if_pos hne]
  · simp only [if_neg hlower, ite_self]

private def upperCoordinateLinearMap
    (rho : NontrivialZetaZero) (s : ℝ) : ℂ →ₗ[ℂ] ℂ where
  toFun c :=
    if 0 < (zetaSpectralCoordinate rho.1).im then
      (((suzukiXiZeroNormalization rho : ℂ) * c) *
        suzukiXiCarrierCayleyNodeParameter rho) *
          suzukiXiCarrierUpperLaplaceFeature
            (zetaSpectralCoordinate rho.1) s
    else 0
  map_add' c d := by
    by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
    · simp only [if_pos hupper, mul_add, add_mul]
    · simp only [if_neg hupper, add_zero]
  map_smul' c d := by
    by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
    · simp only [if_pos hupper, RingHom.id_apply, smul_eq_mul]
      ring
    · simp only [if_neg hupper, RingHom.id_apply, smul_zero]

private def lowerCoordinateLinearMap
    (rho : NontrivialZetaZero) (s : ℝ) : ℂ →ₗ[ℂ] ℂ where
  toFun c :=
    if (zetaSpectralCoordinate rho.1).im < 0 then
      (((suzukiXiZeroNormalization rho : ℂ) * c) *
        suzukiXiCarrierCayleyNodeParameter rho) *
          suzukiXiCarrierLowerLaplaceFeature
            (zetaSpectralCoordinate rho.1) s
    else 0
  map_add' c d := by
    by_cases hlower : (zetaSpectralCoordinate rho.1).im < 0
    · simp only [if_pos hlower, mul_add, add_mul]
    · simp only [if_neg hlower, add_zero]
  map_smul' c d := by
    by_cases hlower : (zetaSpectralCoordinate rho.1).im < 0
    · simp only [if_pos hlower, RingHom.id_apply, smul_eq_mul]
      ring
    · simp only [if_neg hlower, RingHom.id_apply, smul_zero]

private def upperSynthesisLinearMap (s : ℝ) :
    (NontrivialZetaZero →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun rho ↦ upperCoordinateLinearMap rho s

private def lowerSynthesisLinearMap (s : ℝ) :
    (NontrivialZetaZero →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.lsum ℂ fun rho ↦ lowerCoordinateLinearMap rho s

private theorem upperSynthesisLinearMap_apply
    (s : ℝ) (c : NontrivialZetaZero →₀ ℂ) :
    upperSynthesisLinearMap s c =
      suzukiXiCarrierCayleyUpperLaplaceSynthesis c s := by
  rfl

private theorem lowerSynthesisLinearMap_apply
    (s : ℝ) (c : NontrivialZetaZero →₀ ℂ) :
    lowerSynthesisLinearMap s c =
      suzukiXiCarrierCayleyLowerLaplaceSynthesis c s := by
  rfl

private theorem upperSynthesis_window
    (t T s : ℝ) :
    suzukiXiCarrierCayleyUpperLaplaceSynthesis
        (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T) s =
      ∑ rho ∈ spectralZetaZeroWindow T,
        if 0 < (zetaSpectralCoordinate rho.1).im then
          suzukiXiCarrierCayleyTimeCoefficient t rho *
            suzukiXiCarrierUpperLaplaceFeature
              (zetaSpectralCoordinate rho.1) s
        else 0 := by
  rw [← upperSynthesisLinearMap_apply]
  unfold riemannXiSuzukiSpectralCoefficientWindowFinsupp
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  simp [upperSynthesisLinearMap, upperCoordinateLinearMap,
    suzukiXiCarrierCayleyTimeCoefficient]

private theorem lowerSynthesis_window
    (t T s : ℝ) :
    suzukiXiCarrierCayleyLowerLaplaceSynthesis
        (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T) s =
      ∑ rho ∈ spectralZetaZeroWindow T,
        if (zetaSpectralCoordinate rho.1).im < 0 then
          suzukiXiCarrierCayleyTimeCoefficient t rho *
            suzukiXiCarrierLowerLaplaceFeature
              (zetaSpectralCoordinate rho.1) s
        else 0 := by
  rw [← lowerSynthesisLinearMap_apply]
  unfold riemannXiSuzukiSpectralCoefficientWindowFinsupp
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  simp [lowerSynthesisLinearMap, lowerCoordinateLinearMap,
    suzukiXiCarrierCayleyTimeCoefficient]

/-- The finite upper-half-plane Cayley trace at time `t` and spectral cutoff
`T`, defined as the zero-Laplace-time synthesis. -/
def suzukiXiCarrierCayleyUpperTimeTraceWindow (t T : ℝ) : ℂ :=
  suzukiXiCarrierCayleyUpperLaplaceSynthesis
    (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T) 0

/-- The finite lower-half-plane Cayley trace at time `t` and spectral cutoff
`T`, defined as the zero-Laplace-time synthesis. -/
def suzukiXiCarrierCayleyLowerTimeTraceWindow (t T : ℝ) : ℂ :=
  suzukiXiCarrierCayleyLowerLaplaceSynthesis
    (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T) 0

/-- The upper Cayley time trace is the finite sum of the normalized,
Cayley-weighted Suzuki coefficients over precisely the upper off-axis
nodes. -/
theorem suzukiXiCarrierCayleyUpperTimeTraceWindow_eq_sum
    (t T : ℝ) :
    suzukiXiCarrierCayleyUpperTimeTraceWindow t T =
      ∑ rho ∈ spectralZetaZeroWindow T,
        if 0 < (zetaSpectralCoordinate rho.1).im then
          (Real.sqrt 2 : ℂ) *
            suzukiXiCarrierCayleyTimeCoefficient t rho
        else 0 := by
  unfold suzukiXiCarrierCayleyUpperTimeTraceWindow
  rw [upperSynthesis_window]
  apply Finset.sum_congr rfl
  intro rho _hrho
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · simp only [if_pos hupper]
    unfold suzukiXiCarrierUpperLaplaceFeature
    simp only [ofReal_zero, mul_zero, exp_zero, mul_one]
    ring
  · simp only [if_neg hupper]

/-- The lower Cayley time trace is the finite sum of the normalized,
Cayley-weighted Suzuki coefficients over precisely the lower off-axis
nodes. -/
theorem suzukiXiCarrierCayleyLowerTimeTraceWindow_eq_sum
    (t T : ℝ) :
    suzukiXiCarrierCayleyLowerTimeTraceWindow t T =
      ∑ rho ∈ spectralZetaZeroWindow T,
        if (zetaSpectralCoordinate rho.1).im < 0 then
          (Real.sqrt 2 : ℂ) *
            suzukiXiCarrierCayleyTimeCoefficient t rho
        else 0 := by
  unfold suzukiXiCarrierCayleyLowerTimeTraceWindow
  rw [lowerSynthesis_window]
  apply Finset.sum_congr rfl
  intro rho _hrho
  by_cases hlower : (zetaSpectralCoordinate rho.1).im < 0
  · simp only [if_pos hlower]
    unfold suzukiXiCarrierLowerLaplaceFeature
    simp only [ofReal_zero, mul_zero, exp_zero, mul_one]
    ring
  · simp only [if_neg hlower]

/-- Every finite upper Laplace synthesis is exactly a backward shifted-time
trace difference. -/
theorem suzukiXiCarrierCayleyUpperLaplaceSynthesis_window_eq_timeTraceDifference
    (t T s : ℝ) :
    suzukiXiCarrierCayleyUpperLaplaceSynthesis
        (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T) s =
      suzukiXiCarrierCayleyUpperTimeTraceWindow (t - s) T - suzukiXiCarrierCayleyUpperTimeTraceWindow (-s) T := by
  unfold suzukiXiCarrierCayleyUpperTimeTraceWindow
  rw [upperSynthesis_window, upperSynthesis_window, upperSynthesis_window,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hupper : 0 < (zetaSpectralCoordinate rho.1).im
  · simp only [if_pos hupper]
    rw [suzukiXiCarrierCayleyTimeCoefficient_mul_upperLaplaceFeature]
    unfold suzukiXiCarrierUpperLaplaceFeature
    simp only [ofReal_zero, mul_zero, exp_zero, mul_one]
    ring
  · simp only [if_neg hupper, sub_zero]

/-- Every finite lower Laplace synthesis is exactly a forward shifted-time
trace difference. -/
theorem suzukiXiCarrierCayleyLowerLaplaceSynthesis_window_eq_timeTraceDifference
    (t T s : ℝ) :
    suzukiXiCarrierCayleyLowerLaplaceSynthesis
        (riemannXiSuzukiSpectralCoefficientWindowFinsupp t T) s =
      suzukiXiCarrierCayleyLowerTimeTraceWindow (t + s) T - suzukiXiCarrierCayleyLowerTimeTraceWindow s T := by
  unfold suzukiXiCarrierCayleyLowerTimeTraceWindow
  rw [lowerSynthesis_window, lowerSynthesis_window, lowerSynthesis_window,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  by_cases hlower : (zetaSpectralCoordinate rho.1).im < 0
  · simp only [if_pos hlower]
    rw [suzukiXiCarrierCayleyTimeCoefficient_mul_lowerLaplaceFeature]
    unfold suzukiXiCarrierLowerLaplaceFeature
    simp only [ofReal_zero, mul_zero, exp_zero, mul_one]
    ring
  · simp only [if_neg hlower, sub_zero]

private theorem upperTailSynthesis_eq_timeTraceDifference
    (t T U s : ℝ) :
    suzukiXiCarrierCayleyUpperLaplaceSynthesis
        (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U) s =
      (suzukiXiCarrierCayleyUpperTimeTraceWindow (t - s) T - suzukiXiCarrierCayleyUpperTimeTraceWindow (-s) T) -
        (suzukiXiCarrierCayleyUpperTimeTraceWindow (t - s) U - suzukiXiCarrierCayleyUpperTimeTraceWindow (-s) U) := by
  unfold suzukiXiCoefficientTailCayleyOffAxisFinsupp
  rw [upperSynthesis_offAxisPart]
  unfold riemannXiSuzukiSpectralCoefficientTailFinsupp
  rw [← upperSynthesisLinearMap_apply, map_sub,
    upperSynthesisLinearMap_apply, upperSynthesisLinearMap_apply,
    suzukiXiCarrierCayleyUpperLaplaceSynthesis_window_eq_timeTraceDifference,
    suzukiXiCarrierCayleyUpperLaplaceSynthesis_window_eq_timeTraceDifference]

private theorem lowerTailSynthesis_eq_timeTraceDifference
    (t T U s : ℝ) :
    suzukiXiCarrierCayleyLowerLaplaceSynthesis
        (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U) s =
      (suzukiXiCarrierCayleyLowerTimeTraceWindow (t + s) T - suzukiXiCarrierCayleyLowerTimeTraceWindow s T) -
        (suzukiXiCarrierCayleyLowerTimeTraceWindow (t + s) U - suzukiXiCarrierCayleyLowerTimeTraceWindow s U) := by
  unfold suzukiXiCoefficientTailCayleyOffAxisFinsupp
  rw [lowerSynthesis_offAxisPart]
  unfold riemannXiSuzukiSpectralCoefficientTailFinsupp
  rw [← lowerSynthesisLinearMap_apply, map_sub,
    lowerSynthesisLinearMap_apply, lowerSynthesisLinearMap_apply,
    suzukiXiCarrierCayleyLowerLaplaceSynthesis_window_eq_timeTraceDifference,
    suzukiXiCarrierCayleyLowerLaplaceSynthesis_window_eq_timeTraceDifference]

/-- The upper trace increment sampled by the Laplace synthesis at positive
time `s`. -/
def suzukiXiCarrierCayleyUpperTimeTraceIncrement
    (t T s : ℝ) : ℂ :=
  suzukiXiCarrierCayleyUpperTimeTraceWindow (t - s) T - suzukiXiCarrierCayleyUpperTimeTraceWindow (-s) T

/-- The lower trace increment sampled by the Laplace synthesis at positive
time `s`. -/
def suzukiXiCarrierCayleyLowerTimeTraceIncrement
    (t T s : ℝ) : ℂ :=
  suzukiXiCarrierCayleyLowerTimeTraceWindow (t + s) T - suzukiXiCarrierCayleyLowerTimeTraceWindow s T

/-- The genuine upper coefficient-tail Laplace synthesis is exactly the
difference of two upper trace increments. -/
theorem suzukiXiCoefficientTailCayleyUpperLaplaceSynthesis_eq_timeTraceIncrement_sub
    (t T U s : ℝ) :
    suzukiXiCarrierCayleyUpperLaplaceSynthesis
        (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U) s =
      suzukiXiCarrierCayleyUpperTimeTraceIncrement t T s - suzukiXiCarrierCayleyUpperTimeTraceIncrement t U s := by
  exact upperTailSynthesis_eq_timeTraceDifference t T U s

/-- The genuine lower coefficient-tail Laplace synthesis is exactly the
difference of two lower trace increments. -/
theorem suzukiXiCoefficientTailCayleyLowerLaplaceSynthesis_eq_timeTraceIncrement_sub
    (t T U s : ℝ) :
    suzukiXiCarrierCayleyLowerLaplaceSynthesis
        (suzukiXiCoefficientTailCayleyOffAxisFinsupp t T U) s =
      suzukiXiCarrierCayleyLowerTimeTraceIncrement t T s - suzukiXiCarrierCayleyLowerTimeTraceIncrement t U s := by
  exact lowerTailSynthesis_eq_timeTraceDifference t T U s

/-- The upper tail Laplace energy is the literal squared `L²(0,∞)` distance
between upper trace increments. -/
theorem suzukiXiCoefficientTailCayleyUpperLaplaceEnergy_eq_timeTraceIncrement
    (t T U : ℝ) :
    suzukiXiCoefficientTailCayleyUpperLaplaceEnergy t T U =
      ∫ s : ℝ in Ioi 0,
        ‖suzukiXiCarrierCayleyUpperTimeTraceIncrement t T s - suzukiXiCarrierCayleyUpperTimeTraceIncrement t U s‖ ^ 2 := by
  unfold suzukiXiCoefficientTailCayleyUpperLaplaceEnergy
    suzukiXiCarrierCayleyUpperLaplaceEnergy
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  rw [suzukiXiCoefficientTailCayleyUpperLaplaceSynthesis_eq_timeTraceIncrement_sub]

/-- The lower tail Laplace energy is the literal squared `L²(0,∞)` distance
between lower trace increments. -/
theorem suzukiXiCoefficientTailCayleyLowerLaplaceEnergy_eq_timeTraceIncrement
    (t T U : ℝ) :
    suzukiXiCoefficientTailCayleyLowerLaplaceEnergy t T U =
      ∫ s : ℝ in Ioi 0,
        ‖suzukiXiCarrierCayleyLowerTimeTraceIncrement t T s - suzukiXiCarrierCayleyLowerTimeTraceIncrement t U s‖ ^ 2 := by
  unfold suzukiXiCoefficientTailCayleyLowerLaplaceEnergy
    suzukiXiCarrierCayleyLowerLaplaceEnergy
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  rw [suzukiXiCoefficientTailCayleyLowerLaplaceSynthesis_eq_timeTraceIncrement_sub]

/-- The genuine upper trace increments are Cauchy in their exact half-line
squared-energy metric. -/
def SuzukiXiCarrierCayleyUpperTimeTraceEnergyCauchy (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R,
      (∫ s : ℝ in Ioi 0,
        ‖suzukiXiCarrierCayleyUpperTimeTraceIncrement t T s - suzukiXiCarrierCayleyUpperTimeTraceIncrement t U s‖ ^ 2) <
          epsilon

/-- The genuine lower trace increments are Cauchy in their exact half-line
squared-energy metric. -/
def SuzukiXiCarrierCayleyLowerTimeTraceEnergyCauchy (t : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon → ∃ R : ℝ,
    ∀ T ≥ R, ∀ U ≥ R,
      (∫ s : ℝ in Ioi 0,
        ‖suzukiXiCarrierCayleyLowerTimeTraceIncrement t T s - suzukiXiCarrierCayleyLowerTimeTraceIncrement t U s‖ ^ 2) <
          epsilon

/-- Upper Laplace-energy vanishing is exactly upper shifted-trace energy
Cauchy convergence. -/
theorem suzukiXiCoefficientTailCayleyUpperLaplaceEnergyVanishing_iff_timeTraceCauchy
    (t : ℝ) :
    SuzukiXiCoefficientTailCayleyUpperLaplaceEnergyVanishing t ↔
      SuzukiXiCarrierCayleyUpperTimeTraceEnergyCauchy t := by
  unfold SuzukiXiCoefficientTailCayleyUpperLaplaceEnergyVanishing
    SuzukiXiCarrierCayleyUpperTimeTraceEnergyCauchy
  simp only [suzukiXiCoefficientTailCayleyUpperLaplaceEnergy_eq_timeTraceIncrement]

/-- Lower Laplace-energy vanishing is exactly lower shifted-trace energy
Cauchy convergence. -/
theorem suzukiXiCoefficientTailCayleyLowerLaplaceEnergyVanishing_iff_timeTraceCauchy
    (t : ℝ) :
    SuzukiXiCoefficientTailCayleyLowerLaplaceEnergyVanishing t ↔
      SuzukiXiCarrierCayleyLowerTimeTraceEnergyCauchy t := by
  unfold SuzukiXiCoefficientTailCayleyLowerLaplaceEnergyVanishing
    SuzukiXiCarrierCayleyLowerTimeTraceEnergyCauchy
  simp only [suzukiXiCoefficientTailCayleyLowerLaplaceEnergy_eq_timeTraceIncrement]

/-- Cauchy convergence of both shifted traces, together with real-node
remainder decay, proves the original coefficient-tail Gram frontier. -/
theorem coefficientTailGramVanishing_of_cayleyTimeTraceCauchy_realAxisRemainder
    {t : ℝ} (hupper : SuzukiXiCarrierCayleyUpperTimeTraceEnergyCauchy t)
    (hlower : SuzukiXiCarrierCayleyLowerTimeTraceEnergyCauchy t)
    (hreal : SuzukiXiCoefficientTailCayleyRealAxisRemainderNormVanishing t) :
    SuzukiXiCoefficientTailGramVanishing t := by
  exact
    coefficientTailGramVanishing_of_cayleyLaplaceEnergies_realAxisRemainder
      ((suzukiXiCoefficientTailCayleyUpperLaplaceEnergyVanishing_iff_timeTraceCauchy t).2 hupper)
      ((suzukiXiCoefficientTailCayleyLowerLaplaceEnergyVanishing_iff_timeTraceCauchy t).2 hlower)
      hreal

end

end RiemannGaussian
