import RiemannGaussian.RiemannXiSuzukiWeilTest
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Arithmetic evaluations of Suzuki's Weil test

This file begins the right-hand-side calculation in Suzuki's specialized
Weil explicit formula.  It evaluates the elementary completed-zeta pole
integral directly from the already proved transform theorem.

No global Weil distribution identity is assumed here.  Each statement is a
direct integral or algebraic calculation in Lean.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval LSeries.notation Topology lp

namespace RiemannGaussian

noncomputable section

/-- The spectral frequency representing the elementary factor `exp(x/2)`. -/
def suzukiWeilUpperPoleFrequency : ℂ :=
  Complex.I / 2

/-- The spectral frequency representing the elementary factor `exp(-x/2)`. -/
def suzukiWeilLowerPoleFrequency : ℂ :=
  -Complex.I / 2

/-- The upper pole frequency has imaginary part `1/2`. -/
@[simp] theorem suzukiWeilUpperPoleFrequency_im :
    suzukiWeilUpperPoleFrequency.im = 1 / 2 := by
  simp [suzukiWeilUpperPoleFrequency]

/-- The lower pole frequency has imaginary part `-1/2`. -/
@[simp] theorem suzukiWeilLowerPoleFrequency_im :
    suzukiWeilLowerPoleFrequency.im = -1 / 2 := by
  simp [suzukiWeilLowerPoleFrequency]

/-- The upper pole frequency is nonzero. -/
theorem suzukiWeilUpperPoleFrequency_ne_zero :
    suzukiWeilUpperPoleFrequency ≠ 0 := by
  simp [suzukiWeilUpperPoleFrequency]

/-- The lower pole frequency is nonzero. -/
theorem suzukiWeilLowerPoleFrequency_ne_zero :
    suzukiWeilLowerPoleFrequency ≠ 0 := by
  simp [suzukiWeilLowerPoleFrequency]

/-- Fourier oscillation at the upper pole frequency is `exp(x/2)`. -/
theorem exp_neg_I_mul_suzukiWeilUpperPoleFrequency (x : ℝ) :
    Complex.exp
        (-Complex.I * suzukiWeilUpperPoleFrequency * (x : ℂ)) =
      (Real.exp (x / 2) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  unfold suzukiWeilUpperPoleFrequency
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Fourier oscillation at the lower pole frequency is `exp(-x/2)`. -/
theorem exp_neg_I_mul_suzukiWeilLowerPoleFrequency (x : ℝ) :
    Complex.exp
        (-Complex.I * suzukiWeilLowerPoleFrequency * (x : ℂ)) =
      (Real.exp (-x / 2) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  unfold suzukiWeilLowerPoleFrequency
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The elementary completed-zeta integrand in the Weil formula. -/
def suzukiWeilElementaryIntegrand
    (t : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  suzukiWeilTest t z x *
    ((Real.exp (x / 2) : ℂ) + (Real.exp (-x / 2) : ℂ))

/-- The upper elementary integrand is the Fourier integrand at frequency
`i/2`. -/
theorem suzukiWeilFourierIntegrand_upperPole
    (t : ℝ) (z : ℂ) (x : ℝ) :
    suzukiWeilFourierIntegrand t z
        suzukiWeilUpperPoleFrequency x =
      suzukiWeilTest t z x * (Real.exp (x / 2) : ℂ) := by
  unfold suzukiWeilFourierIntegrand
  rw [exp_neg_I_mul_suzukiWeilUpperPoleFrequency]

/-- The lower elementary integrand is the Fourier integrand at frequency
`-i/2`. -/
theorem suzukiWeilFourierIntegrand_lowerPole
    (t : ℝ) (z : ℂ) (x : ℝ) :
    suzukiWeilFourierIntegrand t z
        suzukiWeilLowerPoleFrequency x =
      suzukiWeilTest t z x * (Real.exp (-x / 2) : ℂ) := by
  unfold suzukiWeilFourierIntegrand
  rw [exp_neg_I_mul_suzukiWeilLowerPoleFrequency]

/-- The upper elementary factor is absolutely integrable against Suzuki's
test at every safe point. -/
theorem integrable_suzukiWeilUpperPoleIntegrand
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    Integrable
      (fun x : ℝ ↦
        suzukiWeilTest t z x * (Real.exp (x / 2) : ℂ)) := by
  have hgap : suzukiWeilUpperPoleFrequency.im < z.im := by
    change (1 / 2 : ℝ) < z.im at hz
    simpa using hz
  exact (integrable_suzukiWeilFourierIntegrand ht hgap).congr
    (Filter.Eventually.of_forall fun x ↦
      suzukiWeilFourierIntegrand_upperPole t z x)

/-- The lower elementary factor is absolutely integrable against Suzuki's
test at every safe point. -/
theorem integrable_suzukiWeilLowerPoleIntegrand
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    Integrable
      (fun x : ℝ ↦
        suzukiWeilTest t z x * (Real.exp (-x / 2) : ℂ)) := by
  have hgap : suzukiWeilLowerPoleFrequency.im < z.im := by
    change (1 / 2 : ℝ) < z.im at hz
    rw [suzukiWeilLowerPoleFrequency_im]
    linarith
  exact (integrable_suzukiWeilFourierIntegrand ht hgap).congr
    (Filter.Eventually.of_forall fun x ↦
      suzukiWeilFourierIntegrand_lowerPole t z x)

/-- The `exp(x/2)` integral is the upper completed-zeta pole term. -/
theorem integral_suzukiWeilUpperPoleIntegrand
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    (∫ x : ℝ,
      suzukiWeilTest t z x * (Real.exp (x / 2) : ℂ)) =
      ((4 * (Real.exp (t / 2) - 1) : ℝ) : ℂ) /
        (1 + 2 * Complex.I * z) := by
  have hgap : suzukiWeilUpperPoleFrequency.im < z.im := by
    change (1 / 2 : ℝ) < z.im at hz
    simpa using hz
  calc
    (∫ x : ℝ,
        suzukiWeilTest t z x * (Real.exp (x / 2) : ℂ)) =
        suzukiSpectralScrewCoefficient t
            suzukiWeilUpperPoleFrequency /
          (z - suzukiWeilUpperPoleFrequency) := by
      rw [← integral_suzukiWeilFourierIntegrand ht
        (ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz) hgap]
      apply integral_congr_ae
      filter_upwards with x
      exact (suzukiWeilFourierIntegrand_upperPole t z x).symm
    _ = ((4 * (Real.exp (t / 2) - 1) : ℝ) : ℂ) /
          (1 + 2 * Complex.I * z) := by
      rw [suzukiSpectralScrewCoefficient_of_ne_zero t
        suzukiWeilUpperPoleFrequency_ne_zero]
      unfold spectralScrewExponential
      rw [exp_neg_I_mul_suzukiWeilUpperPoleFrequency]
      have hzgap : z - suzukiWeilUpperPoleFrequency ≠ 0 := by
        intro h
        have him := congrArg Complex.im h
        simp at him
        rw [suzukiWeilUpperPoleFrequency_im] at hgap
        linarith
      have hden : 1 + Complex.I * z * 2 ≠ 0 := by
        convert
          one_add_two_I_mul_ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz
          using 1
        ring
      have hzgapExplicit : z - Complex.I / 2 ≠ 0 := by
        simpa [suzukiWeilUpperPoleFrequency] using hzgap
      have hzgap' : z * 2 - Complex.I ≠ 0 := by
        convert mul_ne_zero hzgapExplicit (by norm_num : (2 : ℂ) ≠ 0)
          using 1
        ring
      have hden' : 1 + z * Complex.I * 2 ≠ 0 := by
        convert hden using 1
        ring
      have hden'' : 1 + z * 2 * Complex.I ≠ 0 := by
        convert hden using 1
        ring
      unfold suzukiWeilUpperPoleFrequency at hzgap ⊢
      field_simp [hzgap, hden, Complex.I_ne_zero,
        one_add_two_I_mul_ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz]
      ring_nf
      field_simp [hzgap', hden', hden'', hden]
      ring_nf
      rw [Complex.I_sq]
      push_cast
      ring

/-- The `exp(-x/2)` integral is the lower completed-zeta pole term. -/
theorem integral_suzukiWeilLowerPoleIntegrand
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    (∫ x : ℝ,
      suzukiWeilTest t z x * (Real.exp (-x / 2) : ℂ)) =
      ((4 * (Real.exp (-t / 2) - 1) : ℝ) : ℂ) /
        (1 - 2 * Complex.I * z) := by
  have hgap : suzukiWeilLowerPoleFrequency.im < z.im := by
    change (1 / 2 : ℝ) < z.im at hz
    rw [suzukiWeilLowerPoleFrequency_im]
    linarith
  calc
    (∫ x : ℝ,
        suzukiWeilTest t z x * (Real.exp (-x / 2) : ℂ)) =
        suzukiSpectralScrewCoefficient t
            suzukiWeilLowerPoleFrequency /
          (z - suzukiWeilLowerPoleFrequency) := by
      rw [← integral_suzukiWeilFourierIntegrand ht
        (ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz) hgap]
      apply integral_congr_ae
      filter_upwards with x
      exact (suzukiWeilFourierIntegrand_lowerPole t z x).symm
    _ = ((4 * (Real.exp (-t / 2) - 1) : ℝ) : ℂ) /
          (1 - 2 * Complex.I * z) := by
      rw [suzukiSpectralScrewCoefficient_of_ne_zero t
        suzukiWeilLowerPoleFrequency_ne_zero]
      unfold spectralScrewExponential
      rw [exp_neg_I_mul_suzukiWeilLowerPoleFrequency]
      have hzgap : z - suzukiWeilLowerPoleFrequency ≠ 0 := by
        intro h
        have him := congrArg Complex.im h
        simp at him
        rw [suzukiWeilLowerPoleFrequency_im] at hgap
        linarith
      have hden : 1 - Complex.I * z * 2 ≠ 0 := by
        convert
          one_sub_two_I_mul_ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz
          using 1
        ring
      have hzgapExplicit : z - -Complex.I / 2 ≠ 0 := by
        simpa [suzukiWeilLowerPoleFrequency] using hzgap
      have hzgap' : z * 2 + Complex.I ≠ 0 := by
        convert mul_ne_zero hzgapExplicit (by norm_num : (2 : ℂ) ≠ 0)
          using 1
        ring
      have hden' : 1 - z * Complex.I * 2 ≠ 0 := by
        convert hden using 1
        ring
      have hden'' : 1 - z * 2 * Complex.I ≠ 0 := by
        convert hden using 1
        ring
      unfold suzukiWeilLowerPoleFrequency at hzgap ⊢
      field_simp [hzgap, hden, Complex.I_ne_zero,
        one_sub_two_I_mul_ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz]
      ring_nf
      field_simp [hzgap', hden', hden'', hden]
      ring_nf
      rw [Complex.I_sq]
      push_cast
      ring

/-- The complete elementary integral is exactly the two-pole contribution in
Suzuki's arithmetic formula (1.6). -/
theorem integral_suzukiWeilElementaryIntegrand
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    (∫ x : ℝ, suzukiWeilElementaryIntegrand t z x) =
      suzukiArithmeticPoleContribution t z := by
  have hu := integrable_suzukiWeilUpperPoleIntegrand ht hz
  have hl := integrable_suzukiWeilLowerPoleIntegrand ht hz
  rw [show (∫ x : ℝ, suzukiWeilElementaryIntegrand t z x) =
      (∫ x : ℝ,
        suzukiWeilTest t z x * (Real.exp (x / 2) : ℂ)) +
      ∫ x : ℝ,
        suzukiWeilTest t z x * (Real.exp (-x / 2) : ℂ) by
    rw [← integral_add hu hl]
    apply integral_congr_ae
    filter_upwards with x
    unfold suzukiWeilElementaryIntegrand
    ring]
  rw [integral_suzukiWeilUpperPoleIntegrand ht hz,
    integral_suzukiWeilLowerPoleIntegrand ht hz]
  rfl

end

end RiemannGaussian
