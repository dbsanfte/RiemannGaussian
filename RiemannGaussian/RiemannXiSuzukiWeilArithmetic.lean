import RiemannGaussian.RiemannXiSuzukiWeilTest
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Arithmetic evaluations of Suzuki's Weil test

This file carries out the elementary and prime-sum pieces of the right-hand
side of Suzuki's specialized Weil explicit formula.  It evaluates the
completed-zeta pole integral directly from the already proved transform
theorem, and it derives the zeta logarithmic derivative plus finite von
Mangoldt correction from the literal positive- and negative-logarithm test
samples.

No global Weil distribution identity is assumed here.  Each statement is a
direct integral, pointwise identity, finite sum, or absolutely convergent
Dirichlet-series calculation in Lean.
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

/-! ## Prime samples -/

/-- The von Mangoldt weight occurring in Suzuki's two prime sums. -/
def suzukiWeilPrimeWeight (n : ℕ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)

/-- The positive-logarithm prime sample in the Weil explicit formula. -/
def suzukiWeilPositivePrimeSample
    (t : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  suzukiWeilPrimeWeight n * suzukiWeilTest t z (Real.log n)

/-- The negative-logarithm prime sample in the Weil explicit formula. -/
def suzukiWeilNegativePrimeSample
    (t : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  suzukiWeilPrimeWeight n * suzukiWeilTest t z (-Real.log n)

/-- The exponential Dirichlet term corresponding to the spectral argument
`1/2 - i z`. -/
def suzukiWeilPrimeDirichletTerm (z : ℂ) (n : ℕ) : ℂ :=
  suzukiWeilPrimeWeight n *
    Complex.exp (Complex.I * z * ((Real.log n : ℝ) : ℂ))

@[simp] theorem suzukiWeilPrimeWeight_zero :
    suzukiWeilPrimeWeight 0 = 0 := by
  simp [suzukiWeilPrimeWeight]

@[simp] theorem suzukiWeilPositivePrimeSample_zero
    {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    suzukiWeilPositivePrimeSample t z 0 = 0 := by
  simp [suzukiWeilPositivePrimeSample, ht]

@[simp] theorem suzukiWeilPrimeDirichletTerm_zero (z : ℂ) :
    suzukiWeilPrimeDirichletTerm z 0 = 0 := by
  simp [suzukiWeilPrimeDirichletTerm]

/-- Suzuki's test kills every negative-logarithm sample, including the
endpoint samples `n = 0, 1` where the logarithm is zero. -/
theorem suzukiWeilTest_neg_log_nat
    {t : ℝ} (ht : 0 ≤ t) (z : ℂ) (n : ℕ) :
    suzukiWeilTest t z (-Real.log n) = 0 := by
  rcases (Real.log_natCast_nonneg n).eq_or_lt with hlog | hlog
  · have hx : -Real.log n = 0 := by linarith
    rw [hx, suzukiWeilTest_zero ht]
  · exact suzukiWeilTest_of_neg t z (by linarith)

/-- Consequently the entire negative-logarithm von Mangoldt sample vanishes
pointwise. -/
@[simp] theorem suzukiWeilNegativePrimeSample_eq_zero
    {t : ℝ} (ht : 0 ≤ t) (z : ℂ) (n : ℕ) :
    suzukiWeilNegativePrimeSample t z n = 0 := by
  simp [suzukiWeilNegativePrimeSample, suzukiWeilTest_neg_log_nat ht]

/-- Inside the finite prime window, one positive-logarithm sample is the
Dirichlet tail term minus Suzuki's finite correction term. -/
theorem suzukiWeilPositivePrimeSample_of_mem
    {t : ℝ} {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane) {n : ℕ}
    (hn : n ∈ suzukiArithmeticPrimeWindow t) :
    suzukiWeilPositivePrimeSample t z n =
      suzukiArithmeticScrewQuotient t z *
          suzukiWeilPrimeDirichletTerm z n -
        suzukiArithmeticPrimeTerm t n z := by
  have hnData := (mem_suzukiArithmeticPrimeWindow_iff.mp hn)
  have hn0 : n ≠ 0 := Nat.ne_of_gt hnData.1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnData.1
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlogt : Real.log n ≤ t :=
    (Real.log_le_iff_le_exp hnpos).2 hnData.2
  rw [suzukiWeilPositivePrimeSample, suzukiWeilTest_of_nonneg_of_le z
    hlog0 hlogt]
  have hexp :
      Complex.exp
          (-Complex.I * z * ((t - Real.log n : ℝ) : ℂ)) =
        Complex.exp (-Complex.I * z * (t : ℂ)) *
          Complex.exp (Complex.I * z * ((Real.log n : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold suzukiArithmeticScrewQuotient suzukiWeilPrimeDirichletTerm
    suzukiArithmeticPrimeTerm suzukiWeilPrimeWeight
  rw [hexp]
  have hiz : Complex.I * z ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero
      (ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz)
  field_simp [hiz]
  ring

/-- Beyond the finite prime window, the positive-logarithm sample is exactly
the uncancelled Dirichlet tail term. -/
theorem suzukiWeilPositivePrimeSample_of_not_mem
    {t : ℝ} (ht : 0 ≤ t) (z : ℂ) {n : ℕ} (hn0 : n ≠ 0)
    (hn : n ∉ suzukiArithmeticPrimeWindow t) :
    suzukiWeilPositivePrimeSample t z n =
      suzukiArithmeticScrewQuotient t z *
        suzukiWeilPrimeDirichletTerm z n := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnNotLe : ¬ (n : ℝ) ≤ Real.exp t := by
    intro hle
    exact hn ((mem_suzukiArithmeticPrimeWindow_iff).2 ⟨hn1, hle⟩)
  have htlog : t < Real.log n :=
    (Real.lt_log_iff_exp_lt hnpos).2 (lt_of_not_ge hnNotLe)
  rw [suzukiWeilPositivePrimeSample,
    suzukiWeilTest_of_lt ht z htlog]
  unfold suzukiArithmeticScrewQuotient suzukiWeilPrimeDirichletTerm
  ring

/-- The finitely supported correction sequence cut out by Suzuki's exact
prime window. -/
def suzukiWeilPrimeWindowTerm (t : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  if n ∈ suzukiArithmeticPrimeWindow t then
    suzukiArithmeticPrimeTerm t n z
  else 0

/-- The pointwise prime-sample identity valid at every natural index. -/
theorem suzukiWeilPositivePrimeSample_eq
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) (n : ℕ) :
    suzukiWeilPositivePrimeSample t z n =
      suzukiArithmeticScrewQuotient t z *
          suzukiWeilPrimeDirichletTerm z n -
        suzukiWeilPrimeWindowTerm t z n := by
  unfold suzukiWeilPrimeWindowTerm
  by_cases hn0 : n = 0
  · subst n
    simp [ht, suzukiArithmeticPrimeWindow]
  · by_cases hn : n ∈ suzukiArithmeticPrimeWindow t
    · rw [if_pos hn]
      exact suzukiWeilPositivePrimeSample_of_mem hz hn
    · rw [if_neg hn, sub_zero]
      exact suzukiWeilPositivePrimeSample_of_not_mem ht z hn0 hn

/-- The exponential Dirichlet term is literally the `n`th von Mangoldt
`L`-series term at `1/2 - i z`, including the totalized index `n = 0`. -/
theorem suzukiWeilPrimeDirichletTerm_eq_LSeriesTerm
    (z : ℂ) (n : ℕ) :
    suzukiWeilPrimeDirichletTerm z n =
      LSeries.term
        (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
        (suzukiArithmeticZetaArgument z) n := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [LSeries.term_of_ne_zero hn]
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    have hnComplex : (n : ℂ) ≠ 0 := by
      exact_mod_cast hn
    have hsqrtReal :
        Real.exp (Real.log n / 2) = Real.sqrt n := by
      rw [Real.exp_half, Real.exp_log hnpos]
    have hpow :
        (n : ℂ) ^ suzukiArithmeticZetaArgument z =
          (Real.sqrt n : ℂ) *
            Complex.exp
              (-Complex.I * z * ((Real.log n : ℝ) : ℂ)) := by
      rw [Complex.cpow_def_of_ne_zero hnComplex, ← Complex.natCast_log,
        ← hsqrtReal, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      unfold suzukiArithmeticZetaArgument
      push_cast
      ring
    rw [hpow]
    unfold suzukiWeilPrimeDirichletTerm suzukiWeilPrimeWeight
    have hsqrt : (Real.sqrt n : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr hnpos)
    have hexp :
        Complex.exp
              (-Complex.I * z * ((Real.log n : ℝ) : ℂ)) ≠ 0 :=
      Complex.exp_ne_zero _
    push_cast
    field_simp [hsqrt, hexp]
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
    rw [Complex.exp_zero]
    ring

/-- Above the spectral zero strip, Suzuki's exponential von Mangoldt terms
are absolutely summable. -/
theorem summable_suzukiWeilPrimeDirichletTerm
    {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    Summable (suzukiWeilPrimeDirichletTerm z) := by
  have hRe : (1 : ℝ) < (suzukiArithmeticZetaArgument z).re :=
    mapsTo_suzukiArithmeticZetaArgument hz
  have hL := ArithmeticFunction.LSeriesSummable_vonMangoldt hRe
  exact hL.congr fun n ↦
    (suzukiWeilPrimeDirichletTerm_eq_LSeriesTerm z n).symm

/-- The complete exponential von Mangoldt series is exactly the negative
zeta logarithmic derivative at Suzuki's spectral argument. -/
theorem tsum_suzukiWeilPrimeDirichletTerm
    {z : ℂ} (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    (∑' n : ℕ, suzukiWeilPrimeDirichletTerm z n) =
      -logDeriv riemannZeta (suzukiArithmeticZetaArgument z) := by
  have hRe : (1 : ℝ) < (suzukiArithmeticZetaArgument z).re :=
    mapsTo_suzukiArithmeticZetaArgument hz
  calc
    (∑' n : ℕ, suzukiWeilPrimeDirichletTerm z n) =
        L (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ))
          (suzukiArithmeticZetaArgument z) := by
      unfold LSeries
      apply tsum_congr
      exact suzukiWeilPrimeDirichletTerm_eq_LSeriesTerm z
    _ = -deriv riemannZeta (suzukiArithmeticZetaArgument z) /
          riemannZeta (suzukiArithmeticZetaArgument z) :=
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hRe
    _ = -logDeriv riemannZeta (suzukiArithmeticZetaArgument z) := by
      simp only [logDeriv, Pi.div_apply, neg_div]

/-- Suzuki's exact finite-window correction is a summable sequence. -/
theorem summable_suzukiWeilPrimeWindowTerm (t : ℝ) (z : ℂ) :
    Summable (suzukiWeilPrimeWindowTerm t z) := by
  apply summable_of_hasFiniteSupport
  refine (suzukiArithmeticPrimeWindow t).finite_toSet.subset ?_
  intro n hn
  simp only [Function.mem_support] at hn
  by_contra hmem
  have hmem' : n ∉ suzukiArithmeticPrimeWindow t := by
    simpa using hmem
  exact hn (by simp [suzukiWeilPrimeWindowTerm, hmem'])

/-- The infinite sum of the finite-window correction is the already defined
finite von Mangoldt contribution. -/
theorem tsum_suzukiWeilPrimeWindowTerm (t : ℝ) (z : ℂ) :
    (∑' n : ℕ, suzukiWeilPrimeWindowTerm t z n) =
      suzukiArithmeticPrimeContribution t z := by
  rw [tsum_eq_sum (s := suzukiArithmeticPrimeWindow t) (fun n hn ↦ by
    simp [suzukiWeilPrimeWindowTerm, hn])]
  simp [suzukiWeilPrimeWindowTerm, suzukiArithmeticPrimeContribution]

/-- The positive-logarithm prime samples are absolutely summable on Suzuki's
safe half-plane. -/
theorem summable_suzukiWeilPositivePrimeSample
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    Summable (suzukiWeilPositivePrimeSample t z) := by
  have htail :=
    (summable_suzukiWeilPrimeDirichletTerm hz).mul_left
      (suzukiArithmeticScrewQuotient t z)
  exact (htail.sub (summable_suzukiWeilPrimeWindowTerm t z)).congr
    fun n ↦ (suzukiWeilPositivePrimeSample_eq ht hz n).symm

/-- The full positive-logarithm prime sum is the negative of Suzuki's zeta
logarithmic-derivative term plus finite prime correction. -/
theorem tsum_suzukiWeilPositivePrimeSample
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    (∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) =
      -(suzukiArithmeticZetaContribution t z +
        suzukiArithmeticPrimeContribution t z) := by
  have hdirichlet := summable_suzukiWeilPrimeDirichletTerm hz
  have htail :=
    hdirichlet.mul_left (suzukiArithmeticScrewQuotient t z)
  calc
    (∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) =
        ∑' n : ℕ, (
          suzukiArithmeticScrewQuotient t z *
              suzukiWeilPrimeDirichletTerm z n -
            suzukiWeilPrimeWindowTerm t z n) := by
      apply tsum_congr
      exact suzukiWeilPositivePrimeSample_eq ht hz
    _ = (∑' n : ℕ, suzukiArithmeticScrewQuotient t z *
          suzukiWeilPrimeDirichletTerm z n) -
        ∑' n : ℕ, suzukiWeilPrimeWindowTerm t z n :=
      htail.tsum_sub (summable_suzukiWeilPrimeWindowTerm t z)
    _ = suzukiArithmeticScrewQuotient t z *
          (∑' n : ℕ, suzukiWeilPrimeDirichletTerm z n) -
        suzukiArithmeticPrimeContribution t z := by
      rw [tsum_mul_left, tsum_suzukiWeilPrimeWindowTerm]
    _ = -(suzukiArithmeticZetaContribution t z +
        suzukiArithmeticPrimeContribution t z) := by
      rw [tsum_suzukiWeilPrimeDirichletTerm hz]
      unfold suzukiArithmeticZetaContribution
      ring

/-- The identically zero negative-logarithm sample sequence is summable. -/
theorem summable_suzukiWeilNegativePrimeSample
    {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    Summable (suzukiWeilNegativePrimeSample t z) := by
  have hzero : suzukiWeilNegativePrimeSample t z = 0 := by
    funext n
    exact suzukiWeilNegativePrimeSample_eq_zero ht z n
  rw [hzero]
  exact summable_zero

/-- The complete negative-logarithm prime sum is zero. -/
theorem tsum_suzukiWeilNegativePrimeSample
    {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    (∑' n : ℕ, suzukiWeilNegativePrimeSample t z n) = 0 := by
  have hzero : suzukiWeilNegativePrimeSample t z = 0 := by
    funext n
    exact suzukiWeilNegativePrimeSample_eq_zero ht z n
  rw [hzero]
  exact tsum_zero

/-- With the signs occurring in Weil's explicit formula, the two prime sums
recover exactly Suzuki's zeta and finite-prime contributions. -/
theorem neg_primeSample_tsums_eq_arithmetic
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    -((∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) +
        ∑' n : ℕ, suzukiWeilNegativePrimeSample t z n) =
      suzukiArithmeticZetaContribution t z +
        suzukiArithmeticPrimeContribution t z := by
  rw [tsum_suzukiWeilPositivePrimeSample ht hz,
    tsum_suzukiWeilNegativePrimeSample ht]
  ring

/-- The elementary integral and both signed prime sums together recover the
first three terms of Suzuki's arithmetic formula.  This is the complete
non-Archimedean RHS evaluation; it still does not assume the global Weil
distribution identity. -/
theorem elementary_integral_sub_primeSample_tsums_eq_arithmetic
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    (∫ x : ℝ, suzukiWeilElementaryIntegrand t z x) -
        ((∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) +
          ∑' n : ℕ, suzukiWeilNegativePrimeSample t z n) =
      suzukiArithmeticPoleContribution t z +
        suzukiArithmeticZetaContribution t z +
          suzukiArithmeticPrimeContribution t z := by
  rw [integral_suzukiWeilElementaryIntegrand ht hz]
  calc
    suzukiArithmeticPoleContribution t z -
          ((∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) +
            ∑' n : ℕ, suzukiWeilNegativePrimeSample t z n) =
        suzukiArithmeticPoleContribution t z +
          -((∑' n : ℕ, suzukiWeilPositivePrimeSample t z n) +
            ∑' n : ℕ, suzukiWeilNegativePrimeSample t z n) := by
      ring
    _ = suzukiArithmeticPoleContribution t z +
          (suzukiArithmeticZetaContribution t z +
            suzukiArithmeticPrimeContribution t z) := by
      rw [neg_primeSample_tsums_eq_arithmetic ht hz]
    _ = suzukiArithmeticPoleContribution t z +
          suzukiArithmeticZetaContribution t z +
            suzukiArithmeticPrimeContribution t z := by
      ring

end

end RiemannGaussian
