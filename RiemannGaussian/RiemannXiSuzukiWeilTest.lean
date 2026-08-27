import RiemannGaussian.RiemannXiSuzukiArithmeticFormula
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Suzuki's piecewise Weil test and its exact zero transform

For nonnegative screw time, Suzuki obtains the spectral summand in his
explicit formula from a piecewise test supported on the positive half-line.
This file constructs that literal test and evaluates its Fourier--Laplace
transform against an arbitrary complex spectral frequency below the
evaluation point.

The transform theorem is unconditional and includes the removable spectral
frequency `gamma = 0`: its value agrees with the continuously extended Suzuki
coefficient already used by the project.  Specializing to every genuine zeta
zero therefore identifies one test-function transform, including analytic
multiplicity, with one summand of the infinite spectral `P_t` series.

This is the local spectral calculation inside Suzuki's proof of Proposition
3.1.  It does not invoke, or assume, the global Weil explicit formula that
equates the sum of these transforms with the arithmetic prime/gamma side.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology lp

namespace RiemannGaussian

noncomputable section

/-- Suzuki's positive-time piecewise Weil test.  On `[0,t]` it is
`(1 - exp(i z x))/(i z)`; above `t` it is continued by the decaying
exponential with the same boundary value; and below zero it vanishes. -/
def suzukiWeilTest (t : ℝ) (z : ℂ) (x : ℝ) : ℂ :=
  if x < 0 then
    0
  else if x ≤ t then
    (1 - Complex.exp (Complex.I * z * (x : ℂ))) /
      (Complex.I * z)
  else
    Complex.exp (Complex.I * z * (x : ℂ)) *
      (Complex.exp (-Complex.I * z * (t : ℂ)) - 1) /
        (Complex.I * z)

/-- The Suzuki test vanishes on the negative half-line. -/
@[simp] theorem suzukiWeilTest_of_neg
    (t : ℝ) (z : ℂ) {x : ℝ} (hx : x < 0) :
    suzukiWeilTest t z x = 0 := by
  simp [suzukiWeilTest, hx]

/-- The middle branch of the Suzuki test. -/
theorem suzukiWeilTest_of_nonneg_of_le
    {t x : ℝ} (z : ℂ) (hx0 : 0 ≤ x) (hxt : x ≤ t) :
    suzukiWeilTest t z x =
      (1 - Complex.exp (Complex.I * z * (x : ℂ))) /
        (Complex.I * z) := by
  simp [suzukiWeilTest, not_lt.mpr hx0, hxt]

/-- The exponentially decaying tail branch of the Suzuki test. -/
theorem suzukiWeilTest_of_lt
    {t x : ℝ} (ht : 0 ≤ t) (z : ℂ) (htx : t < x) :
    suzukiWeilTest t z x =
      Complex.exp (Complex.I * z * (x : ℂ)) *
        (Complex.exp (-Complex.I * z * (t : ℂ)) - 1) /
          (Complex.I * z) := by
  have hx0 : 0 ≤ x := ht.trans (le_of_lt htx)
  simp [suzukiWeilTest, not_lt.mpr hx0, not_le.mpr htx]

/-- The test has its genuine value zero at the origin. -/
@[simp] theorem suzukiWeilTest_zero
    {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    suzukiWeilTest t z 0 = 0 := by
  rw [suzukiWeilTest_of_nonneg_of_le z le_rfl ht]
  simp

/-- The Fourier--Laplace integrand used by Suzuki for one spectral
frequency. -/
def suzukiWeilFourierIntegrand
    (t : ℝ) (z gamma : ℂ) (x : ℝ) : ℂ :=
  suzukiWeilTest t z x *
    Complex.exp (-Complex.I * gamma * (x : ℂ))

/-- On the compact middle interval, the Fourier integrand is a difference of
two elementary exponentials divided by `i z`. -/
theorem suzukiWeilFourierIntegrand_of_mem_Icc
    {t x : ℝ} (z gamma : ℂ) (hx : x ∈ Icc 0 t) :
    suzukiWeilFourierIntegrand t z gamma x =
      (Complex.exp ((-Complex.I * gamma) * (x : ℂ)) -
          Complex.exp ((Complex.I * (z - gamma)) * (x : ℂ))) /
        (Complex.I * z) := by
  unfold suzukiWeilFourierIntegrand
  rw [suzukiWeilTest_of_nonneg_of_le z hx.1 hx.2]
  have hexp :
      Complex.exp (Complex.I * z * (x : ℂ)) *
          Complex.exp (-Complex.I * gamma * (x : ℂ)) =
        Complex.exp ((Complex.I * (z - gamma)) * (x : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [div_mul_eq_mul_div, sub_mul, one_mul, hexp]

/-- On the tail, the Fourier integrand is a constant times the decaying gap
exponential. -/
theorem suzukiWeilFourierIntegrand_of_mem_Ioi
    {t x : ℝ} (ht : 0 ≤ t) (z gamma : ℂ) (hx : x ∈ Ioi t) :
    suzukiWeilFourierIntegrand t z gamma x =
      ((Complex.exp (-Complex.I * z * (t : ℂ)) - 1) /
          (Complex.I * z)) *
        Complex.exp ((Complex.I * (z - gamma)) * (x : ℂ)) := by
  unfold suzukiWeilFourierIntegrand
  rw [suzukiWeilTest_of_lt ht z hx]
  have hexp :
      Complex.exp (Complex.I * z * (x : ℂ)) *
          Complex.exp (-Complex.I * gamma * (x : ℂ)) =
        Complex.exp ((Complex.I * (z - gamma)) * (x : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    Complex.exp (Complex.I * z * (x : ℂ)) *
          (Complex.exp (-Complex.I * z * (t : ℂ)) - 1) /
            (Complex.I * z) *
        Complex.exp (-Complex.I * gamma * (x : ℂ)) =
        ((Complex.exp (-Complex.I * z * (t : ℂ)) - 1) /
            (Complex.I * z)) *
          (Complex.exp (Complex.I * z * (x : ℂ)) *
            Complex.exp (-Complex.I * gamma * (x : ℂ))) := by
      ring
    _ = ((Complex.exp (-Complex.I * z * (t : ℂ)) - 1) /
          (Complex.I * z)) *
        Complex.exp ((Complex.I * (z - gamma)) * (x : ℂ)) := by
      rw [hexp]

/-- Below zero the Fourier integrand vanishes. -/
@[simp] theorem suzukiWeilFourierIntegrand_of_neg
    (t : ℝ) (z gamma : ℂ) {x : ℝ} (hx : x < 0) :
    suzukiWeilFourierIntegrand t z gamma x = 0 := by
  simp [suzukiWeilFourierIntegrand, suzukiWeilTest_of_neg t z hx]

/-- The imaginary-height gap is exactly the negative real part of the tail
exponent. -/
theorem re_I_mul_sub (z gamma : ℂ) :
    (Complex.I * (z - gamma)).re = gamma.im - z.im := by
  simp

/-- Suzuki's Fourier integrand is absolutely integrable whenever the
evaluation point lies strictly above the spectral frequency. -/
theorem integrable_suzukiWeilFourierIntegrand
    {t : ℝ} (ht : 0 ≤ t) {z gamma : ℂ}
    (hgap : gamma.im < z.im) :
    Integrable (suzukiWeilFourierIntegrand t z gamma) := by
  let middle : ℝ → ℂ := fun x ↦
    (Complex.exp ((-Complex.I * gamma) * (x : ℂ)) -
        Complex.exp ((Complex.I * (z - gamma)) * (x : ℂ))) /
      (Complex.I * z)
  let tail : ℝ → ℂ := fun x ↦
    ((Complex.exp (-Complex.I * z * (t : ℂ)) - 1) /
        (Complex.I * z)) *
      Complex.exp ((Complex.I * (z - gamma)) * (x : ℂ))
  have hmiddleContinuous : Continuous middle := by
    dsimp [middle]
    fun_prop
  have hmiddle : IntegrableOn
      (suzukiWeilFourierIntegrand t z gamma) (Icc 0 t) := by
    exact hmiddleContinuous.integrableOn_Icc.congr_fun
      (fun x hx ↦ by
        simpa [middle] using
          (suzukiWeilFourierIntegrand_of_mem_Icc z gamma hx).symm)
      measurableSet_Icc
  have htailFrequency : (Complex.I * (z - gamma)).re < 0 := by
    rw [re_I_mul_sub]
    linarith
  have htailModel : IntegrableOn tail (Ioi t) := by
    dsimp [tail]
    exact (integrableOn_exp_mul_complex_Ioi htailFrequency t).const_mul _
  have htail : IntegrableOn
      (suzukiWeilFourierIntegrand t z gamma) (Ioi t) := by
    exact htailModel.congr_fun
      (fun x hx ↦ by
        simpa [tail] using
          (suzukiWeilFourierIntegrand_of_mem_Ioi ht z gamma hx).symm)
      measurableSet_Ioi
  have hnonnegative : IntegrableOn
      (suzukiWeilFourierIntegrand t z gamma) (Ici 0) := by
    rw [← Icc_union_Ioi_eq_Ici ht]
    exact hmiddle.union htail
  have hnegative : IntegrableOn
      (suzukiWeilFourierIntegrand t z gamma) (Iio 0) := by
    exact integrableOn_zero.congr_fun
      (fun x hx ↦ by
        symm
        exact suzukiWeilFourierIntegrand_of_neg t z gamma hx)
      measurableSet_Iio
  rw [← integrableOn_univ, ← Iio_union_Ici]
  exact hnegative.union hnonnegative

/-- The full transform splits into its compact middle integral and decaying
tail integral. -/
theorem integral_suzukiWeilFourierIntegrand_eq_middle_add_tail
    {t : ℝ} (ht : 0 ≤ t) {z gamma : ℂ}
    (hgap : gamma.im < z.im) :
    (∫ x : ℝ, suzukiWeilFourierIntegrand t z gamma x) =
      (∫ x : ℝ in 0..t,
        (Complex.exp ((-Complex.I * gamma) * (x : ℂ)) -
            Complex.exp ((Complex.I * (z - gamma)) * (x : ℂ))) /
          (Complex.I * z)) +
      ∫ x : ℝ in Ioi t,
        ((Complex.exp (-Complex.I * z * (t : ℂ)) - 1) /
            (Complex.I * z)) *
          Complex.exp ((Complex.I * (z - gamma)) * (x : ℂ)) := by
  have hintegrable :=
    integrable_suzukiWeilFourierIntegrand ht hgap
  have hmiddle : IntegrableOn
      (suzukiWeilFourierIntegrand t z gamma) (Icc 0 t) :=
    hintegrable.integrableOn
  have htail : IntegrableOn
      (suzukiWeilFourierIntegrand t z gamma) (Ioi t) :=
    hintegrable.integrableOn
  calc
    (∫ x : ℝ, suzukiWeilFourierIntegrand t z gamma x) =
        (∫ x : ℝ in Ici 0,
          suzukiWeilFourierIntegrand t z gamma x) := by
      have hzero :
          (∫ x : ℝ in (Ici (0 : ℝ))ᶜ,
            suzukiWeilFourierIntegrand t z gamma x) = 0 := by
        rw [compl_Ici]
        exact setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦
          suzukiWeilFourierIntegrand_of_neg t z gamma hx
      have hadd := integral_add_compl
        (s := Ici (0 : ℝ)) measurableSet_Ici hintegrable
      rw [hzero, add_zero] at hadd
      exact hadd.symm
    _ = (∫ x : ℝ in Icc 0 t,
          suzukiWeilFourierIntegrand t z gamma x) +
        ∫ x : ℝ in Ioi t,
          suzukiWeilFourierIntegrand t z gamma x := by
      have hdisjoint : Disjoint (Icc (0 : ℝ) t) (Ioi t) := by
        refine Set.disjoint_left.2 ?_
        intro x hx hxt
        exact (not_lt_of_ge hx.2) hxt
      rw [← Icc_union_Ioi_eq_Ici ht,
        setIntegral_union hdisjoint measurableSet_Ioi hmiddle htail]
    _ = (∫ x : ℝ in 0..t,
          (Complex.exp ((-Complex.I * gamma) * (x : ℂ)) -
              Complex.exp ((Complex.I * (z - gamma)) * (x : ℂ))) /
            (Complex.I * z)) +
        ∫ x : ℝ in Ioi t,
          ((Complex.exp (-Complex.I * z * (t : ℂ)) - 1) /
              (Complex.I * z)) *
            Complex.exp ((Complex.I * (z - gamma)) * (x : ℂ)) := by
      congr 1
      · rw [integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le ht]
        apply intervalIntegral.integral_congr
        intro x hx
        apply suzukiWeilFourierIntegrand_of_mem_Icc z gamma
        simpa [uIcc_of_le ht] using hx
      · apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact suzukiWeilFourierIntegrand_of_mem_Ioi ht z gamma hx

/-- At zero spectral frequency, Suzuki's transform has precisely the
removable coefficient value. -/
theorem integral_suzukiWeilFourierIntegrand_zero
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ≠ 0)
    (hzIm : 0 < z.im) :
    (∫ x : ℝ, suzukiWeilFourierIntegrand t z 0 x) =
      suzukiSpectralScrewCoefficient t 0 / (z - 0) := by
  rw [integral_suzukiWeilFourierIntegrand_eq_middle_add_tail ht hzIm]
  have hzFrequency : Complex.I * z ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hz
  have hzFrequencyRe : (Complex.I * z).re < 0 := by
    simp
    exact hzIm
  have honeIntegrable : IntervalIntegrable
      (fun _ : ℝ ↦ (1 : ℂ)) volume 0 t :=
    continuous_const.intervalIntegrable 0 t
  have hgapIntegrable : IntervalIntegrable
      (fun x : ℝ ↦
        Complex.exp ((Complex.I * (z - 0)) * (x : ℂ)))
      volume 0 t :=
    (show Continuous (fun x : ℝ ↦
      Complex.exp ((Complex.I * (z - 0)) * (x : ℂ))) by
        fun_prop).intervalIntegrable 0 t
  simp only [mul_zero, zero_mul, Complex.exp_zero, sub_zero]
    at hgapIntegrable ⊢
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub honeIntegrable hgapIntegrable,
    intervalIntegral.integral_const,
    integral_exp_mul_complex hzFrequency,
    MeasureTheory.integral_const_mul,
    integral_exp_mul_complex_Ioi hzFrequencyRe t,
    suzukiSpectralScrewCoefficient_zero]
  simp only [sub_zero]
  have hcancel :
      Complex.exp (-Complex.I * z * (t : ℂ)) *
          Complex.exp (Complex.I * z * (t : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    rw [show -Complex.I * z * (t : ℂ) +
        Complex.I * z * (t : ℂ) = 0 by ring,
      Complex.exp_zero]
  field_simp [hz]
  ring_nf at hcancel ⊢
  rw [hcancel]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hIcube : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]
    ring
  rw [hIcube]
  ring_nf
  rw [Complex.real_smul]
  ring

/-- Away from zero spectral frequency, Suzuki's transform is the published
exponential-difference coefficient divided by the Cauchy gap. -/
theorem integral_suzukiWeilFourierIntegrand_of_ne_zero
    {t : ℝ} (ht : 0 ≤ t) {z gamma : ℂ} (hz : z ≠ 0)
    (hgamma : gamma ≠ 0) (hgap : gamma.im < z.im) :
    (∫ x : ℝ, suzukiWeilFourierIntegrand t z gamma x) =
      suzukiSpectralScrewCoefficient t gamma / (z - gamma) := by
  rw [integral_suzukiWeilFourierIntegrand_eq_middle_add_tail ht hgap]
  have hleft : -Complex.I * gamma ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hgamma
  have hright : Complex.I * (z - gamma) ≠ 0 := by
    apply mul_ne_zero Complex.I_ne_zero
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hzgamma : z - gamma ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  have hrightRe : (Complex.I * (z - gamma)).re < 0 := by
    rw [re_I_mul_sub]
    linarith
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub
      ((show Continuous (fun x : ℝ ↦
        Complex.exp ((-Complex.I * gamma) * (x : ℂ))) by
          fun_prop).intervalIntegrable 0 t)
      ((show Continuous (fun x : ℝ ↦
        Complex.exp ((Complex.I * (z - gamma)) * (x : ℂ))) by
          fun_prop).intervalIntegrable 0 t),
    integral_exp_mul_complex hleft,
    integral_exp_mul_complex hright,
    MeasureTheory.integral_const_mul,
    integral_exp_mul_complex_Ioi hrightRe t,
    suzukiSpectralScrewCoefficient_of_ne_zero t hgamma]
  unfold spectralScrewExponential
  have hcombine :
      Complex.exp ((Complex.I * (z - gamma)) * (t : ℂ)) *
          Complex.exp (-Complex.I * z * (t : ℂ)) =
        Complex.exp (-Complex.I * gamma * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hcombineScaled :
      (gamma * Complex.exp ((Complex.I * (z - gamma)) * (t : ℂ))) *
          Complex.exp (-Complex.I * z * (t : ℂ)) =
        gamma * Complex.exp (-Complex.I * gamma * (t : ℂ)) := by
    rw [mul_assoc, hcombine]
  field_simp [hz, hgamma, hzgamma]
  ring_nf at hcombineScaled ⊢
  simp only [Complex.ofReal_zero, mul_zero, add_zero] at ⊢
  rw [hcombineScaled]
  rw [Complex.I_sq]
  ring_nf
  simp only [Complex.exp_zero, one_mul]

/-- Complete transform identity, including Suzuki's removable frequency-zero
normalization. -/
theorem integral_suzukiWeilFourierIntegrand
    {t : ℝ} (ht : 0 ≤ t) {z gamma : ℂ} (hz : z ≠ 0)
    (hgap : gamma.im < z.im) :
    (∫ x : ℝ, suzukiWeilFourierIntegrand t z gamma x) =
      suzukiSpectralScrewCoefficient t gamma / (z - gamma) := by
  by_cases hgamma : gamma = 0
  · subst gamma
    exact integral_suzukiWeilFourierIntegrand_zero ht hz hgap
  · exact integral_suzukiWeilFourierIntegrand_of_ne_zero
      ht hz hgamma hgap

/-- Every genuine zeta zero lies strictly below a safe Suzuki evaluation
point, so the generic transform theorem applies without RH. -/
theorem integral_suzukiWeilFourierIntegrand_zetaZero
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane)
    (rho : NontrivialZetaZero) :
    (∫ x : ℝ,
      suzukiWeilFourierIntegrand t z
        (zetaSpectralCoordinate rho.1) x) =
      suzukiSpectralScrewCoefficient t
          (zetaSpectralCoordinate rho.1) /
        (z - zetaSpectralCoordinate rho.1) := by
  apply integral_suzukiWeilFourierIntegrand ht
    (ne_zero_of_mem_suzukiXiSafeUpperHalfPlane hz)
  have hstrip := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho
  change (1 / 2 : ℝ) < z.im at hz
  nlinarith [le_abs_self (zetaSpectralCoordinate rho.1).im]

/-- With analytic multiplicity included, one Suzuki test transform is exactly
one genuine-zero summand of the spectral `P_t` series. -/
theorem analyticMultiplicity_mul_integral_suzukiWeilFourierIntegrand
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane)
    (rho : NontrivialZetaZero) :
    (analyticZetaZeroMultiplicity rho : ℂ) *
        (∫ x : ℝ,
          suzukiWeilFourierIntegrand t z
            (zetaSpectralCoordinate rho.1) x) =
      zetaSuzukiSpectralPSummand t z rho := by
  rw [integral_suzukiWeilFourierIntegrand_zetaZero ht hz rho]
  unfold zetaSuzukiSpectralPSummand
    suzukiXiUpperEvaluationDenominator
  ring

/-- Summing the exact one-zero transform identity over a genuine symmetric
zero window recovers the previously constructed finite spectral `P_t`
window. -/
theorem sum_analyticMultiplicity_mul_integral_suzukiWeilFourierIntegrand
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) (T : ℝ) :
    (∑ rho ∈ spectralZetaZeroWindow T,
      (analyticZetaZeroMultiplicity rho : ℂ) *
        ∫ x : ℝ,
          suzukiWeilFourierIntegrand t z
            (zetaSpectralCoordinate rho.1) x) =
      suzukiXiSpectralPWindow t T z := by
  unfold suzukiXiSpectralPWindow
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [analyticMultiplicity_mul_integral_suzukiWeilFourierIntegrand
    ht hz rho]
  rfl

/-- The symmetric sums of Suzuki test transforms converge to the complete
spectral `P_t` at every safe point.  This packages the local transform
calculation in the exact limiting form needed by the future explicit-formula
argument. -/
theorem tendsto_sum_suzukiWeilFourierIntegrand
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : z ∈ suzukiXiSafeUpperHalfPlane) :
    Tendsto
      (fun T : ℝ ↦
        ∑ rho ∈ spectralZetaZeroWindow T,
          (analyticZetaZeroMultiplicity rho : ℂ) *
            ∫ x : ℝ,
              suzukiWeilFourierIntegrand t z
                (zetaSpectralCoordinate rho.1) x)
      atTop (nhds (riemannXiSuzukiSpectralP t z)) := by
  have hzHalf : (1 / 2 : ℝ) < z.im := hz
  apply (tendsto_suzukiXiSpectralPWindow t hzHalf).congr'
  filter_upwards with T
  exact
    (sum_analyticMultiplicity_mul_integral_suzukiWeilFourierIntegrand
      ht hz T).symm

end

end RiemannGaussian
