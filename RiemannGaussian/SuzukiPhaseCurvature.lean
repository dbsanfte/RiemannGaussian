/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhasePrimeRecurrence
import RiemannGaussian.SuzukiPositivityRH

/-!
# The signed bridge from prime phase work to the actual Suzuki signal

Multiplying the genuine Suzuki Laplace transform by the square of its
complex parameter recovers the arithmetic curvature response. Its real part
contains both the cosine channel and the mixed sine channel. The exact Euler
identity then places prime work and Suzuki curvature on opposite sides of
one common budget.

The countable-family identity needs only summable nonnegative coefficients;
no second frequency moment is needed because the complete real curvature
response is retained before estimating it. A finite-family integral identity
also identifies the corresponding signed test of the actual time signal.

In particular, the proved lower floor for prime work transports to an UPPER
bound for this curvature response. It does not supply the lower bound on
the original Suzuki signal required by the RH criterion. Every Laplace
integral here remains in its proved domain `Re z > 1/2`.
-/

open Complex Filter MeasureTheory Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The complete real curvature response of the literal Suzuki Laplace
transform, before separating its real and imaginary channels. -/
def suzukiPhaseCurvatureResponse (lambda v : ℝ) : ℝ :=
  ((((lambda : ℂ) + I * v) ^ 2) *
    suzukiChebyshevLogAverageComplexLaplaceTransform ((lambda : ℂ) + I * v)).re

/-- The real time test corresponding to the full squared complex
Laplace parameter; the mixed sine channel is retained. -/
def suzukiPhaseCurvatureKernel (lambda v t : ℝ) : ℝ :=
  (lambda ^ 2 - v ^ 2) * Real.cos (v * t) + 2 * lambda * v * Real.sin (v * t)

/-- The curvature response retains both parts of the complex transform.
Discarding the imaginary part would discard the displayed mixed term. -/
theorem suzukiPhaseCurvatureResponse_eq_mixed (lambda v : ℝ) :
    suzukiPhaseCurvatureResponse lambda v =
      (lambda ^ 2 - v ^ 2) *
        (suzukiChebyshevLogAverageComplexLaplaceTransform ((lambda : ℂ) + I * v)).re -
      2 * lambda * v *
        (suzukiChebyshevLogAverageComplexLaplaceTransform ((lambda : ℂ) + I * v)).im := by
  simp only [suzukiPhaseCurvatureResponse, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

/-- Exact signed curvature accounting for the actual zeta function. The
boundary polynomial, pole at one, and arithmetic term all retain their
original coefficients. -/
theorem suzukiPhaseCurvature_prime_identity {lambda : ℝ} (hlambda : 1 / 2 < lambda) (v : ℝ) :
    suzukiPhaseCurvatureResponse lambda v +
      (-logDeriv riemannZeta (((lambda + 1 / 2 : ℝ) : ℂ) + I * v)).re =
      4 * lambda + 2 + (lambda - 1 / 2) / ((lambda - 1 / 2) ^ 2 + v ^ 2) := by
  let z : ℂ := (lambda : ℂ) + I * v
  have hz : z ∈ suzukiChebyshevLogAverageComplexLaplaceDomain := by
    simpa [suzukiChebyshevLogAverageComplexLaplaceDomain, z] using hlambda
  have hz0 : z ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [z] at hr
    linarith
  have hzh : z - 1 / 2 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [z] at hr
    linarith
  have hpole : z ^ 2 * (4 / (z - 1 / 2)) = 4 * z + 2 + 1 / (z - 1 / 2) := by
    calc
      _ = (z ^ 2 * 4) / (z - 1 / 2) := (mul_div_assoc _ _ _).symm
      _ = ((4 * z + 2) * (z - 1 / 2) + 1) / (z - 1 / 2) := by congr 1; ring
      _ = _ := by rw [add_div, mul_div_cancel_right₀ _ hzh]
  have he : z ^ 2 * suzukiChebyshevLogAverageComplexLaplaceTransform z +
      (-logDeriv riemannZeta (z + 1 / 2)) = 4 * z + 2 + 1 / (z - 1 / 2) := by
    rw [suzukiChebyshevLogAverageComplexLaplaceTransform_eq_zetaResponse hz]
    unfold suzukiChebyshevLogAverageComplexZetaResponse
    rw [mul_add, mul_div_cancel₀ _ (pow_ne_zero 2 hz0), hpole]
    ring
  have hshift : z + 1 / 2 = ((lambda + 1 / 2 : ℝ) : ℂ) + I * v := by
    dsimp [z]
    push_cast
    ring
  have hr := congrArg Complex.re he
  rw [hshift] at hr
  change suzukiPhaseCurvatureResponse lambda v +
      (-logDeriv riemannZeta (((lambda + 1 / 2 : ℝ) : ℂ) + I * v)).re = _ at hr
  simpa [z, Complex.div_re, Complex.normSq_apply, pow_two] using hr

/-- Countable curvature responses are genuinely summable even without
a second frequency moment. The signed Euler identity supplies the complete
real response's summable majorant. -/
theorem hasSum_suzukiPhase_curvature {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) {lambda : ℝ} (hlambda : 1 / 2 < lambda) (y : ℝ) :
    HasSum (fun n : ℕ ↦ a n * suzukiPhaseCurvatureResponse lambda (ω n * y))
      ((4 * lambda + 2) * (∑' n : ℕ, a n) +
        (∑' n : ℕ, a n * ((lambda - 1 / 2) / ((lambda - 1 / 2) ^ 2 + (ω n * y) ^ 2))) -
        ∑' n : ℕ, a n *
          (-logDeriv riemannZeta (((lambda + 1 / 2 : ℝ) : ℂ) + I * ((ω n * y : ℝ) : ℂ))).re) := by
  have hP := summable_zetaPhase_exactPole (ω := ω) ha hs (by linarith : 0 < lambda - 1 / 2) y
  have hD := summable_zetaPhase_logDeriv (ω := ω) ha hs (by linarith : 1 < lambda + 1 / 2) y
  have h := ((hs.hasSum.mul_left (4 * lambda + 2)).add hP.hasSum).sub hD.hasSum
  apply h.congr_fun
  intro n
  have he := suzukiPhaseCurvature_prime_identity hlambda (ω n * y)
  linear_combination (a n) * he

/-- The complete prime work and the complete curvature response sum to
one exact boundary-and-pole budget. Both infinite series converge. -/
theorem suzukiPhase_curvature_add_primeWork {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) {lambda : ℝ} (hlambda : 1 / 2 < lambda) (y : ℝ) :
    (∑' n : ℕ, a n * suzukiPhaseCurvatureResponse lambda (ω n * y)) +
      (∑' m : ℕ, zetaPhasePrimeWeight (lambda + 1 / 2) m * zetaPhaseKernel a ω (y * Real.log m)) =
      (4 * lambda + 2) * (∑' n : ℕ, a n) +
        ∑' n : ℕ, a n * ((lambda - 1 / 2) / ((lambda - 1 / 2) ^ 2 + (ω n * y) ^ 2)) := by
  rw [(hasSum_suzukiPhase_curvature (ω := ω) ha hs hlambda y).tsum_eq,
    (hasSum_zetaPhase_arithmetic (ω := ω) ha hs (by linarith : 1 < lambda + 1 / 2) y).tsum_eq]
  ring

/-- Nonnegative prime work gives an upper bound for the actual Suzuki
curvature response. This direction is not a lower bound for the time signal. -/
theorem suzukiPhase_curvature_le_budget {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable a) (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    {lambda : ℝ} (hlambda : 1 / 2 < lambda) (y : ℝ) :
    (∑' n : ℕ, a n * suzukiPhaseCurvatureResponse lambda (ω n * y)) ≤
      (4 * lambda + 2) * (∑' n : ℕ, a n) +
        ∑' n : ℕ, a n * ((lambda - 1 / 2) / ((lambda - 1 / 2) ^ 2 + (ω n * y) ^ 2)) := by
  have he := suzukiPhase_curvature_add_primeWork (ω := ω) ha hs hlambda y
  have hp : 0 ≤ ∑' m : ℕ, zetaPhasePrimeWeight (lambda + 1 / 2) m *
      zetaPhaseKernel a ω (y * Real.log m) :=
    tsum_nonneg fun m ↦ mul_nonneg (zetaPhasePrimeWeight_nonneg _ m) (hP _)
  linarith

/-- The independent prime-power floor makes the curvature upper bound
strictly smaller when its coefficient-mass factor is positive. The sign is
fixed by the literal Suzuki transform, rather than inferred from positivity
of an unrelated phase matrix. -/
theorem suzukiPhase_curvature_primePower_bound {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hP : ∀ t, 0 ≤ zetaPhaseKernel a ω t)
    (r : ℕ) (hr : ω r = 0) {lambda : ℝ} (hlambda : 1 / 2 < lambda)
    {p : ℕ} (hp : p.Prime) (N : ℕ) (y : ℝ) :
    (N : ℝ) * (∑' n : ℕ, a n * suzukiPhaseCurvatureResponse lambda (ω n * y)) +
      zetaPhasePrimeBlockWeight (lambda + 1 / 2) p N *
        (((N : ℝ) + 1) * a r - (∑' n : ℕ, a n)) ≤
      (N : ℝ) * ((4 * lambda + 2) * (∑' n : ℕ, a n) +
        ∑' n : ℕ, a n * ((lambda - 1 / 2) / ((lambda - 1 / 2) ^ 2 + (ω n * y) ^ 2))) := by
  have he := (hasSum_suzukiPhase_curvature (ω := ω) ha hs hlambda y).tsum_eq
  have hfloor := zetaPhase_primePower_floor ha hs hP r hr
    (by linarith : 1 < lambda + 1 / 2) hp N y
  rw [he]
  nlinarith only [hfloor]

/-- Pointwise real-time representation of the whole squared-parameter
integrand, including its sine channel. -/
theorem suzukiPhaseCurvature_integrand_re (lambda v t : ℝ) :
    ((((lambda : ℂ) + I * v) ^ 2) *
      ((suzukiChebyshevLogAverageLaplaceSignal t : ℂ) *
        Complex.exp (-((lambda : ℂ) + I * v) * (t : ℂ)))).re =
      suzukiChebyshevLogAverageLaplaceSignal t * Real.exp (-lambda * t) *
        suzukiPhaseCurvatureKernel lambda v t := by
  simp only [suzukiPhaseCurvatureKernel, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.exp_re, Complex.exp_im]
  simp only [mul_zero, zero_mul, one_mul, add_zero, zero_add, sub_zero,
    neg_mul, Real.cos_neg, Real.sin_neg]
  ring

private theorem integrableOn_squared_phase {lambda : ℝ} (hlambda : 1 / 2 < lambda) (v : ℝ) :
    IntegrableOn (fun t : ℝ ↦ (((lambda : ℂ) + I * v) ^ 2) *
      ((suzukiChebyshevLogAverageLaplaceSignal t : ℂ) *
        Complex.exp (-((lambda : ℂ) + I * v) * (t : ℂ)))) (Ioi 0) := by
  have hz : ((lambda : ℂ) + I * v) ∈ suzukiChebyshevLogAverageComplexLaplaceDomain := by
    simpa [suzukiChebyshevLogAverageComplexLaplaceDomain] using hlambda
  have hi := integrable_suzukiChebyshevLogAverageComplexLaplaceIntegrand hz
  unfold suzukiChebyshevLogAverageComplexLaplaceIntegrand at hi
  exact ((integrable_indicator_iff measurableSet_Ioi).mp hi).const_mul _

/-- The actual signed time test is genuinely integrable at every proved
Laplace damping. -/
theorem integrableOn_suzukiPhase_curvature {lambda : ℝ} (hlambda : 1 / 2 < lambda) (v : ℝ) :
    IntegrableOn (fun t : ℝ ↦ suzukiChebyshevLogAverageLaplaceSignal t *
      Real.exp (-lambda * t) * suzukiPhaseCurvatureKernel lambda v t) (Ioi 0) := by
  exact ((integrableOn_squared_phase hlambda v).re).congr
    (Eventually.of_forall fun t ↦ suzukiPhaseCurvature_integrand_re lambda v t)

/-- The curvature response is an integral of the literal signed Suzuki
signal against its complete real phase test. -/
theorem suzukiPhaseCurvatureResponse_eq_integral {lambda : ℝ} (hlambda : 1 / 2 < lambda) (v : ℝ) :
    suzukiPhaseCurvatureResponse lambda v =
      ∫ t in Ioi (0 : ℝ), suzukiChebyshevLogAverageLaplaceSignal t *
        Real.exp (-lambda * t) * suzukiPhaseCurvatureKernel lambda v t := by
  unfold suzukiPhaseCurvatureResponse suzukiChebyshevLogAverageComplexLaplaceTransform
    suzukiChebyshevLogAverageComplexLaplaceIntegrand
  rw [integral_indicator measurableSet_Ioi, ← integral_const_mul]
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        ((((lambda : ℂ) + I * v) ^ 2) *
          ((suzukiChebyshevLogAverageLaplaceSignal t : ℂ) *
            Complex.exp (-((lambda : ℂ) + I * v) * (t : ℂ)))).re :=
      (integral_re (integrableOn_squared_phase hlambda v)).symm
    _ = _ := integral_congr_ae
      (Eventually.of_forall fun t ↦ suzukiPhaseCurvature_integrand_re lambda v t)

/-- Finite superpositions retain the entire real test inside one integral
of the original signed signal. Test coefficients may have either sign. -/
theorem sum_suzukiPhaseCurvatureResponse_eq_integral {ι : Type*} [Fintype ι]
    (a v : ι → ℝ) {lambda : ℝ} (hlambda : 1 / 2 < lambda) :
    (∑ i, a i * suzukiPhaseCurvatureResponse lambda (v i)) =
      ∫ t in Ioi (0 : ℝ), suzukiChebyshevLogAverageLaplaceSignal t *
        Real.exp (-lambda * t) * (∑ i, a i * suzukiPhaseCurvatureKernel lambda (v i) t) := by
  simp_rw [suzukiPhaseCurvatureResponse_eq_integral hlambda, ← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ ↦ (integrableOn_suzukiPhase_curvature hlambda (v i)).const_mul (a i))]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A positive phase polynomial can induce a negative curvature test.
For `1 + cos(2*lambda*t)`, its complete curvature test at zero is negative.
Thus positivity of the phase polynomial cannot be transferred to this
time test by discarding the squared-parameter operation. -/
theorem suzukiPhaseCurvature_positive_phase_negative_test {lambda : ℝ} (hlambda : 0 < lambda) :
    (∀ t : ℝ, 0 ≤ 1 + Real.cos (2 * lambda * t)) ∧
      suzukiPhaseCurvatureKernel lambda 0 0 + suzukiPhaseCurvatureKernel lambda (2 * lambda) 0 < 0 := by
  constructor
  · intro t
    linarith [Real.neg_one_le_cos (2 * lambda * t)]
  · simp only [suzukiPhaseCurvatureKernel, mul_zero, Real.cos_zero, Real.sin_zero,
      mul_one, add_zero, zero_pow (by norm_num : 2 ≠ 0), sub_zero]
    nlinarith [sq_pos_of_pos hlambda]

end

end RiemannGaussian
