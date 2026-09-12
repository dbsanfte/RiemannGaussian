/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianPrimeAverage

/-!
# The complete phase family in the original Gaussian prime series

Every countable summable nonnegative coefficient family retains one common
positive Gaussian prime-power amplitude. The complex frequency kernel and
the two infinite sums are coupled before real projection. Nonnegative real
kernels consequently give a nonnegative actual arithmetic sum, with any
finite prime-power selection available as a stronger retained contribution.
No frequency support, optimizer or coefficient search is imposed.
-/

namespace RiemannGaussian.ZetaGaussianPhaseArithmetic
noncomputable section
open Complex
open ZetaGaussianPrimeAverage GaussianFermiZeroPair
open GaussianFermiPrimeComparison

/-- The common positive amplitude of every original Gaussian prime-power channel. -/
def amplitude (σ B : ℝ) (m : ℕ) : ℝ := zetaPhasePrimeWeight σ m * window B (Real.log m)

/-- Every actual Gaussian prime-power amplitude is nonnegative. -/
theorem amplitude_nonneg (σ B : ℝ) (m : ℕ) : 0 ≤ amplitude σ B m :=
  mul_nonneg (zetaPhasePrimeWeight_nonneg σ m) (Real.exp_pos _).le

/-- The original prime-power amplitudes are summable through the Euler boundary. -/
theorem summable_amplitude {σ B : ℝ} (hσ : 2 / 3 < σ) (hB : 0 < B) :
    Summable (amplitude σ B) := by
  change Summable (fun m => zetaPhasePrimeWeight σ m * window B (Real.log m))
  simpa only [norm_term] using (summable_term hσ le_rfl hB 0).norm

/-- Every actual complex prime term retains its complete phase and common amplitude. -/
theorem term_eq_phase (σ B t : ℝ) (m : ℕ) :
    term σ B t m = (amplitude σ B m : ℂ) * Complex.exp (-(I * ((t * Real.log m : ℝ) : ℂ))) := by
  rw [term, base_eq_phase]
  unfold amplitude
  push_cast
  ring

/-- The original constant channel is exactly the complete positive amplitude mass. -/
theorem ordinarySum_zero (σ B : ℝ) : ordinarySum σ B 0 = ∑' m, amplitude σ B m := by
  simp only [ordinarySum, ordinarySummand, zero_mul, Real.cos_zero, mul_one,
    amplitude, zetaPhasePrimeWeight]

/-- The full complex Gaussian channel is bounded by the original constant channel. -/
theorem norm_primeSum_le {σ B : ℝ} (hσ : 2 / 3 < σ) (hB : 0 < B) (t : ℝ) :
    ‖primeSum σ B t‖ ≤ ordinarySum σ B 0 := by
  simpa only [primeSum, norm_term, ordinarySum_zero, amplitude] using
    norm_tsum_le_tsum_norm (summable_term hσ le_rfl hB t).norm

/-- The signed real prime channel has the same uniform absolute bound. -/
theorem abs_ordinarySum_le {σ B : ℝ} (hσ : 2 / 3 < σ) (hB : 0 < B) (t : ℝ) :
    |ordinarySum σ B t| ≤ ordinarySum σ B 0 := by
  rw [← primeSum_re hσ le_rfl hB]
  exact (Complex.abs_re_le_norm _).trans (norm_primeSum_le hσ hB t)

/-- Every summable nonnegative phase family has a genuinely summable complex
Gaussian prime response, at arbitrary real frequencies. -/
theorem summable_complex_channels {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ B : ℝ} (hσ : 2 / 3 < σ) (hB : 0 < B) (t : ℝ) :
    Summable (fun n => (a n : ℂ) * primeSum σ B (ω n * t)) := by
  apply (hs.mul_right (ordinarySum σ B 0)).of_norm_bounded
  intro n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n)]
  exact mul_le_mul_of_nonneg_left (norm_primeSum_le hσ hB _) (ha n)

/-- The complete signed real phase response is summable without a frequency moment. -/
theorem summable_channels {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ B : ℝ} (hσ : 2 / 3 < σ) (hB : 0 < B) (t : ℝ) :
    Summable (fun n => a n * ordinarySum σ B (ω n * t)) := by
  simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    primeSum_re hσ le_rfl hB] using
      Complex.reCLM.summable (summable_complex_channels (ω := ω) ha hs hσ hB t)

/-- The entire complex phase kernel, before taking its cosine projection. -/
def complexKernel (a ω : ℕ → ℝ) (u : ℝ) : ℂ :=
  ∑' n, (a n : ℂ) * Complex.exp (-(I * ((ω n * u : ℝ) : ℂ)))

/-- The complex frequency series is absolutely summable at every real argument. -/
theorem summable_kernel {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (u : ℝ) :
    Summable (fun n => (a n : ℂ) * Complex.exp (-(I * ((ω n * u : ℝ) : ℂ)))) := by
  apply hs.of_norm_bounded
  intro n
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha n),
    Complex.norm_exp, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
    neg_zero, Real.exp_zero, mul_one, le_refl]

/-- The real projection of the full complex kernel is the existing arbitrary-frequency test. -/
theorem complexKernel_re {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (u : ℝ) :
    (complexKernel a ω u).re = zetaPhaseKernel a ω u := by
  rw [complexKernel, Complex.re_tsum (summable_kernel ha hs u)]
  simp only [zetaPhaseKernel, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_re, Complex.neg_re, Complex.neg_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, one_mul, zero_add,
    neg_zero, Real.exp_zero, Real.cos_neg]

/-- The complete complex Gaussian arithmetic identity retains both infinite
sums and the full frequency kernel, with joint absolute convergence proved. -/
theorem hasSum_complex_arithmetic {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ B : ℝ} (hσ : 2 / 3 < σ) (hB : 0 < B) (t : ℝ) :
    HasSum (fun m => (amplitude σ B m : ℂ) * complexKernel a ω (t * Real.log m))
      (∑' n, (a n : ℂ) * primeSum σ B (ω n * t)) := by
  let f (m n : ℕ) : ℂ := (a n : ℂ) * term σ B (ω n * t) m
  have hmajor := (summable_amplitude hσ hB).mul_of_nonneg hs (amplitude_nonneg σ B) ha
  have hdouble : Summable (Function.uncurry f) := by
    apply hmajor.of_norm_bounded
    intro p
    simp only [f, Function.uncurry, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (ha p.2), norm_term, amplitude]
    exact le_of_eq (mul_comm _ _)
  have he : (∑' m, ∑' n, f m n) = ∑' n, (a n : ℂ) * primeSum σ B (ω n * t) := by
    rw [← hdouble.tsum_comm]
    simp only [f, primeSum, tsum_mul_left]
  rw [← he]
  apply hdouble.prod.hasSum.congr_fun
  intro m
  rw [complexKernel, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [Function.uncurry, f, term_eq_phase, mul_assoc]
  ring

/-- The original ordinary Gaussian prime sum retains the full real phase
kernel after justified complex recombination. -/
theorem hasSum_arithmetic {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {σ B : ℝ} (hσ : 2 / 3 < σ) (hB : 0 < B) (t : ℝ) :
    HasSum (fun m => amplitude σ B m * zetaPhaseKernel a ω (t * Real.log m))
      (∑' n, a n * ordinarySum σ B (ω n * t)) := by
  have h := Complex.reCLM.hasSum (hasSum_complex_arithmetic (ω := ω) ha hs hσ hB t)
  simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    complexKernel_re ha hs, Complex.re_tsum (summable_complex_channels (ω := ω) ha hs hσ hB t),
    primeSum_re hσ le_rfl hB] using h

/-- Every admissible nonnegative phase kernel gives a nonnegative literal
Gaussian prime response, including countably infinite frequency support. -/
theorem channels_nonneg {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ u, 0 ≤ zetaPhaseKernel a ω u) {σ B : ℝ} (hσ : 2 / 3 < σ) (hB : 0 < B) (t : ℝ) :
    0 ≤ ∑' n, a n * ordinarySum σ B (ω n * t) := by
  rw [← (hasSum_arithmetic ha hs hσ hB t).tsum_eq]
  exact tsum_nonneg (fun m => mul_nonneg (amplitude_nonneg σ B m) (hp _))

/-- Any finite actual prime-power work is retained below the full coupled
Gaussian response, so positivity need not discard the available arithmetic. -/
theorem finite_prime_work_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ u, 0 ≤ zetaPhaseKernel a ω u) {σ B : ℝ} (hσ : 2 / 3 < σ) (hB : 0 < B)
    (t : ℝ) (S : Finset ℕ) :
    (∑ m ∈ S, amplitude σ B m * zetaPhaseKernel a ω (t * Real.log m)) ≤
      ∑' n, a n * ordinarySum σ B (ω n * t) := by
  rw [← (hasSum_arithmetic ha hs hσ hB t).tsum_eq]
  exact (hasSum_arithmetic ha hs hσ hB t).summable.sum_le_tsum S
    (fun m _ => mul_nonneg (amplitude_nonneg σ B m) (hp _))

/-- The negative nonconstant Gaussian prime response costs only the actual
constant channel, after all phases have been combined. -/
theorem negative_nonconstant_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (hω0 : ω 0 = 0)
    {σ B : ℝ} (hσ : 2 / 3 < σ) (hB : 0 < B) (t : ℝ) :
    -(∑' n, if n = 0 then 0 else a n * ordinarySum σ B (ω n * t)) ≤
      a 0 * ordinarySum σ B 0 := by
  have h := channels_nonneg ha hs hp hσ hB t
  rw [(summable_channels ha hs hσ hB t).tsum_eq_add_tsum_ite 0, hω0, zero_mul] at h
  linarith

end
end RiemannGaussian.ZetaGaussianPhaseArithmetic
