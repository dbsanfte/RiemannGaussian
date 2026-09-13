/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianPrimeReduction
import RiemannGaussian.ZetaEulerBoundaryControl
import RiemannGaussian.ZetaGaussianAllHeight

/-!
# An independent bound for the complete ordinary Gaussian-prime energy

The full complex Gaussian identity retains the Euler pole and regular response
before projection. The already proved signed Euler-boundary dominator gives a
logarithmic-height cap; the positive Euler mass gives a linear-dilation cap.
Together they bound the complete squared cosine energy using only the existing
first logarithmic frequency moment, uniformly over all eligible families.

Complete prime-prefix convergence transports the original squared zero source
to this independently bounded energy and cancels its constant channel exactly.
The normalized energy tends to zero when logarithmic height is negligible
relative to dilation. The current region's dilation does not satisfy that
condition beyond its plateau. The constants are not numerically enclosed;
no new zero-free region or RH contradiction is proved here.
-/

namespace RiemannGaussian.ZetaGaussianPrimeEnergyBound
noncomputable section
open Complex Filter MeasureTheory
open GaussianVerticalAverage ZetaGaussianScaledBandBudget
open scoped Topology

/-- A vertical displacement costs at most its absolute size in the Euler logarithmic height. -/
theorem logHeight_sub_le (t y : ℝ) :
    zetaEulerLogHeight (t - y) ≤ zetaEulerLogHeight t + |y| := by
  have ha := abs_sub t y
  have h := Real.log_le_log (by positivity : 0 < |t - y| + 26)
    (show |t - y| + 26 ≤ (|t| + 26) * (1 + |y|) by
      nlinarith [abs_nonneg t, abs_nonneg y])
  rw [Real.log_mul (by positivity) (by positivity)] at h
  have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + |y|)
  unfold zetaEulerLogHeight
  linarith

/-- The complete complex Gaussian average after removal of the actual Euler pole. -/
def regularMean (B x t : ℝ) : ℂ :=
  average B (fun y => logDeriv riemannZeta₁ (((1 + x : ℝ) : ℂ) + I * (t - y)))

/-- The actual pole-removed response is integrable under the full Gaussian; the pole and Euler identities are used on their genuine domains. -/
theorem integrable_regularMean {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (t : ℝ) :
    Integrable (fun y : ℝ => (density B y : ℂ) *
      logDeriv riemannZeta₁ (((1 + x : ℝ) : ℂ) + I * (t - y))) := by
  have hp := GaussianComplexPoleAverage.integrable_pole hB
    (z := (x : ℂ) + I * t) (by simpa using hx)
  have he := ZetaGaussianPrimeAverage.integrable_neg_logDeriv (by linarith : 1 < 1 + x) hB t
  apply (hp.sub he).congr
  filter_upwards with y
  simp only [Pi.sub_apply]
  have hs : 1 < ((((1 + x : ℝ) : ℂ) + I * (t - y)) : ℂ).re := by simpa using hx
  rw [neg_logDeriv_riemannZeta_eq_pole_sub (by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith) (riemannZeta_ne_zero_of_one_le_re hs.le)]
  have hh : ((1 + x : ℝ) : ℂ) + I * (t - y) - 1 = (x : ℂ) + I * t - I * y := by
    push_cast
    ring
  simp only [hh, one_div]
  ring

/-- The complete complex Gaussian prime sum is exactly the smoothed pole minus the pole-removed Euler response, before a real projection or estimate. -/
theorem primeSum_eq_transform_sub_regularMean {B x : ℝ} (hB : 0 < B)
    (hx : 0 < x) (t : ℝ) :
    ZetaGaussianPrimeAverage.primeSum (1 + x) B t =
      GaussianComplexHalfMoments.transform B ((x : ℂ) + I * t) - regularMean B x t := by
  rw [← ZetaGaussianPrimeAverage.average_neg_logDeriv (by linarith : 1 < 1 + x) hB,
    ← GaussianComplexPoleAverage.average_pole hB (z := (x : ℂ) + I * t) (by simpa using hx),
    regularMean, ← average_sub B (GaussianComplexPoleAverage.integrable_pole hB
      (z := (x : ℂ) + I * t) (by simpa using hx)) (integrable_regularMean hB hx t)]
  congr 1
  funext y
  have hs : 1 < ((((1 + x : ℝ) : ℂ) + I * (t - y)) : ℂ).re := by simpa using hx
  rw [neg_logDeriv_riemannZeta_eq_pole_sub (by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith) (riemannZeta_ne_zero_of_one_le_re hs.le)]
  congr 1
  push_cast
  ring

/-- The signed Euler-boundary dominator passes through the actual Gaussian with its exact first absolute moment. -/
theorem abs_regularMean_re_le {C B x : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ σ : ℝ, 1 ≤ σ → σ ≤ 3 → ∀ t : ℝ,
      |(logDeriv riemannZeta₁ ((σ : ℂ) + I * t)).re| ≤ C * zetaEulerLogHeight t)
    (hB : 0 < B) (hx : 0 < x) (hx2 : x ≤ 2) (t : ℝ) :
    |(regularMean B x t).re| ≤
      C * (zetaEulerLogHeight t + 4 * B / GaussianPolynomialTransport.mass B) := by
  have hi := integrable_regularMean hB hx t
  have hm := ((integrable_density hB).mul_const (C * zetaEulerLogHeight t)).add
    ((ZetaGaussianCompletionAverage.integrable_density_abs hB).const_mul C)
  rw [regularMean, average_re hi]
  calc
    _ ≤ ∫ y : ℝ, |density B y *
        (logDeriv riemannZeta₁ (((1 + x : ℝ) : ℂ) + I * (t - y))).re| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y : ℝ, density B y * (C * zetaEulerLogHeight t) + C * (density B y * |y|) := by
      apply integral_mono_ae (by
        simpa only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
          sub_zero, Real.norm_eq_abs] using hi.re.norm) hm
      filter_upwards with y
      rw [abs_mul, abs_of_pos (density_pos hB y)]
      have h := (hbound (1 + x) (by linarith) (by linarith) (t - y)).trans
        (mul_le_mul_of_nonneg_left (logHeight_sub_le t y) hC)
      simp only [Complex.ofReal_sub] at h
      dsimp only [Pi.add_apply]
      nlinarith only [mul_le_mul_of_nonneg_left h (density_pos hB y).le]
    _ = _ := by
      rw [integral_add ((integrable_density hB).mul_const _) ((ZetaGaussianCompletionAverage.integrable_density_abs hB).const_mul C),
        integral_mul_const, integral_const_mul, integral_density hB,
        ZetaGaussianCompletionAverage.integral_density_abs hB]
      ring

/-- The complete smoothed pole is uniformly bounded at nonzero heights in the current dilation family. -/
theorem norm_transform_le_thirteen {q t : ℝ} (hq : 1 ≤ q) (ht : 1 ≤ |t|) :
    ‖GaussianComplexHalfMoments.transform (gaussianScale q) ((shift q : ℂ) + I * t)‖ ≤ 13 := by
  have hB := (gaussianScale_bounds hq).1
  have hBs : gaussianScale q ≤ 1 := by
    have h := (gaussianScale_bounds hq).2
    norm_num [GaussianStripProfile.gaussianScale, GaussianStripProfile.width] at h
    linarith
  have hz : 1 ≤ ‖(shift q : ℂ) + I * t‖ :=
    ht.trans (by simpa using Complex.abs_im_le_norm ((shift q : ℂ) + I * t))
  have hn : (shift q : ℂ) + I * t ≠ 0 := norm_pos_iff.mp (by linarith)
  have hr := GaussianLaplacePoleRemainder.norm_remainder_le hB
    (z := (shift q : ℂ) + I * t) (by simpa using (shift_bounds hq).1.le) hn
  have h3 : 1 ≤ ‖(shift q : ℂ) + I * t‖ ^ 3 := one_le_pow₀ hz
  have hp : ‖(1 / ((shift q : ℂ) + I * t) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr hz
  have hr' : ‖GaussianLaplacePoleRemainder.remainder (gaussianScale q)
      ((shift q : ℂ) + I * t)‖ ≤ 12 := hr.trans (by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith)
  have he := norm_add_le (GaussianLaplacePoleRemainder.remainder (gaussianScale q)
    ((shift q : ℂ) + I * t)) (1 / ((shift q : ℂ) + I * t))
  simp only [GaussianLaplacePoleRemainder.remainder, sub_add_cancel] at he
  simp only [GaussianLaplacePoleRemainder.remainder] at hr'
  linarith

/-- The actual Gaussian von-Mangoldt response has a height-logarithmic absolute bound independent of dilation. The constant is finite but not numerically enclosed here. -/
theorem exists_gaussian_log_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ q t : ℝ, 1 ≤ q → 1 ≤ |t| →
      |GaussianFermiPrimeComparison.ordinarySum (1 + shift q) (gaussianScale q) t| ≤
        K * zetaEulerLogHeight t := by
  obtain ⟨C, hC, hbound⟩ := exists_re_logDeriv_riemannZeta₁_euler_bound
  refine ⟨13 + 2 * C, by positivity, ?_⟩
  intro q t hq ht
  have hx := (shift_bounds hq).1
  have hx2 : shift q ≤ 2 := by
    have h := (shift_bounds hq).2
    norm_num [GaussianStripProfile.shift, GaussianStripProfile.width] at h
    linarith
  have hr := abs_regularMean_re_le hC.le hbound (gaussianScale_bounds hq).1 hx hx2 t
  have hcomp := completion_le hq
  have hL := three_lt_zetaEulerLogHeight t
  rw [← ZetaGaussianPrimeAverage.primeSum_re (by linarith : 2 / 3 < 1 + shift q)
    le_rfl (gaussianScale_bounds hq).1,
    primeSum_eq_transform_sub_regularMean (gaussianScale_bounds hq).1 hx, Complex.sub_re]
  have h := abs_sub (GaussianComplexHalfMoments.transform (gaussianScale q)
    ((shift q : ℂ) + I * t)).re (regularMean (gaussianScale q) (shift q) t).re
  have hp := (Complex.abs_re_le_norm _).trans (norm_transform_le_thirteen hq ht)
  nlinarith

open ZetaGaussianPrimeReduction

/-- The complete ordinary Gaussian-prime cosine sum, with its original amplitudes and phases. -/
def primeCosine (q t : ℝ) : ℝ :=
  ∑' n : ℕ, primeAmplitude q n * Real.cos (t * Real.log n)

/-- The retained ordinary-prime amplitude is dominated by the actual positive Euler amplitude. -/
theorem primeAmplitude_le_euler {q : ℝ} (hq : 1 ≤ q) (n : ℕ) :
    primeAmplitude q n ≤ zetaPhasePrimeWeight (1 + shift q) n := by
  unfold primeAmplitude
  split_ifs
  · have hB := (gaussianScale_bounds hq).1
    have hw : GaussianFermiZeroPair.window (gaussianScale q) (Real.log n) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg (Real.log n)]
    exact (mul_le_mul_of_nonneg_left hw (zetaPhasePrimeWeight_nonneg _ n)).trans_eq (mul_one _)
  · exact zetaPhasePrimeWeight_nonneg _ n

/-- Every complete ordinary-prime cosine response converges absolutely at each allowed dilation. -/
theorem summable_primeCosine {q : ℝ} (hq : 1 ≤ q) (t : ℝ) :
    Summable (fun n : ℕ => primeAmplitude q n * Real.cos (t * Real.log n)) := by
  have hx := (shift_bounds hq).1
  apply (hasSum_zetaPhasePrimeWeight (by linarith : 1 < 1 + shift q)).summable.of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (primeAmplitude_nonneg q n)]
  exact ((mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (primeAmplitude_nonneg q n)).trans_eq
    (mul_one _)).trans (primeAmplitude_le_euler hq n)

/-- The actual Euler mass bounds the complete ordinary-prime response at every frequency. -/
theorem abs_primeCosine_le_euler {q : ℝ} (hq : 1 ≤ q) (t : ℝ) :
    |primeCosine q t| ≤ (-logDeriv riemannZeta ((1 + shift q : ℝ) : ℂ)).re := by
  have hx := (shift_bounds hq).1
  rw [primeCosine, ← Real.norm_eq_abs,
    ← (hasSum_zetaPhasePrimeWeight (by linarith : 1 < 1 + shift q)).tsum_eq]
  apply (norm_tsum_le_tsum_norm (summable_primeCosine hq t).norm).trans
  apply (summable_primeCosine hq t).norm.tsum_le_tsum _
    (hasSum_zetaPhasePrimeWeight (by linarith : 1 < 1 + shift q)).summable
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (primeAmplitude_nonneg q n)]
  exact ((mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (primeAmplitude_nonneg q n)).trans_eq
    (mul_one _)).trans (primeAmplitude_le_euler hq n)

/-- The exact proper-power difference is paid by the already bounded full remainder. -/
theorem gaussian_difference_le_remainder {q : ℝ} (hq : 1 ≤ q) (n : ℕ) :
    |primeAmplitude q n - ZetaGaussianPhaseArithmetic.amplitude
      (1 + shift q) (gaussianScale q) n| ≤ remainder q n := by
  have hG := ZetaGaussianPhaseArithmetic.amplitude_nonneg (1 + shift q) (gaussianScale q) n
  have hE := mul_nonneg (factor_bounds hq).1
    (zetaPhasePrimeWeight_nonneg (ZetaStripEulerConstraint.rightLine 9 (shift q)) n)
  have hS := div_nonneg (ZetaSechPrimeBoundary.amplitude_nonneg
    (ZetaStripEulerConstraint.rightLine 9 (shift q))
    (ZetaStripEulerConstraint.verticalScale 9 (shift q)) n)
    (show 0 ≤ 2 * ZetaStripEulerConstraint.halfWidth 9 (shift q) by
      have h := ZetaStripEulerConstraint.halfWidth_pos 9 (shift_bounds hq).1
      positivity)
  unfold primeAmplitude remainder
  split_ifs <;> simp only [sub_self, abs_zero, zero_sub, abs_neg, abs_of_nonneg hG] <;> linarith

/-- Removing proper powers from the complete Gaussian response costs at most the fixed proved remainder allowance. -/
theorem abs_primeCosine_sub_gaussian_le {q : ℝ} (hq : 1 ≤ q) (t : ℝ) :
    |primeCosine q t - GaussianFermiPrimeComparison.ordinarySum
      (1 + shift q) (gaussianScale q) t| ≤ allowance := by
  let G := ZetaGaussianPhaseArithmetic.amplitude (1 + shift q) (gaussianScale q)
  have hσ : 2 / 3 < 1 + shift q := by linarith [(shift_bounds hq).1]
  have hsG : Summable (fun n : ℕ => G n * Real.cos (t * Real.log n)) := by
    apply (ZetaGaussianPhaseArithmetic.summable_amplitude hσ
      (gaussianScale_bounds hq).1).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ZetaGaussianPhaseArithmetic.amplitude_nonneg _ _ n)]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
      (ZetaGaussianPhaseArithmetic.amplitude_nonneg _ _ n)).trans_eq (mul_one _)
  have he : GaussianFermiPrimeComparison.ordinarySum (1 + shift q) (gaussianScale q) t =
      ∑' n : ℕ, G n * Real.cos (t * Real.log n) := by
    apply tsum_congr
    intro n
    dsimp [G, GaussianFermiPrimeComparison.ordinarySummand,
      ZetaGaussianPhaseArithmetic.amplitude, zetaPhasePrimeWeight]
  rw [he, primeCosine, ← (summable_primeCosine hq t).tsum_sub hsG, ← Real.norm_eq_abs]
  apply (norm_tsum_le_tsum_norm ((summable_primeCosine hq t).sub hsG).norm).trans
  apply ((summable_primeCosine hq t).sub hsG).norm.tsum_le_tsum _ (summable_remainder hq) |>.trans (remainder_mass_le hq)
  intro n
  change ‖primeAmplitude q n * Real.cos (t * Real.log n) - G n * Real.cos (t * Real.log n)‖ ≤ _
  rw [← sub_mul, Real.norm_eq_abs, abs_mul]
  exact ((mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)).trans_eq
    (mul_one _)).trans (gaussian_difference_le_remainder hq n)

/-- One pair of positive constants gives both the linear-dilation and logarithmic-height bounds for the actual ordinary-prime sum. -/
theorem exists_prime_bounds :
    ∃ D K : ℝ, 0 < D ∧ 0 < K ∧ ∀ q t : ℝ, 1 ≤ q →
      |primeCosine q t| ≤ D * q ∧
        (1 ≤ |t| → |primeCosine q t| ≤ K * zetaEulerLogHeight t) := by
  obtain ⟨K, hK, hb⟩ := exists_gaussian_log_bound
  let D := 1 / GaussianStripProfile.shift + |448 * localZetaLogHeight 0| + 1
  have hx : 0 < GaussianStripProfile.shift := by
    norm_num [GaussianStripProfile.shift, GaussianStripProfile.width]
  refine ⟨D, K + allowance, by dsimp [D]; positivity, by linarith [allowance_nonneg], ?_⟩
  intro q t hq
  constructor
  · have hsmall : shift q ≤ 1 / 4 := by
      have h := (shift_bounds hq).2
      norm_num [GaussianStripProfile.shift, GaussianStripProfile.width] at h
      linarith
    have h := (abs_primeCosine_le_euler hq t).trans
      (neg_logDeriv_riemannZeta_real_le_local (shift_bounds hq).1 hsmall)
    have he : 1 / shift q = q / GaussianStripProfile.shift := by
      unfold shift
      field_simp
    rw [he] at h
    dsimp only [D]
    simp only [div_eq_mul_inv, one_mul] at h ⊢
    have hcost := mul_le_mul_of_nonneg_left hq (abs_nonneg (448 * localZetaLogHeight 0))
    nlinarith [le_abs_self (448 * localZetaLogHeight 0)]
  · intro ht
    have h := abs_primeCosine_sub_gaussian_le hq t
    have he := abs_add_le (primeCosine q t - GaussianFermiPrimeComparison.ordinarySum
      (1 + shift q) (gaussianScale q) t)
      (GaussianFermiPrimeComparison.ordinarySum (1 + shift q) (gaussianScale q) t)
    rw [sub_add_cancel] at he
    have hg := hb q t hq ht
    have hL := three_lt_zetaEulerLogHeight t
    nlinarith [allowance_nonneg]

open ZetaAngularPhaseAllowance

/-- The full nonconstant ordinary-prime real energy. Each complete cosine sum is squared before the countable coefficient sum. -/
def fullEnergy (a ω : ℕ → ℝ) (q t : ℝ) : ℝ :=
  ∑' n : ℕ, tail a n * (primeCosine q (ω n * t)) ^ 2

/-- A frequency at least one adds only its logarithm to the Euler height cost. -/
theorem logHeight_mul_le {ω : ℝ} (hω : 1 ≤ ω) (t : ℝ) :
    zetaEulerLogHeight (ω * t) ≤ zetaEulerLogHeight t + Real.log ω := by
  have hω0 : 0 < ω := by linarith
  unfold zetaEulerLogHeight
  rw [abs_mul, abs_of_pos hω0]
  have h := Real.log_le_log (by positivity : 0 < ω * |t| + 26)
    (show ω * |t| + 26 ≤ ω * (|t| + 26) by linarith)
  rw [Real.log_mul hω0.ne' (by positivity)] at h
  linarith

/-- A uniform cap and an additive height/frequency cap bound the square using only the first frequency cost. -/
theorem square_le_mixed_caps {z H J V : ℝ} (hJ : 0 ≤ J)
    (hV : 0 ≤ V) (hzV : |z| ≤ V) (hzHJ : |z| ≤ H + J) :
    z ^ 2 ≤ 4 * H ^ 2 + 2 * V * J := by
  by_cases h : |z| ≤ 2 * H
  · have hs := mul_self_le_mul_self (abs_nonneg z) h
    rw [← sq, sq_abs] at hs
    nlinarith [mul_nonneg hV hJ]
  · have hj : |z| ≤ 2 * J := by linarith
    have hs := mul_le_mul hzV hj (abs_nonneg z) hV
    rw [← sq, sq_abs] at hs
    nlinarith [sq_nonneg H]

/-- The complete nonconstant real energy is genuinely summable for every nonnegative summable family. -/
theorem summable_fullEnergy {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {q : ℝ} (hq : 1 ≤ q) (t : ℝ) :
    Summable (fun n => tail a n * (primeCosine q (ω n * t)) ^ 2) := by
  obtain ⟨D, K, hD, _, hb⟩ := exists_prime_bounds
  apply ((tail_summable ha hs).mul_right ((D * q) ^ 2)).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (tail_nonneg ha n) (sq_nonneg _))]
  apply mul_le_mul_of_nonneg_left _ (tail_nonneg ha n)
  have h := mul_self_le_mul_self (abs_nonneg (primeCosine q (ω n * t))) (hb q _ hq).1
  simpa only [← sq, sq_abs] using h

/-- The two actual response caps control every phase-family energy using its mass and first logarithmic frequency moment. -/
theorem fullEnergy_le {D K : ℝ} (hD : 0 < D) (hK : 0 < K)
    (hb : ∀ q t : ℝ, 1 ≤ q → |primeCosine q t| ≤ D * q ∧
      (1 ≤ |t| → |primeCosine q t| ≤ K * zetaEulerLogHeight t))
    {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    {q t : ℝ} (hq : 1 ≤ q) (ht : 1 ≤ |t|) :
    fullEnergy a ω q t ≤ 4 * K ^ 2 * mass a * (zetaEulerLogHeight t) ^ 2 +
      2 * D * K * q * frequencyCost a ω := by
  have hu (n : ℕ) : tail a n * (primeCosine q (ω n * t)) ^ 2 ≤
      tail a n * (4 * K ^ 2 * (zetaEulerLogHeight t) ^ 2) +
        (tail a n * Real.log (ω n)) * (2 * D * K * q) := by
    by_cases hn : n = 0
    · simp [tail, hn]
    have hω0 : 0 < ω n := by linarith [hω n hn]
    have ht' : 1 ≤ |ω n * t| := by
      rw [abs_mul, abs_of_pos hω0]
      nlinarith [hω n hn]
    have h := (hb q (ω n * t) hq).2 ht'
    have hlog' := mul_le_mul_of_nonneg_left (logHeight_mul_le (hω n hn) t) hK.le
    have he := square_le_mixed_caps
      (mul_nonneg hK.le (Real.log_nonneg (hω n hn)))
      (show 0 ≤ D * q by positivity) (hb q (ω n * t) hq).1
      (show |primeCosine q (ω n * t)| ≤ K * zetaEulerLogHeight t + K * Real.log (ω n) by linarith)
    nlinarith only [mul_le_mul_of_nonneg_left he (tail_nonneg ha n)]
  have h := (summable_fullEnergy ha hs hq t).tsum_le_tsum hu
    (((tail_summable ha hs).mul_right _).add (hlog.mul_right _))
  have he := ((tail_summable ha hs).hasSum.mul_right (4 * K ^ 2 * (zetaEulerLogHeight t) ^ 2)).add
    (hlog.hasSum.mul_right (2 * D * K * q))
  have hh := h.trans_eq he.tsum_eq
  change fullEnergy a ω q t ≤ mass a * (4 * K ^ 2 * (zetaEulerLogHeight t) ^ 2) +
    frequencyCost a ω * (2 * D * K * q) at hh
  nlinarith only [hh]

/-- An independent upper bound for the complete ordinary-prime energy, with all arithmetic response premises discharged and constants uniform in the family, height and dilation. -/
theorem exists_fullEnergy_bound :
    ∃ D K : ℝ, 0 < D ∧ 0 < K ∧ ∀ (a ω : ℕ → ℝ),
      (∀ n, 0 ≤ a n) → Summable a → (∀ n, n ≠ 0 → 1 ≤ ω n) →
      Summable (fun n => tail a n * Real.log (ω n)) → ∀ q t : ℝ,
      1 ≤ q → 1 ≤ |t| → fullEnergy a ω q t ≤
        4 * K ^ 2 * mass a * (zetaEulerLogHeight t) ^ 2 +
          2 * D * K * q * frequencyCost a ω := by
  obtain ⟨D, K, hD, hK, hb⟩ := exists_prime_bounds
  exact ⟨D, K, hD, hK, fun _ _ ha hs hω hlog _ _ hq ht => fullEnergy_le hD hK hb ha hs hω hlog hq ht⟩

/-- The actual energy divided by squared dilation tends to zero for moving families of bounded mass and logarithmic frequency cost, provided logarithmic height divided by dilation tends to zero. -/
theorem tendsto_normalized_fullEnergy
    (a ω : ℕ → ℕ → ℝ) (q t : ℕ → ℝ)
    (ha : ∀ N n, 0 ≤ a N n) (hs : ∀ N, Summable (a N))
    (hω : ∀ N n, n ≠ 0 → 1 ≤ ω N n)
    (hlog : ∀ N, Summable (fun n => tail (a N) n * Real.log (ω N n)))
    (hq : ∀ N, 1 ≤ q N) (ht : ∀ N, 1 ≤ |t N|)
    (hqt : Tendsto q atTop atTop)
    (hheight : Tendsto (fun N => zetaEulerLogHeight (t N) / q N) atTop (𝓝 0))
    (A F : ℝ) (hA : ∀ N, mass (a N) ≤ A) (hF : ∀ N, frequencyCost (a N) (ω N) ≤ F) :
    Tendsto (fun N => fullEnergy (a N) (ω N) (q N) (t N) / (q N) ^ 2) atTop (𝓝 0) := by
  obtain ⟨D, K, hD, hK, hb⟩ := exists_fullEnergy_bound
  have hlim : Tendsto (fun N => 4 * K ^ 2 * A * (zetaEulerLogHeight (t N) / q N) ^ 2 +
      2 * D * K * F / q N) atTop (𝓝 0) := by
    have h1 := (hheight.pow 2).const_mul (4 * K ^ 2 * A)
    have h2 := (tendsto_inv_atTop_zero.comp hqt).const_mul (2 * D * K * F)
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero,
      div_eq_mul_inv, Function.comp_apply] using h1.add h2
  apply squeeze_zero _ _ hlim
  · intro N
    exact div_nonneg (tsum_nonneg (fun n => mul_nonneg (tail_nonneg (ha N) n) (sq_nonneg _)))
      (sq_nonneg _)
  · intro N
    have hq0 : 0 < q N := by linarith [hq N]
    have h := hb (a N) (ω N) (ha N) (hs N) (hω N) (hlog N) (q N) (t N) (hq N) (ht N)
    have hm := mul_le_mul_of_nonneg_right (hA N) (sq_nonneg (zetaEulerLogHeight (t N)))
    have hcost := mul_le_mul_of_nonneg_left (hF N)
      (show 0 ≤ 2 * D * K * q N by positivity)
    have hu : fullEnergy (a N) (ω N) (q N) (t N) ≤
        4 * K ^ 2 * A * (zetaEulerLogHeight (t N)) ^ 2 + 2 * D * K * q N * F := by
      nlinarith only [h, mul_le_mul_of_nonneg_left hm (show 0 ≤ 4 * K ^ 2 by positivity), hcost]
    calc
      _ ≤ (4 * K ^ 2 * A * (zetaEulerLogHeight (t N)) ^ 2 + 2 * D * K * q N * F) / (q N) ^ 2 :=
        div_le_div_of_nonneg_right hu (sq_nonneg _)
      _ = _ := by field_simp

/-- Complete prime prefixes converge to the full real energy. The product phases, ratio phases and diagonal in the finite Schur energy are retained in this limit. -/
theorem tendsto_range_energy {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {q : ℝ} (hq : 1 ≤ q) (t : ℝ) :
    Tendsto (fun N => ZetaGaussianPrimeCorrelation.realPrimeEnergy (tail a) ω
      (primeAmplitude q) t (Finset.range N)) atTop (𝓝 (fullEnergy a ω q t)) := by
  obtain ⟨D, K, _, _, hb⟩ := exists_prime_bounds
  have hsP : Summable (primeAmplitude q) := by
    simpa only [zero_mul, Real.cos_zero, mul_one] using summable_primeCosine hq 0
  have hfin (N : ℕ) (v : ℝ) :
      |∑ p ∈ Finset.range N, primeAmplitude q p * Real.cos (v * Real.log p)| ≤ D * q := by
    calc
      _ ≤ ∑ p ∈ Finset.range N, |primeAmplitude q p * Real.cos (v * Real.log p)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ Finset.range N, primeAmplitude q p := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul, abs_of_nonneg (primeAmplitude_nonneg q p)]
        exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (primeAmplitude_nonneg q p)).trans_eq (mul_one _)
      _ ≤ ∑' p, primeAmplitude q p := hsP.sum_le_tsum _ (fun p _ => primeAmplitude_nonneg q p)
      _ = primeCosine q 0 := by simp [primeCosine]
      _ ≤ D * q := (le_abs_self _).trans (hb q 0 hq).1
  have hp (n : ℕ) : Tendsto
      (fun N => tail a n * (∑ p ∈ Finset.range N,
        primeAmplitude q p * Real.cos ((ω n * t) * Real.log p)) ^ 2)
      atTop (𝓝 (tail a n * (primeCosine q (ω n * t)) ^ 2)) :=
    ((summable_primeCosine hq (ω n * t)).hasSum.tendsto_sum_nat.pow 2).const_mul _
  have hd : ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      ‖tail a n * (∑ p ∈ Finset.range N,
        primeAmplitude q p * Real.cos ((ω n * t) * Real.log p)) ^ 2‖ ≤ tail a n * (D * q) ^ 2 := by
    apply Eventually.of_forall
    intro N n
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (tail_nonneg ha n) (sq_nonneg _))]
    apply mul_le_mul_of_nonneg_left _ (tail_nonneg ha n)
    have h := mul_self_le_mul_self (abs_nonneg _) (hfin N (ω n * t))
    simpa only [← sq, sq_abs] using h
  have h := tendsto_tsum_of_dominated_convergence ((tail_summable ha hs).mul_right ((D * q) ^ 2)) hp hd
  apply h.congr'
  apply Eventually.of_forall
  intro N
  simpa only [mul_assoc] using
    (ZetaGaussianPrimeCorrelation.hasSum_realPrimeEnergy (tail_nonneg ha)
      (tail_summable ha hs) (primeAmplitude q) t (Finset.range N)).tsum_eq

open ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint

/-- The original exact signed budget with its constant-channel mass subtracted algebraically. All boundary, pole and completion terms remain. -/
def signedBudget (q M t : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  exactBudget 9 (gaussianScale q) M (shift q) t a ω -
    a 0 * constantWork 9 (gaussianScale q) (shift q)

/-- The actual finite-zero source reaches the complete ordinary-prime energy. Passing the full prime prefixes to the limit cancels the original constant channel exactly. -/
theorem finite_source_le_fullEnergy {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hP : ∀ u, 0 ≤ zetaPhaseKernel a ω u)
    (hω0 : ω 0 = 0) (hω1 : ω 1 = 1) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    {q M : ℝ} (hq : 1 ≤ q) (hM : 0 ≤ M)
    (t : ℝ) (Z : Finset NontrivialZetaZero) (hscale : 1 ≤ ZetaNearOneBudgetLimit.scale t) :
    (max 0 ((a 1 * ∑ ρ ∈ Z, ZetaGaussianNearCancellation.compensated (gaussianScale q)
      (halfWidth 9 (shift q)) (ZetaNearOneLocalDisc.center (shift q) t) ρ) -
        signedBudget q M t a ω)) ^ 2 ≤
      (1 + 1 / q) * mass a * fullEnergy a ω q t + energyAllowance q (mass a) := by
  let F := a 1 * ∑ ρ ∈ Z, ZetaGaussianNearCancellation.compensated (gaussianScale q)
    (halfWidth 9 (shift q)) (ZetaNearOneLocalDisc.center (shift q) t) ρ
  let b := exactBudget 9 (gaussianScale q) M (shift q) t a ω
  have hm : Tendsto (fun N => ∑ p ∈ Finset.range N,
      ZetaGaussianPrimeBlocks.amplitude 9 (gaussianScale q) (shift q) p) atTop
      (𝓝 (constantWork 9 (gaussianScale q) (shift q))) := by
    rw [ZetaGaussianPrimeBlocks.constantWork_eq_sum 9 (gaussianScale_bounds hq).1 (shift_bounds hq).1]
    exact (ZetaGaussianPrimeBlocks.summable_amplitude 9 (gaussianScale_bounds hq).1
      (shift_bounds hq).1).hasSum.tendsto_sum_nat
  have hl := ((tendsto_const_nhds (x := (0 : ℝ))).max
    (((hm.const_mul (a 0)).add_const F).sub_const b)).pow 2
  have hr := ((tendsto_range_energy (ω := ω) ha hs hq t).const_mul ((1 + 1 / q) * mass a)).add_const
    (energyAllowance q (mass a))
  have h := le_of_tendsto_of_tendsto' hl hr (fun N =>
    finite_source_le_prime_energy_scaled ha hs hP hω0 hω1 hω hlog hq hM t Z hscale (Finset.range N))
  have he : a 0 * constantWork 9 (gaussianScale q) (shift q) + F - b =
      F - signedBudget q M t a ω := by unfold b signedBudget; ring
  rwa [he] at h

/-- The actual squared finite-zero surplus obeys the independently proved logarithmic energy bound, with the full auxiliary allowance and signed boundary budget retained. -/
theorem exists_source_growth_bound :
    ∃ D K : ℝ, 0 < D ∧ 0 < K ∧ ∀ (a ω : ℕ → ℝ),
      (∀ n, 0 ≤ a n) → Summable a → (∀ u, 0 ≤ zetaPhaseKernel a ω u) →
      ω 0 = 0 → ω 1 = 1 → (∀ n, n ≠ 0 → 1 ≤ ω n) →
      Summable (fun n => tail a n * Real.log (ω n)) → ∀ q M t : ℝ,
      1 ≤ q → 0 ≤ M → 1 ≤ |t| → ∀ Z : Finset NontrivialZetaZero,
      1 ≤ ZetaNearOneBudgetLimit.scale t →
      (max 0 ((a 1 * ∑ ρ ∈ Z, ZetaGaussianNearCancellation.compensated (gaussianScale q)
        (halfWidth 9 (shift q)) (ZetaNearOneLocalDisc.center (shift q) t) ρ) -
          signedBudget q M t a ω)) ^ 2 ≤
        (1 + 1 / q) * mass a *
          (4 * K ^ 2 * mass a * (zetaEulerLogHeight t) ^ 2 + 2 * D * K * q * frequencyCost a ω) +
            energyAllowance q (mass a) := by
  obtain ⟨D, K, hD, hK, hb⟩ := exists_fullEnergy_bound
  refine ⟨D, K, hD, hK, ?_⟩
  intro a ω ha hs hP hω0 hω1 hω hlog q M t hq hM ht Z hscale
  have h := finite_source_le_fullEnergy ha hs hP hω0 hω1 hω hlog hq hM t Z hscale
  have he := hb a ω ha hs hω hlog q t hq ht
  have hm : 0 ≤ mass a := tsum_nonneg (tail_nonneg ha)
  have hq0 : 0 < q := by linarith
  have hh := mul_le_mul_of_nonneg_left he
    (show 0 ≤ (1 + 1 / q) * mass a by positivity)
  exact h.trans (by nlinarith only [hh])

/-- Beyond the plateau, the current explicit-region dilation has height ratio at least 320000. It therefore does not supply the vanishing height-ratio premise of the energy limit. -/
theorem current_dilation_height_ratio_lower {t : ℝ}
    (ht : 320000 ≤ ZetaNearOneBudgetLimit.scale t) :
    320000 ≤ zetaEulerLogHeight t / ZetaGaussianAllHeight.dilation t := by
  have hq : 1 ≤ ZetaNearOneBudgetLimit.scale t / 320000 := by linarith
  have hL : 0 < ZetaNearOneBudgetLimit.scale t := by linarith
  rw [ZetaGaussianAllHeight.dilation, max_eq_right hq]
  apply (le_div_iff₀ (by positivity)).mpr
  have h : ZetaNearOneBudgetLimit.scale t ≤ zetaEulerLogHeight t := by
    unfold ZetaNearOneBudgetLimit.scale ZetaNearOneLogProfile.height zetaEulerLogHeight
    exact Real.log_le_log (by positivity) (by linarith)
  nlinarith only [h]

end
end RiemannGaussian.ZetaGaussianPrimeEnergyBound
