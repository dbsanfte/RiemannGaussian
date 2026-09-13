/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianPrimeEnergyDecay

/-!
# The signed left mean is the remaining Gaussian source-scale budget

The exact source budget is split into the original signed clipped left mean
and its full rational, Gaussian pole/completion and right-response corrections.
The actual right-response multiplier retains inverse-square dilation decay;
its growing completion term is not treated as a bounded Euler prime sum.

A two-sided quantitative bound proves that the difference from the left mean
vanishes after source-scale normalization when logarithmic height divided by
dilation is bounded. This applies to the current dilation and arbitrary moving
eligible countable families and clipping depths. The actual finite-zero source
surplus over the left mean inherits the normalized squared zero limit.
The left mean itself is not bounded sufficiently to contradict an interior
zero here. No new zero-free region or RH proof is claimed.
-/

namespace RiemannGaussian.ZetaGaussianSignedBudgetReduction
noncomputable section
open Complex Filter
open ZetaGaussianScaledBandBudget ZetaGaussianStripPhaseFamily ZetaStripEulerConstraint
open ZetaGaussianPrimeEnergyBound ZetaGaussianPrimeEnergyDecay ZetaAngularPhaseAllowance
open ZetaGaussianPhaseAllowance
open scoped Topology

/-- The original signed clipped left boundary mean with its exact strip half-width normalization. -/
def leftBudget (q M t : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  ZetaClippedEulerFamily.totalMean 9 M t (verticalScale 9 (shift q)) a ω /
    (2 * halfWidth 9 (shift q))

/-- All original non-left budget terms, keeping the rational mass, complex Gaussian correction and full right response separate. -/
def correction (q t : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  ZetaRegularizedSechMean.rationalTotal (rightLine 9 (shift q)) t
      (verticalScale 9 (shift q)) a ω / (2 * halfWidth 9 (shift q)) +
    extraTotal (gaussianScale q) (shift q) t a ω +
    factor 9 (gaussianScale q) (shift q) *
      ∑' n, tail a n * rightResponse (rightLine 9 (shift q)) (ω n * t)

/-- Exact decomposition of the actual signed source budget; the complete correction is independent of clipping depth. -/
theorem signedBudget_eq_left_add (q M t : ℝ) (a ω : ℕ → ℝ) :
    signedBudget q M t a ω = leftBudget q M t a ω + correction q t a ω := by
  unfold signedBudget exactBudget leftBudget correction
  ring

/-- The original multiplier retains its exact inverse-square dilation factor before the half-width is bounded. -/
theorem factor_mul_sq_eq {q : ℝ} (hq : q ≠ 0) :
    factor 9 (gaussianScale q) (shift q) * q ^ 2 =
      24 * GaussianStripProfile.gaussianScale / (halfWidth 9 (shift q)) ^ 2 := by
  unfold factor gaussianScale
  field_simp

/-- The multiplier times squared dilation is at most one over 50000 throughout the current Gaussian family. -/
theorem factor_mul_sq_le {q : ℝ} (hq : 1 ≤ q) :
    factor 9 (gaussianScale q) (shift q) * q ^ 2 ≤ 1 / 50000 := by
  have hq0 : 0 < q := by linarith
  rw [factor_mul_sq_eq hq0.ne']
  calc
    _ ≤ 24 * GaussianStripProfile.gaussianScale / ((1 / 200 : ℝ) ^ 2) := by
      gcongr
      · norm_num [GaussianStripProfile.gaussianScale, GaussianStripProfile.width]
      · exact (geometry hq).1
    _ ≤ _ := by norm_num [GaussianStripProfile.gaussianScale, GaussianStripProfile.width]

/-- The right-response multiplier has an inverse-square dilation bound, strengthening the old uniform constant cap. -/
theorem factor_le_inverse_square {q : ℝ} (hq : 1 ≤ q) :
    factor 9 (gaussianScale q) (shift q) ≤ (1 / 50000) / q ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < q))).mpr
  exact factor_mul_sq_le hq

/-- The complete complex Gaussian pole, rational subtraction and completion difference have a fixed bound at every nonzero working height. -/
theorem norm_extra_le {q t : ℝ} (hq : 1 ≤ q) (ht : 1 ≤ |t|) :
    ‖extra (gaussianScale q) (shift q) t‖ ≤ 15 := by
  have hB := (gaussianScale_bounds hq).1
  have hx := (shift_bounds hq).1
  have hg := norm_transform_le_thirteen hq ht
  have hc := (ZetaGaussianCompletionAverage.norm_response_sub_center_le hB
    (s := ZetaNearOneLocalDisc.center (shift q) t) (by simp [ZetaNearOneLocalDisc.center]; linarith)).trans
    (completion_le hq)
  have hz : 1 ≤ ‖(((2 + shift q : ℝ) : ℂ) + I * t)‖ := by
    have hh := Complex.re_le_norm (((2 + shift q : ℝ) : ℂ) + I * t)
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, sub_zero, add_zero] at hh
    linarith
  have hp : ‖(1 / (((2 + shift q : ℝ) : ℂ) + I * t) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr hz
  have hh := norm_add_le
    (GaussianComplexHalfMoments.transform (gaussianScale q) ((shift q : ℂ) + I * t) -
      1 / (((2 + shift q : ℝ) : ℂ) + I * t))
    (ZetaGaussianCompletionAverage.response (gaussianScale q) (ZetaNearOneLocalDisc.center (shift q) t) -
      zetaGlobalRegularCorrection (ZetaNearOneLocalDisc.center (shift q) t))
  have hd := norm_sub_le (GaussianComplexHalfMoments.transform (gaussianScale q) ((shift q : ℂ) + I * t))
    (1 / (((2 + shift q : ℝ) : ℂ) + I * t))
  unfold extra
  linarith

/-- The full signed Gaussian correction is bounded by nonconstant mass, for arbitrary countable eligible frequency families. -/
theorem abs_extraTotal_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n) {q t : ℝ} (hq : 1 ≤ q) (ht : 1 ≤ |t|) :
    |extraTotal (gaussianScale q) (shift q) t a ω| ≤ 15 * mass a := by
  have hh : |extraTotal (gaussianScale q) (shift q) t a ω| ≤ mass a * 15 := by
    rw [extraTotal, ← Real.norm_eq_abs]
    apply tsum_of_norm_bounded ((tail_summable ha hs).hasSum.mul_right 15)
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tail_nonneg ha n)]
    by_cases hn : n = 0
    · simp [tail, hn]
    have ht' : 1 ≤ |ω n * t| := by
      rw [abs_mul, abs_of_pos (by linarith [hω n hn] : 0 < ω n)]
      nlinarith [hω n hn]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans (norm_extra_le hq ht')) (tail_nonneg ha n)
  linarith

/-- The entire rational boundary correction is nonnegative and at most the nonconstant mass at the current explicit working heights. -/
theorem rationalTotal_bounds {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n) {q t : ℝ} (hq : 1 ≤ q) (ht : 1000000 ≤ |t|) :
    0 ≤ ZetaRegularizedSechMean.rationalTotal (rightLine 9 (shift q)) t
      (verticalScale 9 (shift q)) a ω ∧
    ZetaRegularizedSechMean.rationalTotal (rightLine 9 (shift q)) t
      (verticalScale 9 (shift q)) a ω ≤ mass a := by
  have hr := (geometry hq).2.2.2.2.2.1
  have hm : 0 ≤ mass a := tsum_nonneg (tail_nonneg ha)
  constructor
  · exact tsum_nonneg (fun n => mul_nonneg (tail_nonneg ha n)
      (RationalVerticalCorrection.mass_nonneg (by linarith) hr.ne' _ _))
  · have hh := ZetaRegularizedSechMean.rationalTotal_le ha hs hω hr
      (show t ≠ 0 by intro hh; norm_num [hh] at ht) (vertical_bounds hq).1.ne'
    have hb := mul_le_mul_of_nonneg_left (rational_le hq ht) hm
    linarith

/-- Both signs of the actual right-line pole and completion response cost at most three times the enlarged logarithmic height. -/
theorem abs_rightResponse_le {σ t : ℝ} (hσ : 1 ≤ σ) (hσ3 : σ ≤ 3) (ht : 1 ≤ |t|) :
    |rightResponse σ t| ≤ 3 * zetaEulerLogHeight t := by
  have hr := abs_re_zetaGlobalRegularCorrection_euler_le hσ hσ3 (t := t)
  have hz : 1 ≤ ‖((σ : ℂ) + I * t - 1)‖ :=
    ht.trans (by simpa using Complex.abs_im_le_norm ((σ : ℂ) + I * t - 1))
  have hp : |(1 / ((σ : ℂ) + I * t - 1) : ℂ).re| ≤ 1 := by
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr hz
  have hh := abs_add_le (1 / ((σ : ℂ) + I * t - 1) : ℂ).re
    (zetaGlobalRegularCorrection ((σ : ℂ) + I * t)).re
  unfold rightResponse
  rw [Complex.add_re]
  linarith [three_lt_zetaEulerLogHeight t]

/-- The complete signed right-response sum costs only nonconstant mass and the first logarithmic frequency moment. -/
theorem abs_rightTotal_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    {q t : ℝ} (hq : 1 ≤ q) (ht : 1 ≤ |t|) :
    |∑' n, tail a n * rightResponse (rightLine 9 (shift q)) (ω n * t)| ≤
      3 * (mass a * zetaEulerLogHeight t + frequencyCost a ω) := by
  have hu := ((tail_summable ha hs).hasSum.mul_right (3 * zetaEulerLogHeight t)).add
    (hlog.hasSum.mul_left 3)
  have hh : |∑' n, tail a n * rightResponse (rightLine 9 (shift q)) (ω n * t)| ≤
      mass a * (3 * zetaEulerLogHeight t) + 3 * frequencyCost a ω := by
    rw [← Real.norm_eq_abs]
    apply tsum_of_norm_bounded hu
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (tail_nonneg ha n)]
    by_cases hn : n = 0
    · simp [tail, hn]
    have ht' : 1 ≤ |ω n * t| := by
      rw [abs_mul, abs_of_pos (by linarith [hω n hn] : 0 < ω n)]
      nlinarith [hω n hn]
    have hr := abs_rightResponse_le (geometry hq).2.2.2.2.2.1.le
      (by linarith [(geometry hq).2.2.2.2.2.2]) ht'
    have hl := logHeight_mul_le (hω n hn) t
    nlinarith only [mul_le_mul_of_nonneg_left hr (tail_nonneg ha n),
      mul_le_mul_of_nonneg_left hl (tail_nonneg ha n)]
  linarith

/-- A two-sided bound for the entire non-left budget correction retains the inverse-square multiplier on the full right-response height cost. -/
theorem abs_correction_le {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    {q t : ℝ} (hq : 1 ≤ q) (ht : 1000000 ≤ |t|) :
    |correction q t a ω| ≤ 109 * mass a +
      3 * (mass a * zetaEulerLogHeight t + frequencyCost a ω) / (50000 * q ^ 2) := by
  have hm : 0 ≤ mass a := tsum_nonneg (tail_nonneg ha)
  have hq0 : 0 < q := by linarith
  have hη : 0 < halfWidth 9 (shift q) := by linarith [(geometry hq).1]
  have hR := rationalTotal_bounds ha hs hω hq ht
  have hR' : |ZetaRegularizedSechMean.rationalTotal (rightLine 9 (shift q)) t
      (verticalScale 9 (shift q)) a ω / (2 * halfWidth 9 (shift q))| ≤ 94 * mass a := by
    rw [abs_of_nonneg (div_nonneg hR.1 (by positivity))]
    calc
      _ ≤ mass a / (2 * halfWidth 9 (shift q)) := div_le_div_of_nonneg_right hR.2 (by positivity)
      _ = mass a * (1 / (2 * halfWidth 9 (shift q))) := by ring
      _ ≤ mass a * 94 := mul_le_mul_of_nonneg_left (geometry hq).2.2.1 hm
      _ = _ := by ring
  have he := abs_extraTotal_le ha hs hω hq (by linarith : 1 ≤ |t|)
  have hr := abs_rightTotal_le ha hs hω hlog hq (by linarith : 1 ≤ |t|)
  have hf := factor_le_inverse_square hq
  have hf0 := (factor_bounds hq).1
  have hright : |factor 9 (gaussianScale q) (shift q) *
      ∑' n, tail a n * rightResponse (rightLine 9 (shift q)) (ω n * t)| ≤
      3 * (mass a * zetaEulerLogHeight t + frequencyCost a ω) / (50000 * q ^ 2) := by
    rw [abs_mul, abs_of_nonneg hf0]
    have hh := mul_le_mul hf hr (abs_nonneg _) (by positivity : 0 ≤ (1 / 50000 : ℝ) / q ^ 2)
    calc
      _ ≤ ((1 / 50000 : ℝ) / q ^ 2) *
          (3 * (mass a * zetaEulerLogHeight t + frequencyCost a ω)) := hh
      _ = _ := by field_simp
  have hh := abs_add_le
    (ZetaRegularizedSechMean.rationalTotal (rightLine 9 (shift q)) t
      (verticalScale 9 (shift q)) a ω / (2 * halfWidth 9 (shift q)) +
      extraTotal (gaussianScale q) (shift q) t a ω)
    (factor 9 (gaussianScale q) (shift q) *
      ∑' n, tail a n * rightResponse (rightLine 9 (shift q)) (ω n * t))
  have hh' := abs_add_le
    (ZetaRegularizedSechMean.rationalTotal (rightLine 9 (shift q)) t
      (verticalScale 9 (shift q)) a ω / (2 * halfWidth 9 (shift q)))
    (extraTotal (gaussianScale q) (shift q) t a ω)
  unfold correction
  linarith

/-- The actual signed budget differs from its original clipped left mean by the proved full correction bound, uniformly in clipping depth. -/
theorem abs_signedBudget_sub_left_le {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    {q t : ℝ} (hq : 1 ≤ q) (ht : 1000000 ≤ |t|) (M : ℝ) :
    |signedBudget q M t a ω - leftBudget q M t a ω| ≤ 109 * mass a +
      3 * (mass a * zetaEulerLogHeight t + frequencyCost a ω) / (50000 * q ^ 2) := by
  rw [signedBudget_eq_left_add, add_sub_cancel_left]
  exact abs_correction_le ha hs hω hlog hq ht

/-- The signed budget minus the actual left mean, divided by dilation, tends to zero for moving families with bounded mass, logarithmic frequency cost and height-to-dilation ratio. -/
theorem tendsto_normalized_signedBudget_sub_left
    (a ω : ℕ → ℕ → ℝ) (q t M : ℕ → ℝ)
    (ha : ∀ N n, 0 ≤ a N n) (hs : ∀ N, Summable (a N))
    (hω : ∀ N n, n ≠ 0 → 1 ≤ ω N n)
    (hlog : ∀ N, Summable (fun n => tail (a N) n * Real.log (ω N n)))
    (hq : ∀ N, 1 ≤ q N) (hqt : Tendsto q atTop atTop)
    (ht : Tendsto (fun N => |t N|) atTop atTop)
    (A F C : ℝ) (hA : ∀ N, mass (a N) ≤ A) (hF : ∀ N, frequencyCost (a N) (ω N) ≤ F)
    (hC : ∀ N, zetaEulerLogHeight (t N) / q N ≤ C) :
    Tendsto (fun N => (signedBudget (q N) (M N) (t N) (a N) (ω N) -
      leftBudget (q N) (M N) (t N) (a N) (ω N)) / q N) atTop (𝓝 0) := by
  let K := |A| * |C| + |F|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlim : Tendsto (fun N => (109 * |A| + 3 * K / 50000) / q N) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp hqt).const_mul (109 * |A| + 3 * K / 50000)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [ht.eventually (eventually_ge_atTop 1000000)] with N hNt
  have hq0 : 0 < q N := by linarith [hq N]
  have he := abs_signedBudget_sub_left_le (ha N) (hs N) (hω N) (hlog N) (hq N) hNt (M N)
  have hL : 0 ≤ zetaEulerLogHeight (t N) / q N :=
    div_nonneg (by linarith [three_lt_zetaEulerLogHeight (t N)]) hq0.le
  have hm := mul_le_mul ((hA N).trans (le_abs_self A)) ((hC N).trans (le_abs_self C)) hL (abs_nonneg A)
  have hf : frequencyCost (a N) (ω N) / q N ≤ |F| := by
    apply (div_le_iff₀ hq0).mpr
    have hh := mul_le_mul_of_nonneg_left (hq N) (abs_nonneg F)
    linarith [hF N, le_abs_self F]
  have hsum : (mass (a N) * zetaEulerLogHeight (t N) + frequencyCost (a N) (ω N)) / q N ≤ K := by
    rw [add_div, mul_div_assoc]
    dsimp [K]
    linarith
  have hsum' := (div_le_iff₀ hq0).mp hsum
  have hright : 3 * (mass (a N) * zetaEulerLogHeight (t N) + frequencyCost (a N) (ω N)) /
      (50000 * (q N) ^ 2) ≤ 3 * K / 50000 := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 50000)).mpr
    have hh := mul_le_mul_of_nonneg_left (hq N) (mul_nonneg hK hq0.le)
    nlinarith only [hsum', hh]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hq0]
  apply div_le_div_of_nonneg_right _ hq0.le
  linarith [hA N, le_abs_self A]

/-- At the actual current dilation, all non-left budget terms vanish at the source scale, uniformly over moving eligible families and arbitrary clipping depths. -/
theorem tendsto_current_signedBudget_sub_left
    (a ω : ℕ → ℕ → ℝ) (t M : ℕ → ℝ)
    (ha : ∀ N n, 0 ≤ a N n) (hs : ∀ N, Summable (a N))
    (hω : ∀ N n, n ≠ 0 → 1 ≤ ω N n)
    (hlog : ∀ N, Summable (fun n => tail (a N) n * Real.log (ω N n)))
    (ht : Tendsto (fun N => |t N|) atTop atTop)
    (A F : ℝ) (hA : ∀ N, mass (a N) ≤ A) (hF : ∀ N, frequencyCost (a N) (ω N) ≤ F) :
    Tendsto (fun N => (signedBudget (ZetaGaussianAllHeight.dilation (t N)) (M N) (t N) (a N) (ω N) -
      leftBudget (ZetaGaussianAllHeight.dilation (t N)) (M N) (t N) (a N) (ω N)) /
        ZetaGaussianAllHeight.dilation (t N)) atTop (𝓝 0) := by
  exact tendsto_normalized_signedBudget_sub_left a ω _ t M ha hs hω hlog
    (fun _ => le_max_left _ _) (current_dilation_tendsto t ht) ht A F (320000 + Real.log 13)
    hA hF (fun N => current_dilation_height_ratio_upper (t N))

/-- Changing the comparison budget pays the full squared difference while preserving the positive source surplus. -/
theorem positive_surplus_square_le (S B L : ℝ) :
    (max 0 (S - L)) ^ 2 ≤ 2 * (max 0 (S - B)) ^ 2 + 2 * (B - L) ^ 2 := by
  have hh : max 0 (S - L) ≤ max 0 (S - B) + |B - L| := by
    apply max_le
    · exact add_nonneg (le_max_left _ _) (abs_nonneg _)
    · linarith [le_max_right (0 : ℝ) (S - B), le_abs_self (B - L)]
  have hs := mul_self_le_mul_self (le_max_left (0 : ℝ) (S - L)) hh
  have ht := sq_nonneg (max 0 (S - B) - |B - L|)
  nlinarith [sq_abs (B - L)]

/-- The actual positive squared finite-zero source surplus over the original signed clipped left mean has vanishing normalized limit at the current dilation. Every selected multiplicity and original phase hypothesis remains; no bound forcing the left mean below the source is assumed or proved. -/
theorem tendsto_current_source_surplus_over_left_sq
    (a ω : ℕ → ℕ → ℝ) (t M : ℕ → ℝ) (Z : ℕ → Finset NontrivialZetaZero)
    (ha : ∀ N n, 0 ≤ a N n) (hs : ∀ N, Summable (a N))
    (hP : ∀ N u, 0 ≤ zetaPhaseKernel (a N) (ω N) u)
    (hω0 : ∀ N, ω N 0 = 0) (hω1 : ∀ N, ω N 1 = 1)
    (hω : ∀ N n, n ≠ 0 → 1 ≤ ω N n)
    (hlog : ∀ N, Summable (fun n => tail (a N) n * Real.log (ω N n)))
    (hM : ∀ N, 0 ≤ M N) (hscale : ∀ N, 1 ≤ ZetaNearOneBudgetLimit.scale (t N))
    (ht : Tendsto (fun N => |t N|) atTop atTop)
    (A F : ℝ) (hA : ∀ N, mass (a N) ≤ A) (hF : ∀ N, frequencyCost (a N) (ω N) ≤ F) :
    Tendsto (fun N =>
      (max 0 ((a N 1 * ∑ ρ ∈ Z N, ZetaGaussianNearCancellation.compensated
        (gaussianScale (ZetaGaussianAllHeight.dilation (t N)))
        (halfWidth 9 (shift (ZetaGaussianAllHeight.dilation (t N))))
        (ZetaNearOneLocalDisc.center (shift (ZetaGaussianAllHeight.dilation (t N))) (t N)) ρ) -
          leftBudget (ZetaGaussianAllHeight.dilation (t N)) (M N) (t N) (a N) (ω N))) ^ 2 /
            (ZetaGaussianAllHeight.dilation (t N)) ^ 2) atTop (𝓝 0) := by
  let q := fun N => ZetaGaussianAllHeight.dilation (t N)
  let S := fun N => a N 1 * ∑ ρ ∈ Z N, ZetaGaussianNearCancellation.compensated
    (gaussianScale (q N)) (halfWidth 9 (shift (q N))) (ZetaNearOneLocalDisc.center (shift (q N)) (t N)) ρ
  have hsource := tendsto_current_source_surplus_sq a ω t M Z ha hs hP hω0 hω1 hω hlog
    hM hscale ht A F hA hF
  have hd := tendsto_current_signedBudget_sub_left a ω t M ha hs hω hlog ht A F hA hF
  have hlim : Tendsto (fun N =>
      2 * ((max 0 (S N - signedBudget (q N) (M N) (t N) (a N) (ω N))) ^ 2 / (q N) ^ 2) +
      2 * (((signedBudget (q N) (M N) (t N) (a N) (ω N) -
        leftBudget (q N) (M N) (t N) (a N) (ω N)) / q N) ^ 2)) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero] using
      (hsource.const_mul 2).add ((hd.pow 2).const_mul 2)
  apply squeeze_zero _ _ hlim
  · intro N
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · intro N
    have hq0 : 0 < q N := lt_of_lt_of_le zero_lt_one (show 1 ≤ q N from le_max_left _ _)
    have hh := positive_surplus_square_le (S N)
      (signedBudget (q N) (M N) (t N) (a N) (ω N)) (leftBudget (q N) (M N) (t N) (a N) (ω N))
    calc
      _ ≤ (2 * (max 0 (S N - signedBudget (q N) (M N) (t N) (a N) (ω N))) ^ 2 +
          2 * (signedBudget (q N) (M N) (t N) (a N) (ω N) -
            leftBudget (q N) (M N) (t N) (a N) (ω N)) ^ 2) / (q N) ^ 2 :=
        div_le_div_of_nonneg_right hh (sq_nonneg _)
      _ = _ := by field_simp

end
end RiemannGaussian.ZetaGaussianSignedBudgetReduction
