/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGaussianPhaseArithmetic
import RiemannGaussian.ZetaGaussianPhaseAllowance

/-!
# The complete Gaussian strip inequality for every admissible phase family

The original Gaussian prime response, shifted Euler prime work and averaged
right logarithmic prime response remain coupled to the same phase kernel.
The selected actual zero keeps its compensated source and full multiplicity.
Only the constant channel pays the corresponding real-axis arithmetic costs.
Every countable sum is genuinely summable under the existing logarithmic
frequency moment. The full signed pole and completion correction remains
available alongside the exact left and right boundary responses.
-/

namespace RiemannGaussian.ZetaGaussianStripPhaseFamily
noncomputable section
open Complex
open ZetaNearOneLocalDisc ZetaNearOneBudgetLimit ZetaStripEulerConstraint
open ZetaAngularPhaseAllowance ZetaGaussianNearCancellation
open ZetaGaussianPhaseAllowance
open scoped Classical

/-- The original coefficient paying the complete Gaussian divisor correction. -/
def factor (k : ℕ) (B x : ℝ) : ℝ := 24 * B / halfWidth k x ^ 2

/-- The full original complex smoothed pole and completion difference, with
the rational center subtraction retained before any estimate. -/
def extra (B x t : ℝ) : ℂ :=
  GaussianComplexHalfMoments.transform B ((x : ℂ) + I * t) -
    1 / (((2 + x : ℝ) : ℂ) + I * t) +
    (ZetaGaussianCompletionAverage.response B (center x t) -
      zetaGlobalRegularCorrection (center x t))

/-- The complete signed nonconstant smoothing correction. -/
def extraTotal (B x t : ℝ) (a ω : ℕ → ℝ) : ℝ := ∑' n, tail a n * (extra B x (ω n * t)).re

/-- The three actual prime responses on a common phase family and Gaussian scale. -/
def mixedWork (k : ℕ) (B x t : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  (∑' n, a n * GaussianFermiPrimeComparison.ordinarySum (1 + x) B (ω n * t)) +
    factor k B x * (∑' m, zetaPhasePrimeWeight (rightLine k x) m *
      zetaPhaseKernel a ω (t * Real.log m)) +
    (∑' n, a n * ZetaSechPrimeBoundary.mean (rightLine k x) (ω n * t) (verticalScale k x)) /
      (2 * halfWidth k x)

/-- The same three actual prime responses on their constant channel. -/
def constantWork (k : ℕ) (B x : ℝ) : ℝ :=
  GaussianFermiPrimeComparison.ordinarySum (1 + x) B 0 +
    factor k B x * (-logDeriv riemannZeta (rightLine k x : ℂ)).re +
    ZetaSechPrimeBoundary.mean (rightLine k x) 0 (verticalScale k x) / (2 * halfWidth k x)

/-- The exact remaining signed budget, after all three arithmetic responses
are kept together. No frequency-by-frequency Euler norm cost is substituted. -/
def exactBudget (k : ℕ) (B M x t : ℝ) (a ω : ℕ → ℝ) : ℝ :=
  a 0 * constantWork k B x +
    (ZetaClippedEulerFamily.totalMean k M t (verticalScale k x) a ω +
      ZetaRegularizedSechMean.rationalTotal (rightLine k x) t (verticalScale k x) a ω) /
      (2 * halfWidth k x) + extraTotal B x t a ω +
    factor k B x * ∑' n, tail a n * rightResponse (rightLine k x) (ω n * t)

/-- The complete complex smoothing corrections are summable for arbitrary
frequencies before taking their signed real projections. -/
theorem summable_extra {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (t : ℝ) :
    Summable (fun n => (a n : ℂ) * extra B x (ω n * t)) := by
  have hf := summable_transform (ω := ω) ha hs hB hx.le t
  have hp := summable_pole (ω := ω) ha hs (show 0 < 2 + x by linarith) t
  have hc := summable_completion (ω := ω) ha hs hB (show 0 < 1 + x by linarith) t
  simpa only [extra, center, mul_add, mul_sub, Complex.ofReal_mul] using (hf.sub hp).add hc

/-- The complete original signed smoothing correction has a genuine real sum. -/
theorem summable_extra_re {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    {B x : ℝ} (hB : 0 < B) (hx : 0 < x) (t : ℝ) :
    Summable (fun n => a n * (extra B x (ω n * t)).re) := by
  simpa only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] using
    Complex.reCLM.summable (summable_extra (ω := ω) ha hs hB hx t)

/-- The actual Gaussian strip inequality in the exact balanced boundary
coordinates, retaining any selected finite actual zero group. -/
theorem prime_add_selected_le_means (k : ℕ) (hk : 2 ≤ k) {B x M : ℝ}
    (hB : 0 < B) (hx : 0 < x) (hx' : x ≤ DerivativeOrderComparison.delta k / 4)
    (hM : 0 ≤ M) (t : ℝ) (S : Finset NontrivialZetaZero) :
    GaussianFermiPrimeComparison.ordinarySum (1 + x) B t +
        (∑ ρ ∈ S, compensated B (halfWidth k x) (center x t) ρ) ≤
      (ZetaClippedEulerMean.mean k M t (verticalScale k x) -
        ZetaRegularizedSechMean.mean (rightLine k x) t (verticalScale k x)) /
        (2 * halfWidth k x) + (extra B x t).re +
        factor k B x * (logDeriv riemannXi ((rightLine k x : ℂ) + I * t)).re := by
  have hg := geometry k hk hx hx' t
  have h := ZetaGaussianStripBound.prime_add_selected_le (by linarith : 1 < 1 + x) hB
    (halfWidth_pos k hx) (by simpa [center] using hg.1) (by simpa [center] using hg.2) hM t S
  rw [show ((1 + x : ℝ) : ℂ) + I * (t : ℂ) = center x t from rfl] at h
  change GaussianFermiPrimeComparison.ordinarySum (1 + x) B t +
    (∑ ρ ∈ S, compensated B (halfWidth k x) (center x t) ρ) ≤ _ at h
  have hm : center x t - 1 = (x : ℂ) + I * t := by unfold center; push_cast; ring
  have hp : center x t + 1 = ((2 + x : ℝ) : ℂ) + I * t := by unfold center; push_cast; ring
  have hs : center x t + (halfWidth k x : ℂ) = ((rightLine k x : ℝ) : ℂ) + I * t := by
    unfold center halfWidth rightLine
    push_cast
    ring
  rw [boundary_eq, hm, hp, hs] at h
  simp only [extra, Complex.add_re, Complex.sub_re, factor, div_eq_mul_inv] at h ⊢
  nlinarith only [h]

/-- The constant/nonconstant split of the averaged right logarithm is exact.
Its complete positive phase response remains visible alongside the rational mass. -/
theorem right_mean_identity {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hω0 : ω 0 = 0) {σ : ℝ} (hσ : 1 < σ) (t b : ℝ) :
    (∑' n, tail a n * ZetaRegularizedSechMean.mean σ (ω n * t) b) +
      a 0 * ZetaSechPrimeBoundary.mean σ 0 b +
      ZetaRegularizedSechMean.rationalTotal σ t b a ω =
      (∑' n, a n * ZetaSechPrimeBoundary.mean σ (ω n * t) b) := by
  have hz := ZetaSechPhaseFamily.summable_means (ω := ω) ha hs hσ t b
  have hzt := ZetaSechPhaseFamily.summable_means (ω := ω) (tail_nonneg ha) (tail_summable ha hs) hσ t b
  have hr := ZetaRegularizedSechMean.summable_rational (ω := ω) ha hs hσ t b
  have he : (∑' n, tail a n * ZetaRegularizedSechMean.mean σ (ω n * t) b) =
      (∑' n, tail a n * ZetaSechPrimeBoundary.mean σ (ω n * t) b) -
        ZetaRegularizedSechMean.rationalTotal σ t b a ω := by
    simp only [ZetaRegularizedSechMean.mean_eq hσ, mul_sub]
    exact hzt.tsum_sub hr
  rw [he, hz.tsum_eq_add_tsum_ite 0, hω0, zero_mul]
  simp only [tail, ite_mul, zero_mul]
  ring

/-- The selected actual zero and all three original prime responses obey
one complete signed inequality for every eligible countable family. The
kernel's nonnegativity is not needed until the downstream scalar estimate. -/
theorem source_add_mixedWork_le_exactBudget {a ω : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable a) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) {B x M : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hx' : x ≤ DerivativeOrderComparison.delta k / 4) (hM : 0 ≤ M)
    (ρ : NontrivialZetaZero) (hscale : 1 ≤ scale ρ.1.im) :
    a 1 * compensated B (halfWidth k x) (center x ρ.1.im) ρ + mixedWork k B x ρ.1.im a ω ≤
      exactBudget k B M x ρ.1.im a ω := by
  let t := ρ.1.im
  let Q := compensated B (halfWidth k x) (center x t) ρ
  let P (n : ℕ) := GaussianFermiPrimeComparison.ordinarySum (1 + x) B (ω n * t)
  let L (n : ℕ) := ZetaClippedEulerMean.mean k M (ω n * t) (verticalScale k x)
  let R (n : ℕ) := ZetaRegularizedSechMean.mean (rightLine k x) (ω n * t) (verticalScale k x)
  let E (n : ℕ) := (extra B x (ω n * t)).re
  let X (n : ℕ) := (logDeriv riemannXi ((rightLine k x : ℂ) + I * (ω n * t))).re
  let U (n : ℕ) := (tail a n * L n - tail a n * R n) / (2 * halfWidth k x) +
    tail a n * E n + factor k B x * (tail a n * X n)
  have hP : Summable (fun n => a n * P n) :=
    ZetaGaussianPhaseArithmetic.summable_channels ha hs (by linarith : 2 / 3 < 1 + x) hB t
  have hL : Summable (fun n => tail a n * L n) :=
    ZetaClippedEulerFamily.summable_means ha hs hω hlog k (by omega) hM (verticalScale k x) hscale
  have hR : Summable (fun n => tail a n * R n) :=
    ZetaRegularizedSechMean.summable_means (ω := ω) (tail_nonneg ha) (tail_summable ha hs)
      (rightLine_gt_one k hx) t (verticalScale k x)
  have hE : Summable (fun n => tail a n * E n) :=
    summable_extra_re (ω := ω) (tail_nonneg ha) (tail_summable ha hs) hB hx t
  have hX : Summable (fun n => tail a n * X n) :=
    summable_xi ha hs hω hlog (rightLine_gt_one k hx) t
  have hU : Summable U := (((hL.sub hR).div_const (2 * halfWidth k x)).add hE).add
    (hX.mul_left (factor k B x))
  have hq := (hasSum_ite_eq (1 : ℕ) (a 1 * Q)).summable
  have hc := (hasSum_ite_eq (0 : ℕ) (a 0 * GaussianFermiPrimeComparison.ordinarySum (1 + x) B 0)).summable
  have hpoint (n : ℕ) : a n * P n + (if n = 1 then a 1 * Q else 0) ≤
      (if n = 0 then a 0 * GaussianFermiPrimeComparison.ordinarySum (1 + x) B 0 else 0) + U n := by
    by_cases hn0 : n = 0
    · subst n
      simp [P, U, tail, hω0]
    · by_cases hn1 : n = 1
      · subst n
        have h := mul_le_mul_of_nonneg_left
          (prime_add_selected_le_means k hk hB hx hx' hM t {ρ}) (ha 1)
        simp only [Finset.sum_singleton] at h
        simp only [P, U, L, R, E, X, hω1, one_mul, tail,
          show (1 : ℕ) ≠ 0 by norm_num, if_false, if_true, zero_add, Q, Complex.ofReal_one]
        simp only [div_eq_mul_inv] at h ⊢
        nlinarith only [h]
      · have h := mul_le_mul_of_nonneg_left
          (prime_add_selected_le_means k hk hB hx hx' hM (ω n * t) ∅) (ha n)
        simp only [Finset.sum_empty, add_zero] at h
        simp only [P, U, L, R, E, X, tail, hn0, hn1, if_false, add_zero, zero_add]
        simp only [div_eq_mul_inv, Complex.ofReal_mul] at h ⊢
        nlinarith only [h]
  have hb := (hP.add hq).tsum_le_tsum hpoint (hc.add hU)
  rw [hP.tsum_add hq, hc.tsum_add hU] at hb
  simp only [tsum_ite_eq] at hb
  have hu : (∑' n, U n) =
      ((∑' n, tail a n * L n) - ∑' n, tail a n * R n) / (2 * halfWidth k x) +
      (∑' n, tail a n * E n) + factor k B x * ∑' n, tail a n * X n := by
    simp only [U, Summable.tsum_add (((hL.sub hR).div_const (2 * halfWidth k x)).add hE)
      (hX.mul_left (factor k B x)), Summable.tsum_add ((hL.sub hR).div_const (2 * halfWidth k x)) hE,
      tsum_div_const, hL.tsum_sub hR, tsum_mul_left]
  rw [hu] at hb
  have hr := congrArg (fun y : ℝ => y / (2 * halfWidth k x))
    (right_mean_identity ha hs hω0 (rightLine_gt_one k hx) t (verticalScale k x))
  have hxid := congrArg (fun y : ℝ => factor k B x * y)
    (tsum_xi_add_arithmetic_eq ha hs hω0 hω hlog (rightLine_gt_one k hx) t)
  change a 1 * Q + mixedWork k B x t a ω ≤ exactBudget k B M x t a ω
  unfold mixedWork exactBudget constantWork extraTotal ZetaClippedEulerFamily.totalMean
  dsimp only [P, L, R, E, X] at hb
  simp only [div_eq_mul_inv] at hb hr hxid ⊢
  nlinarith only [hb, hr, hxid]

/-- All three original arithmetic responses have favorable sign only after
their shared full phase kernel has been used. -/
theorem mixedWork_nonneg {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (k : ℕ) {B x : ℝ}
    (hB : 0 < B) (hx : 0 < x) (t : ℝ) : 0 ≤ mixedWork k B x t a ω := by
  have hg := ZetaGaussianPhaseArithmetic.channels_nonneg ha hs hp
    (by linarith : 2 / 3 < 1 + x) hB t
  have he : 0 ≤ ∑' m, zetaPhasePrimeWeight (rightLine k x) m *
      zetaPhaseKernel a ω (t * Real.log m) :=
    tsum_nonneg (fun m => mul_nonneg (zetaPhasePrimeWeight_nonneg _ m) (hp _))
  have hr := ZetaSechPhaseFamily.means_nonneg ha hs hp (rightLine_gt_one k hx) t (verticalScale k x)
  have hwidth := halfWidth_pos k hx
  unfold mixedWork factor
  exact add_nonneg (add_nonneg hg (mul_nonneg (by positivity) he)) (div_nonneg hr (by positivity))

/-- Every admissible countable family bounds the full actual selected
Gaussian source by the exact signed budget, with all three prime series controlled. -/
theorem source_le_exactBudget {a ω : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hs : Summable a)
    (hp : ∀ u, 0 ≤ zetaPhaseKernel a ω u) (hω0 : ω 0 = 0) (hω1 : ω 1 = 1)
    (hω : ∀ n, n ≠ 0 → 1 ≤ ω n)
    (hlog : Summable (fun n => tail a n * Real.log (ω n)))
    (k : ℕ) (hk : 2 ≤ k) {B x M : ℝ} (hB : 0 < B) (hx : 0 < x)
    (hx' : x ≤ DerivativeOrderComparison.delta k / 4) (hM : 0 ≤ M)
    (ρ : NontrivialZetaZero) (hscale : 1 ≤ scale ρ.1.im) :
    a 1 * compensated B (halfWidth k x) (center x ρ.1.im) ρ ≤
      exactBudget k B M x ρ.1.im a ω := by
  have h := source_add_mixedWork_le_exactBudget ha hs hω0 hω1 hω hlog k hk hB hx hx' hM ρ hscale
  linarith [mixedWork_nonneg ha hs hp k hB hx ρ.1.im]

end
end RiemannGaussian.ZetaGaussianStripPhaseFamily
