/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FiniteSignedFourierHinge
import RiemannGaussian.ZetaSquarefreeSignedTail

/-!
# The nonlinear prime character is integrable against the cutoff kernel

Retaining the local quadratic phase loss gives an exact cosine majorant
for the logarithmic remainder divided by frequency squared. The original
zeta prime features have one integrated bound uniform over finite prime
cutoffs at every fixed Re(s)>1/2. The first-order prime-phase core remains
in the exact exponential representation; its bound and the filtered
source-normalized floor remain open. Small primes stay explicit.
-/

namespace RiemannGaussian.ZetaPrimeCharacterRemainder
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
open CosineHinge ZetaSquarefreeSignedTail

/-- The nonlinear local logarithm retains its exact quadratic phase loss,
rather than replacing it by a frequency-independent constant. -/
theorem norm_local_log_error_le_phase (q z : ℂ) (hq : ‖q‖ ≤ 1 / 4)
    (hz : ‖z‖ ≤ 1) :
    ‖Complex.log (1 + q * (1 - z)) - q * (1 - z)‖ ≤ ‖q‖ ^ 2 * ‖1 - z‖ ^ 2 := by
  let w := q * (1 - z)
  have hw : ‖w‖ ≤ 1 / 2 := by
    have hz' : ‖1 - z‖ ≤ 2 := (norm_sub_le (1 : ℂ) z).trans (by rw [norm_one]; linarith only [hz])
    dsimp only [w]
    rw [norm_mul]
    nlinarith [mul_le_mul hq hz' (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)]
  have hi : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - ‖w‖)]
    linarith only [hw]
  have h := Complex.norm_log_one_add_sub_self_le (by linarith : ‖w‖ < 1)
  calc
    _ ≤ ‖w‖ ^ 2 := h.trans (by
      nlinarith only [mul_le_mul_of_nonneg_left hi (sq_nonneg ‖w‖)])
    _ = _ := by dsimp only [w]; rw [norm_mul, mul_pow]

/-- Squaring the complete unit-character difference gives an exact cosine
loss. It vanishes quadratically at frequency zero. -/
theorem norm_character_difference_sq (t : ℝ) :
    ‖1 - Complex.exp ((t : ℂ) * Complex.I)‖ ^ 2 = 2 * (1 - Real.cos t) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
    Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_im]
  nlinarith only [Real.sin_sq_add_cos_sq t]

/-- A single nonlinear logarithm error is controlled by a genuinely
integrable cosine kernel with a prime-square amplitude. -/
theorem norm_local_log_error_div_le (q : ℂ) (hq : ‖q‖ ≤ 1 / 4) (ell xi : ℝ) :
    ‖(Complex.log (1 + q * (1 - Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I))) -
      q * (1 - Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I))) / (xi : ℂ) ^ 2‖ ≤
      2 * ‖q‖ ^ 2 * ((1 - Real.cos (ell * xi)) / xi ^ 2) := by
  have h := norm_local_log_error_le_phase q
    (Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I)) hq
    (by rw [Complex.norm_exp_ofReal_mul_I])
  rw [norm_character_difference_sq] at h
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ (‖q‖ ^ 2 * (2 * (1 - Real.cos (ell * xi)))) / xi ^ 2 :=
      div_le_div_of_nonneg_right h (sq_nonneg xi)
    _ = _ := by ring

/-- The local normalized factor remains in the logarithm's analytic domain
for all real frequencies under the explicit small-prime-weight condition. -/
theorem local_character_mem_slitPlane (q : ℂ) (hq : ‖q‖ ≤ 1 / 4) (ell xi : ℝ) :
    1 + q * (1 - Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I)) ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_mul]
  have hz : ‖1 - Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I)‖ ≤ 2 := by
    have h := norm_sub_le (1 : ℂ) (Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I))
    simpa only [norm_one, Complex.norm_exp_ofReal_mul_I, one_add_one_eq_two] using h
  have h := mul_le_mul hq hz (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  linarith

/-- The local error divided by frequency squared is absolutely integrable,
with no puncture or unspecified limit at the origin. -/
theorem integrable_local_log_error_div (q : ℂ) (hq : ‖q‖ ≤ 1 / 4) (ell : ℝ) :
    IntegrableOn (fun xi : ℝ =>
      (Complex.log (1 + q * (1 - Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I))) -
        q * (1 - Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I))) / (xi : ℂ) ^ 2) (Ioi 0) := by
  apply ((integrable_one_sub_cos_div_sq ell).const_mul (2 * ‖q‖ ^ 2)).mono'
  · have hlog : Continuous (fun xi : ℝ =>
        Complex.log (1 + q * (1 - Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I)))) := by
      apply Continuous.clog (by fun_prop)
      intro xi
      exact local_character_mem_slitPlane q hq ell xi
    have hc : ContinuousOn (fun xi : ℝ =>
        (Complex.log (1 + q * (1 - Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I))) -
          q * (1 - Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I))) / (xi : ℂ) ^ 2) (Ioi 0) := by
      apply (hlog.sub (by fun_prop)).continuousOn.div (by fun_prop)
      intro xi hxi
      exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hxi))
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [] with xi
    exact norm_local_log_error_div_le q hq ell xi

/-- The full frequency integral of the nonlinear local error costs only
pi times its squared amplitude times its logarithmic scale. -/
theorem integral_norm_local_log_error_div_le (q : ℂ) (hq : ‖q‖ ≤ 1 / 4) (ell : ℝ) :
    (∫ xi : ℝ in Ioi 0,
      ‖(Complex.log (1 + q * (1 - Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I))) -
        q * (1 - Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I))) / (xi : ℂ) ^ 2‖) ≤
      Real.pi * ‖q‖ ^ 2 * |ell| := by
  calc
    _ ≤ ∫ xi : ℝ in Ioi 0, 2 * ‖q‖ ^ 2 * ((1 - Real.cos (ell * xi)) / xi ^ 2) :=
      integral_mono_ae (integrable_local_log_error_div q hq ell).norm
        ((integrable_one_sub_cos_div_sq ell).const_mul _) (Filter.Eventually.of_forall
          (norm_local_log_error_div_le q hq ell))
    _ = _ := by rw [integral_const_mul, integral_one_sub_cos_div_sq]; ring

/-- The exact first-order prime-phase contribution, retaining its complex sign. -/
def firstOrder {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (ell : ι → ℝ) (xi : ℝ) : ℂ :=
  ∑ p ∈ Q, q p * (1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I))

/-- Sum the local logarithm remainders, without choosing a logarithm
of the full complex product. -/
def logRemainder {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (ell : ι → ℝ) (xi : ℝ) : ℂ :=
  ∑ p ∈ Q, (Complex.log (1 + q p * (1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I))) -
    q p * (1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)))

/-- The finite normalized Euler character is exactly the exponential of
its first-order core and the sum of its small local remainders. -/
theorem normalized_character_eq_exp {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (xi : ℝ) :
    (∏ p ∈ Q, (1 + q p * (1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)))) =
      Complex.exp (firstOrder Q q ell xi + logRemainder Q q ell xi) := by
  have h : firstOrder Q q ell xi + logRemainder Q q ell xi =
      ∑ p ∈ Q, Complex.log (1 + q p * (1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I))) := by
    unfold firstOrder logRemainder
    rw [Finset.sum_sub_distrib]
    ring
  rw [h, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Complex.exp_log (Complex.slitPlane_ne_zero (local_character_mem_slitPlane (q p) (hq p hp) (ell p) xi))]

/-- The integrated nonlinear remainder preserves a sum of prime-square
logarithmic weights and is uniform in the selected finite set. -/
theorem integral_norm_logRemainder_div_le {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) :
    (∫ xi : ℝ in Ioi 0, ‖logRemainder Q q ell xi / (xi : ℂ) ^ 2‖) ≤
      Real.pi * ∑ p ∈ Q, ‖q p‖ ^ 2 * |ell p| := by
  have hi (p : ι) (hp : p ∈ Q) := integrable_local_log_error_div (q p) (hq p hp) (ell p)
  have he (xi : ℝ) : logRemainder Q q ell xi / (xi : ℂ) ^ 2 =
      ∑ p ∈ Q, (Complex.log (1 + q p * (1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I))) -
        q p * (1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I))) / (xi : ℂ) ^ 2 := by
    rw [logRemainder, Finset.sum_div]
  simp_rw [he]
  calc
    _ ≤ ∫ xi : ℝ in Ioi 0, ∑ p ∈ Q,
        ‖(Complex.log (1 + q p * (1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I))) -
          q p * (1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I))) / (xi : ℂ) ^ 2‖ := by
      apply integral_mono_ae (integrable_finsetSum _ hi).norm
        (integrable_finsetSum _ (fun p hp => (hi p hp).norm))
      filter_upwards [] with xi
      exact norm_sum_le _ _
    _ = ∑ p ∈ Q, ∫ xi : ℝ in Ioi 0,
        ‖(Complex.log (1 + q p * (1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I))) -
          q p * (1 - Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I))) / (xi : ℂ) ^ 2‖ :=
      integral_finsetSum Q (fun p hp => (hi p hp).norm)
    _ ≤ ∑ p ∈ Q, Real.pi * ‖q p‖ ^ 2 * |ell p| :=
      Finset.sum_le_sum (fun p hp => integral_norm_local_log_error_div_le (q p) (hq p hp) (ell p))
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring

/-- The full sum of local remainders has an absolutely convergent cutoff
frequency integral, before any estimates for its exponential main term. -/
theorem integrable_logRemainder_div {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) :
    IntegrableOn (fun xi : ℝ => logRemainder Q q ell xi / (xi : ℂ) ^ 2) (Ioi 0) := by
  simp only [logRemainder, Finset.sum_div]
  exact integrable_finsetSum _ (fun p hp => integrable_local_log_error_div (q p) (hq p hp) (ell p))

/-- A convergent integer majorant pays the actual logarithmic prime-square
mass for any finite set of labels, at every fixed Re(s)>1/2. -/
theorem actual_prime_square_log_sum_le (Q : Finset ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    (∑ p ∈ Q, ‖zetaPrimeFeature s p‖ ^ 2 * |Real.log p|) ≤
      (s.re - 1 / 2)⁻¹ * ∑' n, zetaPrimeExpWeight (s.re + 1 / 2) n := by
  have he (p : ℕ) : ‖zetaPrimeFeature s p‖ ^ 2 * |Real.log p| =
      ‖zetaPrimeLogKernel 1 ((2 * s.re : ℝ) : ℂ) p‖ := by
    rw [norm_zetaPrimeFeature, norm_zetaPrimeLogKernel]
    simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, Complex.ofReal_re,
      abs_of_nonneg (Real.log_natCast_nonneg p)]
    unfold zetaPrimeExpWeight
    rw [pow_two, ← Real.exp_add, mul_comm]
    congr 1
    ring
  simp_rw [he]
  calc
    _ ≤ ∑ p ∈ Q, (s.re - 1 / 2)⁻¹ * zetaPrimeExpWeight (s.re + 1 / 2) p := by
      apply Finset.sum_le_sum
      intro p _hp
      have h := norm_zetaPrimeLogKernel_le 1 ((2 * s.re : ℝ) : ℂ) p (by linarith : 0 < s.re - 1 / 2)
      simpa only [pow_one, Complex.ofReal_re, show 2 * s.re - (s.re - 1 / 2) = s.re + 1 / 2 by ring] using h
    _ = (s.re - 1 / 2)⁻¹ * ∑ p ∈ Q, zetaPrimeExpWeight (s.re + 1 / 2) p := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_zetaPrimeExpWeight (by linarith : 1 < s.re + 1 / 2)).sum_le_tsum Q
        (fun n _ => (Real.exp_pos _).le)) (by positivity)

/-- The actual nonlinear prime-character remainder is uniformly integrable
against the exact hinge kernel over all finite prime cutoffs. The first-order
core and its exponential, and the factorial filter, are still separate. -/
theorem integral_norm_actual_logRemainder_div_le (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, 16 ≤ p) {s : ℂ} (hs : 1 / 2 < s.re) :
    (∫ xi : ℝ in Ioi 0,
      ‖logRemainder Q (zetaPrimeFeature s) (fun p => Real.log p) xi / (xi : ℂ) ^ 2‖) ≤
      Real.pi * (s.re - 1 / 2)⁻¹ * ∑' n, zetaPrimeExpWeight (s.re + 1 / 2) n := by
  have h := integral_norm_logRemainder_div_le Q (zetaPrimeFeature s) (fun p => Real.log p)
    (fun p hp => norm_primeFeature_le_quarter hs.le (hQ p hp))
  apply h.trans
  have hmass := mul_le_mul_of_nonneg_left (actual_prime_square_log_sum_le Q hs) Real.pi_pos.le
  simpa only [mul_assoc] using hmass

end
end RiemannGaussian.ZetaPrimeCharacterRemainder
