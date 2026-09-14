/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCompositeProduct
import RiemannGaussian.ZetaPrimeNonlinearHalfplane

/-!
# Finite Euler quotients and paired local corrections

The complete finite character factors into an explicit Euler quotient and
its quadratic local correction. Reciprocal-frequency pairing cancels the
linear correction at frequency zero and gives an integrable cosine bound.
The local paired allowance tends uniformly to zero above a growing prime
threshold on each fixed closed half-plane right of one half. The quotient,
its original factorial filter and signed completion boundary remain unpaid.
No infinite Euler-product identity is asserted in this module.
-/

namespace RiemannGaussian.ZetaRieszEulerQuotient
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory Set

/-- The exact quadratic correction to the local two-variable Euler quotient. -/
def localCorrection (q z : ℂ) : ℂ := q ^ 2 * (z - 1) / (1 - q * z)

/-- Recombining the local correction with the Euler quotient recovers
the complete signed character, with no expansion or prime-count truncation. -/
theorem local_factorization (q z : ℂ) (hq : 1 - q ≠ 0) (hz : 1 - q * z ≠ 0) :
    1 + q * (1 - z) = (1 - q * z) / (1 - q) * (1 + localCorrection q z) := by
  have h := ZetaSquarefreeSignedTail.deformed_euler_local_factor q (q * z) hq hz
  unfold localCorrection
  convert h using 1 <;> ring

/-- The denominator is uniformly separated from zero for all unit
characters at every local weight in the stated disk. -/
theorem local_denominator_bound {q z : ℂ} (hq : ‖q‖ ≤ 1 / 4) (hz : ‖z‖ ≤ 1) :
    3 / 4 ≤ ‖1 - q * z‖ := by
  have h := norm_sub_norm_le (1 : ℂ) (q * z)
  rw [norm_one, norm_mul] at h
  have hm := mul_le_mul hq hz (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  nlinarith

/-- The local quotient has no totalized singularity in the bounded-weight domain. -/
theorem local_denominator_ne_zero {q z : ℂ} (hq : ‖q‖ ≤ 1 / 4) (hz : ‖z‖ ≤ 1) :
    1 - q * z ≠ 0 := norm_pos_iff.mp
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4) (local_denominator_bound hq hz))

/-- Coupling reciprocal phases cancels the linear-frequency defect of
the Euler-quotient correction exactly, before taking any absolute value. -/
theorem paired_local_identity (q z w : ℂ) (hzw : z * w = 1)
    (hz : 1 - q * z ≠ 0) (hw : 1 - q * w ≠ 0) :
    localCorrection q z + localCorrection q w =
      q ^ 2 * (1 + q) * (z + w - 2) / ((1 - q * z) * (1 - q * w)) := by
  unfold localCorrection
  field_simp
  linear_combination (-2 * q ^ 3) * hzw


/-- The reciprocal real-frequency characters retain an exact unit product. -/
theorem phase_mul_neg (x : ℝ) :
    Complex.exp ((x : ℂ) * Complex.I) * Complex.exp (((-x : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [← Complex.exp_add]
  simp

/-- The reciprocal phases have exactly a cosine second difference. -/
theorem norm_phase_pair_sub_two (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (((-x : ℝ) : ℂ) * Complex.I) - 2‖ =
      2 * (1 - Real.cos x) := by
  have he : Complex.exp ((x : ℂ) * Complex.I) +
      Complex.exp (((-x : ℝ) : ℂ) * Complex.I) - 2 = ((2 * (Real.cos x - 1) : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.add_re, Complex.exp_ofReal_mul_I_re,
        Real.cos_neg, Complex.ofReal_re]
      norm_num
      ring
    · simp only [Complex.sub_im, Complex.add_im, Complex.exp_ofReal_mul_I_im,
        Real.sin_neg, Complex.ofReal_im]
      norm_num
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one x))]
  ring

/-- A coupled local correction has a quadratic cosine bound. Each
individual correction has a linear-frequency term which is not discarded. -/
theorem norm_paired_local_le (q : ℂ) (hq : ‖q‖ ≤ 1 / 4) (x : ℝ) :
    ‖localCorrection q (Complex.exp ((x : ℂ) * Complex.I)) +
      localCorrection q (Complex.exp (((-x : ℝ) : ℂ) * Complex.I))‖ ≤
        16 * ‖q‖ ^ 2 * (1 - Real.cos x) := by
  let z := Complex.exp ((x : ℂ) * Complex.I)
  let w := Complex.exp (((-x : ℝ) : ℂ) * Complex.I)
  have hz : ‖z‖ ≤ 1 := (Complex.norm_exp_ofReal_mul_I x).le
  have hw : ‖w‖ ≤ 1 := (Complex.norm_exp_ofReal_mul_I (-x)).le
  have hz0 := local_denominator_ne_zero hq hz
  have hw0 := local_denominator_ne_zero hq hw
  have hdz := local_denominator_bound hq hz
  have hdw := local_denominator_bound hq hw
  have hd : 1 / 4 ≤ ‖1 - q * z‖ * ‖1 - q * w‖ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdz) (sub_nonneg.mpr hdw)]
  have hd0 : 0 < ‖1 - q * z‖ * ‖1 - q * w‖ := by linarith
  have hq1 : ‖1 + q‖ ≤ 2 := by
    have h := norm_add_le (1 : ℂ) q
    rw [norm_one] at h
    linarith
  have hx : 0 ≤ 1 - Real.cos x := sub_nonneg.mpr (Real.cos_le_one x)
  change ‖localCorrection q z + localCorrection q w‖ ≤ _
  rw [paired_local_identity q z w (phase_mul_neg x) hz0 hw0]
  simp only [norm_div, norm_mul, norm_pow]
  change ‖q‖ ^ 2 * ‖1 + q‖ * ‖z + w - 2‖ / (‖1 - q * z‖ * ‖1 - q * w‖) ≤ _
  rw [show ‖z + w - 2‖ = 2 * (1 - Real.cos x) from norm_phase_pair_sub_two x]
  apply (div_le_iff₀ hd0).mpr
  calc
    _ ≤ ‖q‖ ^ 2 * 2 * (2 * (1 - Real.cos x)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq1 (sq_nonneg _)) (by positivity)
    _ = (16 * ‖q‖ ^ 2 * (1 - Real.cos x)) * (1 / 4) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

/-- The paired quotient is dominated by the original integrable cosine
kernel, uniformly in the complex local phase of q. -/
theorem norm_paired_local_div_le (q : ℂ) (hq : ‖q‖ ≤ 1 / 4) (ell xi : ℝ) :
    ‖(localCorrection q (Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I)) +
      localCorrection q (Complex.exp (((-(ell * xi) : ℝ) : ℂ) * Complex.I))) /
        (xi : ℂ) ^ 2‖ ≤
      16 * ‖q‖ ^ 2 * ((1 - Real.cos (ell * xi)) / xi ^ 2) := by
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ (16 * ‖q‖ ^ 2 * (1 - Real.cos (ell * xi))) / xi ^ 2 :=
      div_le_div_of_nonneg_right (norm_paired_local_le q hq (ell * xi)) (sq_nonneg xi)
    _ = _ := by ring


/-- The actual local correction is continuous for every real character
frequency; its denominator remains separated from zero. -/
theorem continuous_localCorrection_phase (q : ℂ) (hq : ‖q‖ ≤ 1 / 4) :
    Continuous (fun x : ℝ => localCorrection q (Complex.exp ((x : ℂ) * Complex.I))) := by
  unfold localCorrection
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  exact local_denominator_ne_zero hq (Complex.norm_exp_ofReal_mul_I x).le

/-- The paired local Euler correction divided by frequency squared is
genuinely integrable. Pairing precedes division and the norm. -/
theorem integrable_paired_local_div (q : ℂ) (hq : ‖q‖ ≤ 1 / 4) (ell : ℝ) :
    IntegrableOn (fun xi : ℝ =>
      (localCorrection q (Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I)) +
        localCorrection q (Complex.exp (((-(ell * xi) : ℝ) : ℂ) * Complex.I))) /
          (xi : ℂ) ^ 2) (Ioi 0) := by
  apply ((CosineHinge.integrable_one_sub_cos_div_sq ell).const_mul (16 * ‖q‖ ^ 2)).mono'
  · have hp := (continuous_localCorrection_phase q hq).comp
      (show Continuous (fun xi : ℝ => ell * xi) by fun_prop)
    have hm := (continuous_localCorrection_phase q hq).comp
      (show Continuous (fun xi : ℝ => -(ell * xi)) by fun_prop)
    have hc : ContinuousOn (fun xi : ℝ =>
        (localCorrection q (Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I)) +
          localCorrection q (Complex.exp (((-(ell * xi) : ℝ) : ℂ) * Complex.I))) /
            (xi : ℂ) ^ 2) (Ioi 0) := by
      apply (hp.add hm).continuousOn.div (by fun_prop)
      intro xi hxi
      exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hxi))
    exact hc.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [] with xi
    exact norm_paired_local_div_le q hq ell xi

/-- The integrated paired correction costs only a square-amplitude
logarithmic weight, with arbitrary complex phase of the prime amplitude. -/
theorem integral_norm_paired_local_div_le (q : ℂ) (hq : ‖q‖ ≤ 1 / 4) (ell : ℝ) :
    (∫ xi : ℝ in Ioi 0,
      ‖(localCorrection q (Complex.exp (((ell * xi : ℝ) : ℂ) * Complex.I)) +
        localCorrection q (Complex.exp (((-(ell * xi) : ℝ) : ℂ) * Complex.I))) /
          (xi : ℂ) ^ 2‖) ≤ 8 * Real.pi * ‖q‖ ^ 2 * |ell| := by
  calc
    _ ≤ ∫ xi : ℝ in Ioi 0,
        16 * ‖q‖ ^ 2 * ((1 - Real.cos (ell * xi)) / xi ^ 2) :=
      integral_mono_ae (integrable_paired_local_div q hq ell).norm
        ((CosineHinge.integrable_one_sub_cos_div_sq ell).const_mul _)
        (Filter.Eventually.of_forall (norm_paired_local_div_le q hq ell))
    _ = _ := by
      rw [integral_const_mul, CosineHinge.integral_one_sub_cos_div_sq]
      ring


/-- The complete paired sum of local quotient corrections. This is
not the full product of correction factors. -/
def pairedLocalSum {ι : Type*} (Q : Finset ι) (q : ι → ℂ) (ell : ι → ℝ) (xi : ℝ) : ℂ :=
  ∑ p ∈ Q, (localCorrection (q p) (Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)) +
    localCorrection (q p) (Complex.exp (((-(ell p * xi) : ℝ) : ℂ) * Complex.I)))

/-- The coupled sum of local correction quotients has an ordinary
absolutely convergent frequency integral. -/
theorem integrable_pairedLocalSum_div {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) :
    IntegrableOn (fun xi : ℝ => pairedLocalSum Q q ell xi / (xi : ℂ) ^ 2) (Ioi 0) := by
  simp only [pairedLocalSum, Finset.sum_div]
  exact integrable_finsetSum _ (fun p hp => integrable_paired_local_div (q p) (hq p hp) (ell p))

/-- Pairing the two frequencies first pays the full finite sum of
local corrections by its square-amplitude logarithmic mass. -/
theorem integral_norm_pairedLocalSum_div_le {ι : Type*} (Q : Finset ι)
    (q : ι → ℂ) (ell : ι → ℝ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) :
    (∫ xi : ℝ in Ioi 0, ‖pairedLocalSum Q q ell xi / (xi : ℂ) ^ 2‖) ≤
      8 * Real.pi * ∑ p ∈ Q, ‖q p‖ ^ 2 * |ell p| := by
  have hi (p : ι) (hp : p ∈ Q) := integrable_paired_local_div (q p) (hq p hp) (ell p)
  simp only [pairedLocalSum, Finset.sum_div]
  calc
    _ ≤ ∫ xi : ℝ in Ioi 0, ∑ p ∈ Q,
        ‖(localCorrection (q p) (Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)) +
          localCorrection (q p) (Complex.exp (((-(ell p * xi) : ℝ) : ℂ) * Complex.I))) /
            (xi : ℂ) ^ 2‖ := by
      apply integral_mono_ae (integrable_finsetSum _ hi).norm
        (integrable_finsetSum _ (fun p hp => (hi p hp).norm))
      filter_upwards [] with xi
      exact norm_sum_le _ _
    _ = ∑ p ∈ Q, ∫ xi : ℝ in Ioi 0,
        ‖(localCorrection (q p) (Complex.exp (((ell p * xi : ℝ) : ℂ) * Complex.I)) +
          localCorrection (q p) (Complex.exp (((-(ell p * xi) : ℝ) : ℂ) * Complex.I))) /
            (xi : ℂ) ^ 2‖ := integral_finsetSum Q (fun p hp => (hi p hp).norm)
    _ ≤ ∑ p ∈ Q, 8 * Real.pi * ‖q p‖ ^ 2 * |ell p| :=
      Finset.sum_le_sum (fun p hp => integral_norm_paired_local_div_le (q p) (hq p hp) (ell p))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring

/-- The complete finite character is its exact Euler quotient times
all local correction factors. No product is replaced by its linearization. -/
theorem finite_character_eq_quotient_product {ι : Type*} (Q : Finset ι)
    (q z : ι → ℂ) (hq : ∀ p ∈ Q, ‖q p‖ ≤ 1 / 4) (hz : ∀ p ∈ Q, ‖z p‖ ≤ 1) :
    (∏ p ∈ Q, (1 + q p * (1 - z p))) =
      ((∏ p ∈ Q, (1 - q p * z p)) / (∏ p ∈ Q, (1 - q p))) *
        ∏ p ∈ Q, (1 + localCorrection (q p) (z p)) := by
  calc
    _ = ∏ p ∈ Q, ((1 - q p * z p) / (1 - q p)) *
        (1 + localCorrection (q p) (z p)) := by
      apply Finset.prod_congr rfl
      intro p hp
      apply local_factorization
      · simpa only [mul_one] using local_denominator_ne_zero (hq p hp)
          (show ‖(1 : ℂ)‖ ≤ 1 by norm_num)
      · exact local_denominator_ne_zero (hq p hp) (hz p hp)
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_div_distrib]

/-- The literal prime features give a vanishing integrated allowance
for their paired local Euler corrections on every fixed closed half-plane. -/
theorem integral_norm_actual_pairedLocalSum_le_tail (Q : Finset ℕ)
    (h16 : ∀ p ∈ Q, 16 ≤ p) {sigma : ℝ} (hsigma : 1 / 2 < sigma)
    {s : ℂ} (hs : sigma ≤ s.re) (K : ℕ) (hK : ∀ p ∈ Q, K ≤ p) :
    (∫ xi : ℝ in Ioi 0,
      ‖pairedLocalSum Q (zetaPrimeFeature s) (fun p => Real.log p) xi / (xi : ℂ) ^ 2‖) ≤
      8 * Real.pi * ZetaPrimeNonlinearTail.squareLogTail sigma K := by
  have h := integral_norm_pairedLocalSum_div_le Q (zetaPrimeFeature s) (fun p => Real.log p)
    (fun p hp => ZetaSquarefreeSignedTail.norm_primeFeature_le_quarter
      (hsigma.trans_le hs).le (h16 p hp))
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp_rw [← ZetaPrimeNonlinearTail.squareLogWeight_eq]
  exact (Finset.sum_le_sum (fun p _hp =>
    ZetaPrimeNonlinearHalfplane.squareLogWeight_mono hs p)).trans
      (ZetaPrimeNonlinearTail.sum_squareLogWeight_le_tail Q hsigma K hK)

/-- One threshold pays all larger finite prime selections and all
heights in the closed half-plane for the paired local correction sum.
The full correction product, Euler quotient and original filter remain coupled. -/
theorem exists_uniform_actual_pairedLocalSum_lt {sigma : ℝ}
    (hsigma : 1 / 2 < sigma) {eps : ℝ} (heps : 0 < eps) :
    ∃ K : ℕ, 16 ≤ K ∧ ∀ (s : ℂ), sigma ≤ s.re → ∀ (Q : Finset ℕ),
      (∀ p ∈ Q, K ≤ p) →
        (∫ xi : ℝ in Ioi 0,
          ‖pairedLocalSum Q (zetaPrimeFeature s) (fun p => Real.log p) xi / (xi : ℂ) ^ 2‖) < eps := by
  have ht : Filter.Tendsto (fun K => 8 * Real.pi * ZetaPrimeNonlinearTail.squareLogTail sigma K)
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (ZetaPrimeNonlinearTail.tendsto_squareLogTail hsigma).const_mul (8 * Real.pi)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds heps))
  refine ⟨max 16 K, le_max_left _ _, ?_⟩
  intro s hs Q hQ
  have h16 (p : ℕ) (hp : p ∈ Q) : 16 ≤ p := (le_max_left _ _).trans (hQ p hp)
  exact (integral_norm_actual_pairedLocalSum_le_tail Q h16 hsigma hs (max 16 K) hQ).trans_lt
    (hK (max 16 K) (le_max_right _ _))


end
end RiemannGaussian.ZetaRieszEulerQuotient
