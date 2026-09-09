/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RiemannXiCanonicalLogVariation

/-!
# Removing the mirror factors from the canonical xi expansion

An exact canonical factor contains its Cauchy pole and a mirror correction.
We keep that correction explicitly. After subtracting two evaluation points,
each correction is bounded by `4 * ‖s-w‖ / R²`. The actual multiplicity
count is `O(R^(3/2))`, so the complete correction vanishes. Together with
vanishing residual variation, this constructs the ordinary finite Cauchy
expansion limit for the genuine xi logarithmic derivative.
-/

open Complex Filter MeromorphicOn Metric Set Topology
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit mirror correction in a disk's canonical factor. -/
def xiCanonicalMirror (R : ℝ) (i z : ℂ) : ℂ :=
  starRingEnd ℂ i / ((R : ℂ) ^ 2 - starRingEnd ℂ i * z)

private lemma mirror_denominator_lower {R : ℝ} (hR : 0 < R) {i z : ℂ}
    (hi : ‖i‖ ≤ R) (hz : ‖z‖ ≤ R / 2) :
    R ^ 2 / 2 ≤ ‖(R : ℂ) ^ 2 - starRingEnd ℂ i * z‖ := by
  have hprod : ‖starRingEnd ℂ i * z‖ ≤ R ^ 2 / 2 := by
    rw [norm_mul, Complex.norm_conj]
    calc
      ‖i‖ * ‖z‖ ≤ R * (R / 2) :=
        mul_le_mul hi hz (norm_nonneg _) hR.le
      _ = R ^ 2 / 2 := by ring
  calc
    R ^ 2 / 2 ≤ R ^ 2 - ‖starRingEnd ℂ i * z‖ := by linarith
    _ = ‖(R : ℂ) ^ 2‖ - ‖starRingEnd ℂ i * z‖ := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    _ ≤ ‖(R : ℂ) ^ 2 - starRingEnd ℂ i * z‖ := norm_sub_norm_le _ _

/-- Exact signed difference of the two mirror evaluations, before any norm
estimate. Its numerator contains the extra inverse-radius cancellation. -/
theorem xiCanonicalMirror_sub {R : ℝ} (hR : 0 < R) {i s w : ℂ}
    (hi : ‖i‖ ≤ R) (hs : ‖s‖ ≤ R / 2) (hw : ‖w‖ ≤ R / 2) :
    xiCanonicalMirror R i s - xiCanonicalMirror R i w =
      (starRingEnd ℂ i) ^ 2 * (s - w) /
        (((R : ℂ) ^ 2 - starRingEnd ℂ i * s) *
          ((R : ℂ) ^ 2 - starRingEnd ℂ i * w)) := by
  have hds : (R : ℂ) ^ 2 - starRingEnd ℂ i * s ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < R ^ 2 / 2)
      (mirror_denominator_lower hR hi hs))
  have hdw : (R : ℂ) ^ 2 - starRingEnd ℂ i * w ≠ 0 :=
    norm_pos_iff.mp (lt_of_lt_of_le (by positivity : 0 < R ^ 2 / 2)
      (mirror_denominator_lower hR hi hw))
  unfold xiCanonicalMirror
  field_simp
  ring

/-- Every mirror difference is uniformly of inverse-square order, including
its dependence on the separation of the two evaluation points. -/
theorem norm_xiCanonicalMirror_sub_le {R : ℝ} (hR : 0 < R) {i s w : ℂ}
    (hi : ‖i‖ ≤ R) (hs : ‖s‖ ≤ R / 2) (hw : ‖w‖ ≤ R / 2) :
    ‖xiCanonicalMirror R i s - xiCanonicalMirror R i w‖ ≤
      4 * ‖s - w‖ / R ^ 2 := by
  rw [xiCanonicalMirror_sub hR hi hs hw, norm_div, norm_mul, norm_mul,
    norm_pow, Complex.norm_conj]
  calc
    ‖i‖ ^ 2 * ‖s - w‖ /
        (‖(R : ℂ) ^ 2 - starRingEnd ℂ i * s‖ *
          ‖(R : ℂ) ^ 2 - starRingEnd ℂ i * w‖)
      ≤ R ^ 2 * ‖s - w‖ / ((R ^ 2 / 2) * (R ^ 2 / 2)) := by
        gcongr
        · exact mirror_denominator_lower hR hi hs
        · exact mirror_denominator_lower hR hi hw
    _ = 4 * ‖s - w‖ / R ^ 2 := by field_simp; ring

/-- The complete multiplicity-weighted canonical mirror difference. -/
def riemannXiCanonicalMirrorDifference (n : ℕ) (s w : ℂ) : ℂ :=
  ∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i •
    (xiCanonicalMirror (xiCanonicalRadius n) i s -
      xiCanonicalMirror (xiCanonicalRadius n) i w)

/-- The full mirror correction retains the actual divisor multiplicities
and is bounded by the proved three-halves count times its inverse-square gain. -/
theorem norm_riemannXiCanonicalMirrorDifference_le_of_threeHalves_growth
    {A : ℝ} (hA : 1 ≤ A)
    (hbound : ∀ z : ℂ,
      ‖riemannXi z‖ ≤ Real.exp (A * (‖z‖ + 1) ^ (3 / 2 : ℝ)))
    (n : ℕ) {s w : ℂ}
    (hs : ‖s‖ ≤ xiCanonicalRadius n / 2)
    (hw : ‖w‖ ≤ xiCanonicalRadius n / 2) :
    ‖riemannXiCanonicalMirrorDifference n s w‖ ≤
      (A * (2 * xiCanonicalRadius n + 1) ^ (3 / 2 : ℝ) / Real.log 2) *
        (4 * ‖s - w‖ / xiCanonicalRadius n ^ 2) := by
  have hdFinite : (Function.support fun i =>
      divisor riemannXi (ball 0 (xiCanonicalRadius n)) i).Finite :=
    (riemannXiCanonicalResidual_decomp n).meromorphicOn.divisor_ball_support_finite
  have hraw := norm_finsum_zsmul_le_of_nonneg hdFinite
    (fun i => (analyticOnNhd_riemannXi.mono (subset_univ _)).divisor_nonneg i)
    (fun i hi => norm_xiCanonicalMirror_sub_le (xiCanonicalRadius_pos n)
      (show ‖i‖ ≤ xiCanonicalRadius n from le_of_lt (by
        simpa only [mem_ball, dist_zero_right] using
          (divisor riemannXi (ball 0 (xiCanonicalRadius n))).supportWithinDomain hi)) hs hw)
  exact hraw.trans (mul_le_mul_of_nonneg_right
    (sum_divisor_riemannXi_ball_le_threeHalves_of_growth hA hbound n) (by positivity))

/-- The actual full canonical mirror difference tends to zero at any two
fixed complex points; no zero-location conjecture enters the estimate. -/
theorem tendsto_riemannXiCanonicalMirrorDifference (s w : ℂ) :
    Tendsto (fun n => riemannXiCanonicalMirrorDifference n s w) atTop (𝓝 0) := by
  obtain ⟨A, hA, hbound⟩ := riemannXi_threeHalvesGrowth
  have hdecay := (tendsto_affine_threeHalves_div_xiCanonicalRadius_sq
    (a := 2) (b := 1) (by norm_num) (by norm_num)).const_mul
      (4 * A * ‖s - w‖ / Real.log 2)
  simp only [mul_zero] at hdecay
  refine squeeze_zero_norm' ?_ hdecay
  filter_upwards [tendsto_xiCanonicalRadius_atTop.eventually
    (eventually_ge_atTop (2 * max ‖s‖ ‖w‖))] with n hn
  have hs : ‖s‖ ≤ xiCanonicalRadius n / 2 := by
    have := le_max_left ‖s‖ ‖w‖
    linarith
  have hw : ‖w‖ ≤ xiCanonicalRadius n / 2 := by
    have := le_max_right ‖s‖ ‖w‖
    linarith
  convert norm_riemannXiCanonicalMirrorDifference_le_of_threeHalves_growth
    hA hbound n hs hw using 1
  ring

/-- The ordinary multiplicity-weighted Cauchy differences over the complete
xi divisor enclosed by the canonical disk. -/
def riemannXiCanonicalCauchyDifference (n : ℕ) (s w : ℂ) : ℂ :=
  ∑ᶠ i, divisor riemannXi (ball 0 (xiCanonicalRadius n)) i •
    (1 / (s - i) - 1 / (w - i))

/-- Exact finite expansion of a xi logarithmic-derivative difference. Both
analytic and mirror remainders remain visible, with their original signs. -/
theorem logDeriv_riemannXi_sub_eq_canonicalCauchy_add_remainders
    (n : ℕ) {s w : ℂ}
    (hs : s ∈ ball 0 (xiCanonicalRadius n))
    (hw : w ∈ ball 0 (xiCanonicalRadius n))
    (hxis : riemannXi s ≠ 0) (hxiw : riemannXi w ≠ 0) :
    logDeriv riemannXi s - logDeriv riemannXi w =
      (logDeriv (riemannXiCanonicalResidual n) s -
        logDeriv (riemannXiCanonicalResidual n) w) +
      riemannXiCanonicalMirrorDifference n s w +
      riemannXiCanonicalCauchyDifference n s w := by
  classical
  let R := xiCanonicalRadius n
  let d : ℂ → ℤ := fun i => divisor riemannXi (ball 0 R) i
  have hdFinite : (Function.support d).Finite :=
    (riemannXiCanonicalResidual_decomp n).meromorphicOn.divisor_ball_support_finite
  let S := hdFinite.toFinset
  have hsum (f : ℂ → ℂ) : (∑ᶠ i, d i • f i) = ∑ i ∈ S, d i • f i := by
    apply finsum_eq_sum_of_support_subset
    intro i hi
    apply hdFinite.mem_toFinset.mpr
    intro hdi
    exact hi (by simp [hdi])
  have hfactor :
      (∑ i ∈ S, d i • logDeriv (Complex.canonicalFactor R i) s) -
        (∑ i ∈ S, d i • logDeriv (Complex.canonicalFactor R i) w) =
      -(∑ i ∈ S, d i • (xiCanonicalMirror R i s - xiCanonicalMirror R i w)) -
        (∑ i ∈ S, d i • (1 / (s - i) - 1 / (w - i))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hdi : d i ≠ 0 := hdFinite.mem_toFinset.mp hi
    have hiBall : i ∈ ball (0 : ℂ) R :=
      (divisor riemannXi (ball 0 R)).supportWithinDomain hdi
    have hzero : riemannXi i = 0 := riemannXi_eq_zero_of_divisor_ball_ne_zero hdi
    have hsi : s ≠ i := fun heq => hxis (heq ▸ hzero)
    have hwi : w ≠ i := fun heq => hxiw (heq ▸ hzero)
    rw [logDeriv_canonicalFactor_eq (xiCanonicalRadius_pos n) hiBall
        (ball_subset_closedBall hs) hsi,
      logDeriv_canonicalFactor_eq (xiCanonicalRadius_pos n) hiBall
        (ball_subset_closedBall hw) hwi]
    simp only [xiCanonicalMirror, neg_div, smul_sub, smul_neg]
    abel
  rw [logDeriv_riemannXi_eq_residual_sub_canonical_sum n hs hxis,
    logDeriv_riemannXi_eq_residual_sub_canonical_sum n hw hxiw]
  change (_ - ∑ᶠ i, d i • _) - (_ - ∑ᶠ i, d i • _) =
    _ + (∑ᶠ i, d i • _) + ∑ᶠ i, d i • _
  rw [hsum, hsum, hsum, hsum]
  linear_combination -hfactor

/-- The genuine xi logarithmic-derivative difference is the limit of its
ordinary finite Cauchy differences. All analytic and mirror errors have
been proved to vanish independently. -/
theorem tendsto_riemannXiCanonicalCauchyDifference {s w : ℂ}
    (hs : riemannXi s ≠ 0) (hw : riemannXi w ≠ 0) :
    Tendsto (fun n => riemannXiCanonicalCauchyDifference n s w) atTop
      (𝓝 (logDeriv riemannXi s - logDeriv riemannXi w)) := by
  have ht := ((tendsto_const_nhds (x := logDeriv riemannXi s - logDeriv riemannXi w)).sub
    (tendsto_logDeriv_riemannXiCanonicalResidual_sub s w)).sub
    (tendsto_riemannXiCanonicalMirrorDifference s w)
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [tendsto_xiCanonicalRadius_atTop.eventually
    (eventually_gt_atTop (max ‖s‖ ‖w‖))] with n hn
  have hsball : s ∈ ball 0 (xiCanonicalRadius n) := by
    rw [mem_ball, dist_zero_right]
    exact (le_max_left _ _).trans_lt hn
  have hwball : w ∈ ball 0 (xiCanonicalRadius n) := by
    rw [mem_ball, dist_zero_right]
    exact (le_max_right _ _).trans_lt hn
  have heq := logDeriv_riemannXi_sub_eq_canonicalCauchy_add_remainders n hsball hwball hs hw
  linear_combination heq

end

end RiemannGaussian
