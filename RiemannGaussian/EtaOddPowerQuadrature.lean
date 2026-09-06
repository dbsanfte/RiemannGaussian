import RiemannGaussian.EtaCurrentMoebiusInverse

/-!
# Complex midpoint estimates for grouped inverse divisor weights

The inverse weights with a common divided cutoff must be summed as complex
numbers before taking norms. A positive-axis derivative estimate compares
their odd-index midpoint sum with its exact Mellin integral, retaining the
oscillatory power and its complex coefficient.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- Complex powers have an explicit Lipschitz bound above a positive
real base when the real exponent is at most one. -/
theorem norm_cpow_sub_cpow_le_above (r : ℂ) {a x y : ℝ} (ha : 0 < a)
    (hr : r.re ≤ 1) (hx : a ≤ x) (hy : a ≤ y) :
    ‖(y : ℂ) ^ r - (x : ℂ) ^ r‖ ≤ ‖r‖ * a ^ (r.re - 1) * |y - x| := by
  have hderiv (z : ℝ) (hz : z ∈ Ici a) :
      HasDerivWithinAt (fun t : ℝ ↦ (t : ℂ) ^ r)
        (r * (z : ℂ) ^ (r - 1)) (Ici a) z := by
    by_cases hr0 : r = 0
    · subst r
      simpa using (hasDerivAt_const (x := z) (c := (1 : ℂ))).hasDerivWithinAt
    · exact (hasDerivAt_ofReal_cpow_const (ne_of_gt (ha.trans_le hz)) hr0).hasDerivWithinAt
  have hbound (z : ℝ) (hz : z ∈ Ici a) :
      ‖r * (z : ℂ) ^ (r - 1)‖ ≤ ‖r‖ * a ^ (r.re - 1) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hz)]
    simp only [Complex.sub_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha hz (by linarith))
      (norm_nonneg _)
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Ici a) hx hy

/-- One odd midpoint differs from half its two-unit power integral by
at most the explicit derivative envelope at the common positive base. -/
theorem norm_cpow_midpoint_sub_half_integral_le (r : ℂ) {a x : ℝ}
    (ha : 0 < a) (hx : a ≤ x) (hr : r.re ≤ 1) :
    ‖((x + 1 : ℝ) : ℂ) ^ r - (∫ t : ℝ in x..x + 2, (t : ℂ) ^ r) / 2‖ ≤
      ‖r‖ * a ^ (r.re - 1) := by
  have hf : IntervalIntegrable (fun t : ℝ ↦ (t : ℂ) ^ r) volume x (x + 2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
    intro t ht
    rw [uIcc_of_le (by linarith : x ≤ x + 2)] at ht
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.1])
  have he : ((x + 1 : ℝ) : ℂ) ^ r - (∫ t : ℝ in x..x + 2, (t : ℂ) ^ r) / 2 =
      (∫ t : ℝ in x..x + 2, (((x + 1 : ℝ) : ℂ) ^ r - (t : ℂ) ^ r)) / 2 := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const hf, intervalIntegral.integral_const]
    rw [show x + 2 - x = 2 by ring, two_smul ℝ]
    ring
  have hnorm : ‖∫ t : ℝ in x..x + 2, (((x + 1 : ℝ) : ℂ) ^ r - (t : ℂ) ^ r)‖ ≤
      (‖r‖ * a ^ (r.re - 1)) * 2 := by
    calc
      _ ≤ (‖r‖ * a ^ (r.re - 1)) * |x + 2 - x| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro t ht
        rw [uIoc_of_le (by linarith : x ≤ x + 2)] at ht
        have h := norm_cpow_sub_cpow_le_above r ha hr (by linarith [ht.1] : a ≤ t) (by linarith : a ≤ x + 1)
        have hd : |x + 1 - t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.2], by linarith [ht.1]⟩
        exact h.trans (by nlinarith [mul_nonneg (norm_nonneg r) (Real.rpow_nonneg ha.le (r.re - 1))])
      _ = _ := by rw [show x + 2 - x = 2 by ring, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [he, norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by nlinarith)

/-- The literal odd-index power sum in the top half of cutoff `4*K`,
written at its arithmetic midpoints. -/
def pairedEtaOddTopPowerSum (rho : NontrivialZetaZero) (K : ℕ) : ℂ :=
  ∑ k ∈ Finset.range K, ((2 * K + 2 * k + 1 : ℕ) : ℂ) ^ (-rho.1)

/-- Grouping the odd inverse weights in the top half gives a complex
Mellin integral with an error gaining one full power of the physical scale. -/
theorem norm_pairedEtaOddTopPowerSum_sub_half_integral_le (rho : NontrivialZetaZero)
    {K : ℕ} (hK : 1 ≤ K) :
    ‖pairedEtaOddTopPowerSum rho K -
      (∫ t : ℝ in (2 * K : ℝ)..(4 * K : ℝ), (t : ℂ) ^ (-rho.1)) / 2‖ ≤
        (K : ℝ) * (‖rho.1‖ * (2 * K : ℝ) ^ (-rho.1.re - 1)) := by
  have hKp : (0 : ℝ) < K := by exact_mod_cast hK
  have hint (k : ℕ) (hk : k < K) : IntervalIntegrable
      (fun t : ℝ ↦ (t : ℂ) ^ (-rho.1)) volume
        (2 * K + 2 * k : ℝ) (2 * K + 2 * (k + 1) : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.cpow_const continuous_ofReal.continuousOn
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    exact Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.1, Nat.cast_nonneg (α := ℝ) k])
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ ↦ (2 * K + 2 * k : ℝ)) (n := K)
      (fun k hk ↦ by simpa only [Nat.cast_add, Nat.cast_one] using hint k hk)
  simp only [Nat.cast_zero, mul_zero, add_zero, show (2 * K + 2 * K : ℝ) = 4 * K by ring] at hsum
  rw [pairedEtaOddTopPowerSum, ← hsum, Finset.sum_div, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k ∈ Finset.range K,
        ‖((2 * K + 2 * k + 1 : ℕ) : ℂ) ^ (-rho.1) -
          (∫ t : ℝ in (2 * K + 2 * k : ℝ)..(2 * K + 2 * ((k + 1 : ℕ) : ℝ)), (t : ℂ) ^ (-rho.1)) / 2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range K, ‖rho.1‖ * (2 * K : ℝ) ^ (-rho.1.re - 1) := by
      apply Finset.sum_le_sum
      intro k hk
      have h := norm_cpow_midpoint_sub_half_integral_le (-rho.1)
        (by positivity : (0 : ℝ) < 2 * K)
        (by linarith [Nat.cast_nonneg (α := ℝ) k] : (2 * K : ℝ) ≤ 2 * K + 2 * k)
        (by simp only [Complex.neg_re]; linarith [NontrivialZetaZero.zero_lt_re rho])
      have hbase : ((2 * K + 2 * k + 1 : ℕ) : ℂ) = ((2 * K + 2 * k + 1 : ℝ) : ℂ) := by push_cast; rfl
      have hupper : (2 * K + 2 * ((k + 1 : ℕ) : ℝ) : ℝ) = 2 * K + 2 * k + 2 := by push_cast; ring
      rw [hbase, hupper]
      simpa only [norm_neg, Complex.neg_re] using h
    _ = _ := by simp

end

end RiemannGaussian
