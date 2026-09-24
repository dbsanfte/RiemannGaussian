/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRectangleTails

/-!
# Paying every literal mask error in the allocation-safe rectangle

The geometric error is uniform in height. It does not use exposed-zero
phases, replace the composite cofactor, or assert positivity of a surrogate.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszWideOwnerAudit ZetaRieszAnnulusJoint ZetaRieszPrimeCountFrequency

/-- The exact positive product majorant on the three separate prime legs. -/
def rectangleWeight (a : ℕ × ℕ × ℕ) : ℝ :=
  zetaPrimeExpWeight (1 + 1 / 262144) a.1 *
    zetaPrimeExpWeight (1 + 1 / 262144) a.2.1 *
      zetaPrimeExpWeight (1 + 1 / 262144) a.2.2

/-- Its finite physical sum is bounded by an actual convergent series. -/
theorem rectangleWeight_sum_le (u : ℝ) (N : ℕ) :
    (∑ a ∈ rectangleCube u N, rectangleWeight a) ≤
      (∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n) ^ 3 := by
  have h := (summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ) < 1 + 1 / 262144)).sum_le_tsum
    (intermediatePrimes u N) (fun n _ => (Real.exp_pos _).le)
  have hpos : 0 ≤ ∑ n ∈ intermediatePrimes u N, zetaPrimeExpWeight (1 + 1 / 262144) n :=
    Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  calc
    _ = (∑ n ∈ intermediatePrimes u N, zetaPrimeExpWeight (1 + 1 / 262144) n) ^ 3 := by
      simp only [rectangleCube, Finset.sum_product, rectangleWeight, pow_succ, pow_zero,
        one_mul, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ ≤ _ := pow_le_pow_left₀ hpos h 3

/-- Every actual failed mask is covered by the five leg tails or one
of the original total-window tails. -/
theorem rectangle_bad_kernel_bound (t : ℕ) (ht : 32 ≤ t) {u : ℝ}
    (hu : 1 / 2 < u) (huU : u ≤ radiusCeiling)
    (hL : (11 / 8 : ℝ) * dyadicMomentOrder t ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder t))
    {a : ℕ × ℕ × ℕ} (ha : a ∈ rectangleCube u (dyadicMomentOrder t))
    (hbad : ¬ rectangleLiteralMask u (dyadicMomentOrder t) (dyadicPrimeCount t) a)
    (y : ℝ) {j h : ℕ} (hj : j < dyadicMomentOrder t + 2)
    (hh : h ∈ rectangleOrders (dyadicMomentOrder t) j) :
    ‖rectangleKernel y (dyadicMomentOrder t) j h a‖ ≤
      (dyadicMomentOrder t + 2 : ℝ) * rectangleTilt⁻¹ ^ (dyadicMomentOrder t + 2) *
        Real.exp (1 - (dyadicMomentOrder t : ℝ) / 4000) * rectangleWeight a := by
  by_cases hb : rectangleLogBox (dyadicMomentOrder t) a.1 a.2.1 a.2.2
  · have hw : ¬ ((39 / 20 : ℝ) * dyadicMomentOrder t < Real.log (a.1 * (a.2.1 * a.2.2) : ℕ) ∧
        Real.log (a.1 * (a.2.1 * a.2.2) : ℕ) ≤ (41 / 20 : ℝ) * dyadicMomentOrder t) :=
      fun hw => hbad (rectangleLiteralMask_of_good t ht hu huU hL ha hb hw)
    obtain ⟨hp, hqr⟩ := Finset.mem_product.mp ha
    obtain ⟨hq, hr⟩ := Finset.mem_product.mp hqr
    exact rectangle_bad_total_bound hj hh y a
      ((mem_intermediatePrimes _ _ _).mp hp).1.pos
      ((mem_intermediatePrimes _ _ _).mp hq).1.pos
      ((mem_intermediatePrimes _ _ _).mp hr).1.pos hw
  · exact rectangle_bad_leg_bound hj hh y a hb

private theorem rectangleOrders_card_le (N j : ℕ) : (rectangleOrders N j).card ≤ N + 2 := by
  calc
    _ ≤ (Finset.range (N + 1 - j + 1)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ _ := by simp only [Finset.card_range]; omega

/-- Summing only the exceptional factorial terms costs a fixed polynomial
in N, while retaining the strict geometric saving. -/
theorem rectangle_bad_atom_bound (t : ℕ) (ht : 32 ≤ t) {u : ℝ}
    (hu : 1 / 2 < u) (huU : u ≤ radiusCeiling)
    (hL : (11 / 8 : ℝ) * dyadicMomentOrder t ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder t))
    {a : ℕ × ℕ × ℕ} (ha : a ∈ rectangleCube u (dyadicMomentOrder t))
    (hbad : ¬ rectangleLiteralMask u (dyadicMomentOrder t) (dyadicPrimeCount t) a)
    (y : ℝ) :
    ‖rectangleCubeAtom u y (dyadicMomentOrder t) a‖ ≤
      (dyadicMomentOrder t + 1 : ℝ) * (dyadicMomentOrder t + 2 : ℝ) ^ 3 *
        rectangleTilt⁻¹ ^ (dyadicMomentOrder t + 2) *
          Real.exp (1 - (dyadicMomentOrder t : ℝ) / 4000) * rectangleWeight a := by
  let N := dyadicMomentOrder t
  let B : ℝ := (N + 2 : ℝ) * rectangleTilt⁻¹ ^ (N + 2) *
    Real.exp (1 - (N : ℝ) / 4000) * rectangleWeight a
  have hB : 0 ≤ B := by dsimp [B, rectangleTilt, rectangleWeight, zetaPrimeExpWeight]; positivity
  have hinner (j : ℕ) (hj : j < N + 2) :
      ‖∑ h ∈ rectangleOrders N j, rectangleKernel y N j h a‖ ≤ (N + 2 : ℝ) * B := by
    apply (norm_sum_le _ _).trans
    have hs := Finset.sum_le_sum (fun h hh => rectangle_bad_kernel_bound t ht hu huU hL ha hbad y hj hh)
    change (∑ h ∈ rectangleOrders N j, _) ≤ ∑ _h ∈ rectangleOrders N j, B at hs
    simp only [Finset.sum_const, nsmul_eq_mul] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast rectangleOrders_card_le N j) hB)
  have hsum : ‖∑ j ∈ Finset.range (N + 2), ∑ h ∈ rectangleOrders N j,
      rectangleKernel y N j h a‖ ≤ (N + 2 : ℝ) ^ 2 * B := by
    apply (norm_sum_le _ _).trans
    have hs := Finset.sum_le_sum (fun j hj => hinner j (Finset.mem_range.mp hj))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_ofNat, pow_two, mul_assoc] using hs
  have hLone := ZetaRieszHeadOrders.one_le_length u N
  have hpref : ‖((N + 1 : ℕ) : ℂ) / (SquarefreeVaughanLogSource.length u N : ℂ)‖ ≤ N + 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg (SquarefreeVaughanLogSource.length_pos u N).le]
    push_cast
    exact div_le_self (by positivity : (0 : ℝ) ≤ N + 1) hLone
  rw [rectangleCubeAtom, norm_mul]
  exact (mul_le_mul hpref hsum (norm_nonneg _) (by positivity)).trans_eq (by dsimp [B]; ring)

/-- Uniform finite mask error before applying the source normalization. -/
theorem rectangleMaskError_bound (t : ℕ) (ht : 32 ≤ t) {u : ℝ}
    (hu : 1 / 2 < u) (huU : u ≤ radiusCeiling)
    (hL : (11 / 8 : ℝ) * dyadicMomentOrder t ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder t)) (y : ℝ) :
    ‖rectangleMaskError u y (dyadicMomentOrder t) (dyadicPrimeCount t)‖ ≤
      (dyadicMomentOrder t + 1 : ℝ) * (dyadicMomentOrder t + 2 : ℝ) ^ 3 *
        rectangleTilt⁻¹ ^ (dyadicMomentOrder t + 2) *
          Real.exp (1 - (dyadicMomentOrder t : ℝ) / 4000) *
            (∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n) ^ 3 := by
  let N := dyadicMomentOrder t
  let B := (N + 1 : ℝ) * (N + 2 : ℝ) ^ 3 * rectangleTilt⁻¹ ^ (N + 2) *
    Real.exp (1 - (N : ℝ) / 4000)
  have hB : 0 ≤ B := by dsimp [B, rectangleTilt]; positivity
  unfold rectangleMaskError
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ (rectangleCube u N).filter (fun a =>
        ¬ rectangleLiteralMask u N (dyadicPrimeCount t) a), B * rectangleWeight a := by
      apply Finset.sum_le_sum
      intro a ha
      exact rectangle_bad_atom_bound t ht hu huU hL (Finset.mem_filter.mp ha).1
        (Finset.mem_filter.mp ha).2 y
    _ ≤ ∑ a ∈ rectangleCube u N, B * rectangleWeight a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ => mul_nonneg hB (by unfold rectangleWeight zetaPrimeExpWeight; positivity))
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (rectangleWeight_sum_le u N) hB

private theorem normalized_mask_scalar (N : ℕ) {u : ℝ} (hu : 0 ≤ u) (huU : u ≤ radiusCeiling) :
    u ^ (N + 1) * ((N + 1 : ℝ) * (N + 2 : ℝ) ^ 3 *
      rectangleTilt⁻¹ ^ (N + 2) * Real.exp (1 - (N : ℝ) / 4000)) ≤
    (8 * radiusCeiling * rectangleTilt⁻¹ ^ 2 * Real.exp 1) *
      (N + 1 : ℝ) ^ 4 * rectangleMaskRate ^ N := by
  have hd : 0 < rectangleTilt := by norm_num [rectangleTilt]
  have hp : (N + 1 : ℝ) * (N + 2 : ℝ) ^ 3 ≤ 8 * (N + 1 : ℝ) ^ 4 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ N + 2)
      (show (N + 2 : ℝ) ≤ 2 * (N + 1) by linarith [Nat.cast_nonneg (α := ℝ) N]) 3
    have hh := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ N + 1 by positivity)
    nlinarith only [hh]
  have he : radiusCeiling ^ (N + 1) * rectangleTilt⁻¹ ^ (N + 2) *
      Real.exp (1 - (N : ℝ) / 4000) =
    radiusCeiling * rectangleTilt⁻¹ ^ 2 * Real.exp 1 * rectangleMaskRate ^ N := by
    rw [show 1 - (N : ℝ) / 4000 = 1 + (N : ℝ) * (-(1 / 4000 : ℝ)) by ring,
      Real.exp_add, Real.exp_nat_mul]
    simp only [rectangleMaskRate, div_eq_mul_inv, mul_pow, pow_add, pow_one]
    ring
  calc
    _ ≤ radiusCeiling ^ (N + 1) * ((N + 1 : ℝ) * (N + 2 : ℝ) ^ 3 *
        rectangleTilt⁻¹ ^ (N + 2) * Real.exp (1 - (N : ℝ) / 4000)) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu huU _) (by positivity)
    _ = ((N + 1 : ℝ) * (N + 2 : ℝ) ^ 3) *
        (radiusCeiling ^ (N + 1) * rectangleTilt⁻¹ ^ (N + 2) *
          Real.exp (1 - (N : ℝ) / 4000)) := by ring
    _ ≤ (8 * (N + 1 : ℝ) ^ 4) *
        (radiusCeiling * rectangleTilt⁻¹ ^ 2 * Real.exp 1 * rectangleMaskRate ^ N) := by
      rw [he]
      exact mul_le_mul_of_nonneg_right hp (by
        have := rectangleMaskRate_bounds.1
        unfold radiusCeiling
        positivity)
    _ = _ := by ring

/-- Every literal mask failure vanishes at the original source scale,
uniformly in arbitrary moving heights. No zero hypothesis is used. -/
theorem tendsto_rectangleMaskError (y : ℕ → ℝ) {u : ℝ}
    (hu : 1 / 2 < u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun t => (u : ℂ) ^ (dyadicMomentOrder t + 1) *
      rectangleMaskError u (y t) (dyadicMomentOrder t) (dyadicPrimeCount t)) atTop (𝓝 0) := by
  let C : ℝ := (8 * radiusCeiling * rectangleTilt⁻¹ ^ 2 * Real.exp 1) *
    (∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n) ^ 3
  have hlim := ((ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 4
    (by unfold rectangleMaskRate rectangleTilt radiusCeiling; positivity)
    rectangleMaskRate_bounds.2).const_mul C).comp tendsto_dyadicMomentOrder
  simp only [mul_zero, Function.comp_def] at hlim
  apply squeeze_zero_norm' (a := fun t => C *
    ((dyadicMomentOrder t + 1 : ℝ) ^ 4 * rectangleMaskRate ^ dyadicMomentOrder t)) ?_ hlim
  have hlength := (ZetaRieszLowerDegreeBounds.eventually_length_ge_exponent
    (show 0 < u by linarith) (by norm_num : (0 : ℝ) ≤ 11 / 16)
      (huU.trans_lt radius_lt_source))
  filter_upwards [tendsto_dyadicMomentOrder.eventually hlength, eventually_ge_atTop 32] with t hL ht
  have hL' : (11 / 8 : ℝ) * dyadicMomentOrder t ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder t) := by nlinarith
  have hb := rectangleMaskError_bound t ht hu huU hL' (y t)
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ u)]
  apply (mul_le_mul_of_nonneg_left hb (pow_nonneg (by linarith : 0 ≤ u) _)).trans
  have hZ : 0 ≤ (∑' n, zetaPrimeExpWeight (1 + 1 / 262144) n) ^ 3 :=
    pow_nonneg (tsum_nonneg (fun _ => (Real.exp_pos _).le)) 3
  have hs := mul_le_mul_of_nonneg_right (normalized_mask_scalar (dyadicMomentOrder t)
    (show 0 ≤ u by linarith) huU)
      hZ
  dsimp only [C]
  convert hs using 1 <;> ring

/-- The separate prime-leg rectangle and the literal unassigned
rectangle differ by o(1). Both the old allocation and every original
mask failure have now been paid independently. -/
theorem tendsto_separate_sub_rectangle (y : ℕ → ℝ) {u : ℝ}
    (hu : 1 / 2 < u) (huU : u ≤ radiusCeiling) :
    Tendsto (fun t => (u : ℂ) ^ (dyadicMomentOrder t + 1) *
      (separatePrimeRectangle u (y t) (dyadicMomentOrder t) -
        rectangleResponse u (y t) (dyadicMomentOrder t) (dyadicPrimeCount t))) atTop (𝓝 0) := by
  have h := (tendsto_raw_sub_rectangle y (show 0 ≤ u by linarith) huU).add
    (tendsto_rectangleMaskError y hu huU)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 32] with t ht
  rw [separatePrimeRectangle_eq t ht]
  ring

end
end RiemannGaussian.ZetaRieszSkewAllocation
