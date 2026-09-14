/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovCoarseCongruence
import RiemannGaussian.VinogradovShiftedMoment

/-!
# Exact affine transport of complete Vinogradov moments

The complete weighted integer moment vector is invariant under common
nonzero integer dilation and translation. Its exact collision set and
complex weighted homogeneous Gram coefficient are retained before bounding
any shifted coefficient. Actual arithmetic progressions therefore use the
literal Vinogradov mean value at their normalized length, with an explicit
all-order elementary bound available downstream.
-/

namespace RiemannGaussian.VinogradovAffineMoment
noncomputable section
open scoped BigOperators
open VinogradovCoarseCongruence

/-- Every weighted homogeneous moment equation is unchanged by a common
integer affine transformation with nonzero scale. The full vector and
original weights are retained, including repeated entries. -/
theorem weighted_affine_equal_iff {r k : ℕ} (c u v : Fin r → ℤ) {q : ℤ}
    (hq : q ≠ 0) (xi : ℤ) :
    (∀ n, 1 ≤ n → n ≤ k →
      (∑ i, c i * (q * u i + xi) ^ n) = ∑ i, c i * (q * v i + xi) ^ n) ↔
    (∀ n, 1 ≤ n → n ≤ k →
      (∑ i, c i * u i ^ n) = ∑ i, c i * v i ^ n) := by
  constructor
  · intro h n hn hnk
    have ht := translated_power_difference_dvd c
      (fun i => q * v i + xi) (fun i => q * u i + xi) xi 0 (n := n) (by
        intro d hd hdn
        rw [h d hd (hdn.trans hnk), sub_self])
    simp only [add_sub_cancel_right, scaled_power_difference, zero_dvd_iff] at ht
    exact sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_left (pow_ne_zero n hq))
  · intro h n hn hnk
    have ht := translated_power_difference_dvd c
      (fun i => q * v i) (fun i => q * u i) (-xi) 0 (n := n) (by
        intro d hd hdn
        rw [scaled_power_difference, h d hd (hdn.trans hnk), sub_self, mul_zero])
    simpa only [sub_neg_eq_add, zero_dvd_iff, sub_eq_zero] using ht

/-- Equality of the complete frequency vector is exactly equality of
all the retained positive-degree integer moments. -/
theorem frequency_sum_eq_iff {r k : ℕ} (u v : Fin r → ℤ) :
    (∑ i, VinogradovPowerSumRigidity.integerFrequency k (u i)) =
      (∑ i, VinogradovPowerSumRigidity.integerFrequency k (v i)) ↔
    ∀ n, 1 ≤ n → n ≤ k → (∑ i, u i ^ n) = ∑ i, v i ^ n := by
  constructor
  · intro h n hn hnk
    have he := congrFun h ⟨n - 1, by omega⟩
    simpa only [Finset.sum_apply, VinogradovPowerSumRigidity.integerFrequency,
      Nat.sub_add_cancel hn] using he
  · intro h
    funext i
    simpa only [Finset.sum_apply, VinogradovPowerSumRigidity.integerFrequency] using
      h (i.val + 1) (by omega) (by omega)

/-- Common nondegenerate affine changes preserve every complete tuple
collision, without requiring distinct entries. -/
theorem affine_frequency_collision_iff {r k : ℕ} (u v : Fin r → ℤ)
    {q : ℤ} (hq : q ≠ 0) (xi : ℤ) :
    (∑ i, VinogradovPowerSumRigidity.integerFrequency k (q * u i + xi)) =
      (∑ i, VinogradovPowerSumRigidity.integerFrequency k (q * v i + xi)) ↔
    (∑ i, VinogradovPowerSumRigidity.integerFrequency k (u i)) =
      (∑ i, VinogradovPowerSumRigidity.integerFrequency k (v i)) := by
  rw [frequency_sum_eq_iff, frequency_sum_eq_iff]
  simpa only [one_mul] using weighted_affine_equal_iff (fun _ => 1) u v hq xi

/-- The exact even torus moment of any finite integer family is invariant
under every common nonzero integer dilation and integer translation. -/
theorem moment_affine {ι : Type*} [Fintype ι] (r k : ℕ) (v : ι → ℤ)
    {q : ℤ} (hq : q ≠ 0) (xi : ℤ) :
    VinogradovMeanValue.moment r (fun i => VinogradovPowerSumRigidity.integerFrequency k (q * v i + xi)) =
      VinogradovMeanValue.moment r (fun i => VinogradovPowerSumRigidity.integerFrequency k (v i)) := by
  classical
  rw [VinogradovMeanValue.moment_eq_collisionCount, VinogradovMeanValue.moment_eq_collisionCount]
  congr 1
  unfold VinogradovMeanValue.collisionCount
  congr 1
  ext xy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    affine_frequency_collision_iff (fun i => v (xy.1 i)) (fun i => v (xy.2 i)) hq xi]

/-- Every shifted complete moment system on an arbitrary integer
arithmetic progression is bounded by the literal unshifted Vinogradov
mean value at its normalized length. This controls each fixed tail target. -/
theorem affine_shift_le_meanValue (r k N : ℕ) {q : ℤ} (hq : q ≠ 0)
    (xi : ℤ) (h : Fin k → ℤ) :
    (VinogradovShiftedMoment.differenceCount
      (VinogradovShiftedMoment.tupleFrequency r (fun i : Fin N =>
        VinogradovPowerSumRigidity.integerFrequency k (q * ((i.val + 1 : ℕ) : ℤ) + xi))) h : ℝ) ≤
      VinogradovMeanValue.meanValue r k N := by
  have hb := VinogradovShiftedMoment.tuple_differenceCount_le_moment r
    (fun i : Fin N => VinogradovPowerSumRigidity.integerFrequency k
      (q * ((i.val + 1 : ℕ) : ℤ) + xi)) h
  rw [moment_affine r k (fun i : Fin N => ((i.val + 1 : ℕ) : ℤ)) hq xi] at hb
  exact hb

/-- The shifted progression count also has an unconditional explicit
base estimate at every tuple order, with no mean-value premise. -/
theorem affine_shift_explicit_le (r k N : ℕ) {q : ℤ} (hq : q ≠ 0)
    (xi : ℤ) (h : Fin k → ℤ) :
    (VinogradovShiftedMoment.differenceCount
      (VinogradovShiftedMoment.tupleFrequency r (fun i : Fin N =>
        VinogradovPowerSumRigidity.integerFrequency k (q * ((i.val + 1 : ℕ) : ℤ) + xi))) h : ℝ) ≤
      (Nat.factorial (min r k) : ℝ) * (N : ℝ) ^ (2 * r - min r k) :=
  (affine_shift_le_meanValue r k N hq xi h).trans
    (by simpa only [mul_comm] using VinogradovPowerSumRigidity.meanValue_le_all r k N)

/-- Affine moment invariance retains every complex tuple-weight product
in the exact homogeneous Gram coefficient, before any norm is taken. -/
theorem weighted_gram_affine {ι : Type*} [Fintype ι] (r k : ℕ) (v : ι → ℤ)
    (w : ι → ℂ) {q : ℤ} (hq : q ≠ 0) (xi : ℤ) :
    VinogradovShiftedMoment.weightedShift
      (VinogradovShiftedMoment.tupleFrequency r (fun i =>
        VinogradovPowerSumRigidity.integerFrequency k (q * v i + xi)))
      (VinogradovShiftedMoment.tupleWeight r w) 0 =
    VinogradovShiftedMoment.weightedShift
      (VinogradovShiftedMoment.tupleFrequency r (fun i =>
        VinogradovPowerSumRigidity.integerFrequency k (v i)))
      (VinogradovShiftedMoment.tupleWeight r w) 0 := by
  classical
  simp only [VinogradovShiftedMoment.weightedShift, VinogradovShiftedMoment.tupleFrequency,
    add_zero, affine_frequency_collision_iff _ _ hq xi]

/-- Every bounded complex weight family on the actual progression has
its shifted tuple Gram coefficient controlled by the normalized mean value.
The complete weighted coefficient remains available before this norm bound. -/
theorem weighted_affine_shift_le_meanValue (r k N : ℕ) (w : Fin N → ℂ)
    (hw : ∀ i, ‖w i‖ ≤ 1) {q : ℤ} (hq : q ≠ 0) (xi : ℤ) (h : Fin k → ℤ) :
    ‖VinogradovShiftedMoment.weightedShift
      (VinogradovShiftedMoment.tupleFrequency r (fun i : Fin N =>
        VinogradovPowerSumRigidity.integerFrequency k (q * ((i.val + 1 : ℕ) : ℤ) + xi)))
      (VinogradovShiftedMoment.tupleWeight r w) h‖ ≤
      VinogradovMeanValue.meanValue r k N :=
  (VinogradovShiftedMoment.weightedShift_norm_le_count _ _
    (VinogradovShiftedMoment.tupleWeight_norm_le_one r w hw) h).trans
      (affine_shift_le_meanValue r k N hq xi h)

end
end RiemannGaussian.VinogradovAffineMoment
