/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovMeanValue

/-!
# Shifted frequency correlations and even-moment majorants

The full complex weighted correlation at an arbitrary integer frequency
shift is a Fourier coefficient of a nonnegative density. Its norm is at
most the zero-frequency coefficient. Consequently every shifted
equal-power-sum system has at most as many solutions as the homogeneous
system, with every frequency coordinate retained.

This is the zero-right-hand-side domination used in Ford's Vinogradov
argument (Lemma 5.1, Proposition ZRD). It does not estimate the homogeneous
Vinogradov mean value quantitatively.
-/

namespace RiemannGaussian.VinogradovShiftedMoment
noncomputable section
open MeasureTheory UnitAddTorus VinogradovMeanValue
open scoped BigOperators ComplexConjugate

/-- Use the normalized Haar measure from the multivariate Fourier library. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The chosen circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

variable {d ι : Type*} [Fintype d] [Fintype ι]

/-- The full weighted complex Gram coefficient at an integer vector shift. -/
def weightedShift (v : ι → d → ℤ) (w : ι → ℂ) (h : d → ℤ) : ℂ := by
  classical
  exact ∑ i, ∑ j, if v i = v j + h then w i * conj (w j) else 0

/-- Ordered frequency pairs at a prescribed difference vector. -/
def differenceCount (v : ι → d → ℤ) (h : d → ℤ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p : ι × ι => v p.1 = v p.2 + h)).card

/-- Every multivariate Fourier monomial has pointwise unit modulus. -/
theorem norm_mFourier_apply (h : d → ℤ) (θ : UnitAddTorus d) :
    ‖mFourier h θ‖ = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk, fourier_apply, norm_prod,
    Circle.norm_coe, Finset.prod_const_one]

/-- Fourier orthogonality identifies the entire shifted weighted Gram
coefficient, including every matching-frequency cross term. -/
theorem weightedShift_eq_integral (v : ι → d → ℤ) (w : ι → ℂ) (h : d → ℤ) :
    weightedShift v w h = ∫ θ : UnitAddTorus d,
      (∑ i, w i * mFourier (v i) θ) * conj (∑ j, w j * mFourier (v j) θ) *
        conj (mFourier h θ) := by
  classical
  have hi (i j : ι) : Integrable (fun θ : UnitAddTorus d =>
      (w i * conj (w j)) * (mFourier (v i) θ * conj (mFourier (v j + h) θ))) := by
    apply Continuous.integrable_of_hasCompactSupport (by fun_prop)
    exact HasCompactSupport.of_compactSpace _
  have he (θ : UnitAddTorus d) :
      (∑ i, w i * mFourier (v i) θ) * conj (∑ j, w j * mFourier (v j) θ) *
        conj (mFourier h θ) =
      ∑ i, ∑ j, (w i * conj (w j)) *
        (mFourier (v i) θ * conj (mFourier (v j + h) θ)) := by
    simp only [mFourier_add, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi'
    apply Finset.sum_congr rfl
    intro j hj'
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  unfold weightedShift
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j hj'
  rw [integral_const_mul, VinogradovMeanValue.integral_pair]
  split_ifs <;> simp

/-- The zero coefficient is exactly the nonnegative square energy. -/
theorem weightedShift_zero (v : ι → d → ℤ) (w : ι → ℂ) :
    weightedShift v w 0 =
      ((∫ θ : UnitAddTorus d, ‖∑ i, w i * mFourier (v i) θ‖ ^ 2 : ℝ) : ℂ) := by
  rw [weightedShift_eq_integral, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [] with θ
  simp only [mFourier_zero, ContinuousMap.one_apply, map_one, mul_one,
    Complex.mul_conj, Complex.sq_norm]

/-- Every shifted complex coefficient is controlled by the zero coefficient
of the same full weighted family. No coordinate is projected away. -/
theorem weightedShift_norm_le_zero (v : ι → d → ℤ) (w : ι → ℂ) (h : d → ℤ) :
    ‖weightedShift v w h‖ ≤ (weightedShift v w 0).re := by
  rw [weightedShift_zero, Complex.ofReal_re, weightedShift_eq_integral]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, norm_mFourier_apply]
  ring

/-- Unit coefficients recover the literal count of all shifted pairs. -/
theorem weightedShift_one (v : ι → d → ℤ) (h : d → ℤ) :
    weightedShift v (fun _ => 1) h = (differenceCount v h : ℂ) := by
  classical
  rw [differenceCount, Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  unfold weightedShift
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> norm_num

/-- The homogeneous system dominates every shifted frequency-difference
system, for any finite family of integer vectors. -/
theorem differenceCount_le_zero (v : ι → d → ℤ) (h : d → ℤ) :
    differenceCount v h ≤ differenceCount v 0 := by
  have he := weightedShift_norm_le_zero v (fun _ => 1) h
  rw [weightedShift_one, weightedShift_one, Complex.norm_natCast, Complex.natCast_re] at he
  exact_mod_cast he

/-- Bounded complex weights pay no more than the actual shifted pair count.
This estimate is downstream from the full signed Gram identity. -/
theorem weightedShift_norm_le_count (v : ι → d → ℤ) (w : ι → ℂ)
    (hw : ∀ i, ‖w i‖ ≤ 1) (h : d → ℤ) :
    ‖weightedShift v w h‖ ≤ differenceCount v h := by
  classical
  have hc : (differenceCount v h : ℝ) =
      ∑ i, ∑ j, if v i = v j + h then (1 : ℝ) else 0 := by
    rw [differenceCount, Finset.card_filter]
    push_cast
    rw [Fintype.sum_prod_type]
  rw [hc]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  split_ifs
  · rw [norm_mul, Complex.norm_conj]
    simpa using mul_le_mul (hw i) (hw j) (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 1)
  · simp

/-- The complete frequency vector of an ordered tuple, before taking any
count, norm or coordinate restriction. -/
def tupleFrequency (s : ℕ) (v : ι → d → ℤ) (x : Fin s → ι) : d → ℤ :=
  ∑ j, v (x j)

/-- The complete product of the original complex tuple weights. -/
def tupleWeight (s : ℕ) (w : ι → ℂ) (x : Fin s → ι) : ℂ := ∏ j, w (x j)

/-- The zero-shift tuple count is the existing Vinogradov collision count. -/
theorem tupleFrequency_count_zero (s : ℕ) (v : ι → d → ℤ) :
    differenceCount (tupleFrequency s v) 0 = collisionCount s v := by
  simp only [differenceCount, collisionCount, tupleFrequency, add_zero]

/-- Every shifted equal-power-sum count is bounded by the actual even
torus moment of the original frequency family. -/
theorem tuple_differenceCount_le_moment (s : ℕ) (v : ι → d → ℤ) (h : d → ℤ) :
    (differenceCount (tupleFrequency s v) h : ℝ) ≤ moment s v := by
  rw [moment_eq_collisionCount, ← tupleFrequency_count_zero]
  exact_mod_cast differenceCount_le_zero (tupleFrequency s v) h

/-- The weighted power expansion preserves every ordered tuple and its
original complex product weight. -/
theorem weighted_power_expansion (s : ℕ) (v : ι → d → ℤ) (w : ι → ℂ)
    (θ : UnitAddTorus d) :
    (∑ i, w i * mFourier (v i) θ) ^ s =
      ∑ x : Fin s → ι, tupleWeight s w x * mFourier (tupleFrequency s v x) θ := by
  classical
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.prod_mul_distrib, product_mFourier]
  rfl

omit [Fintype ι] in
/-- Bounded original weights remain bounded after forming every tuple. -/
theorem tupleWeight_norm_le_one (s : ℕ) (w : ι → ℂ) (hw : ∀ i, ‖w i‖ ≤ 1)
    (x : Fin s → ι) : ‖tupleWeight s w x‖ ≤ 1 := by
  rw [tupleWeight, norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => hw (x j))

/-- The shifted Fourier coefficient of an actual even weighted moment is
exactly its full tuple Gram coefficient. -/
theorem weighted_moment_coefficient (s : ℕ) (v : ι → d → ℤ) (w : ι → ℂ) (h : d → ℤ) :
    (∫ θ : UnitAddTorus d,
      ((‖∑ i, w i * mFourier (v i) θ‖ ^ (2 * s) : ℝ) : ℂ) * conj (mFourier h θ)) =
      weightedShift (tupleFrequency s v) (tupleWeight s w) h := by
  rw [weightedShift_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with θ
  rw [← weighted_power_expansion, Complex.mul_conj, ← Complex.sq_norm, norm_pow]
  congr 2
  ring

/-- Bounded complex phase weights cannot enlarge any shifted coefficient
beyond the homogeneous even moment of the unweighted family. -/
theorem weighted_coefficient_norm_le_moment (s : ℕ) (v : ι → d → ℤ) (w : ι → ℂ)
    (hw : ∀ i, ‖w i‖ ≤ 1) (h : d → ℤ) :
    ‖∫ θ : UnitAddTorus d,
      ((‖∑ i, w i * mFourier (v i) θ‖ ^ (2 * s) : ℝ) : ℂ) * conj (mFourier h θ)‖ ≤
      moment s v := by
  rw [weighted_moment_coefficient]
  exact (weightedShift_norm_le_count _ _ (tupleWeight_norm_le_one s w hw) h).trans
    (tuple_differenceCount_le_moment s v h)

/-- The even-moment majorant holds for every bounded complex weight family.
No pointwise inequality between the two oscillating sums is asserted. -/
theorem weighted_moment_le (s : ℕ) (v : ι → d → ℤ) (w : ι → ℂ)
    (hw : ∀ i, ‖w i‖ ≤ 1) :
    (∫ θ : UnitAddTorus d, ‖∑ i, w i * mFourier (v i) θ‖ ^ (2 * s)) ≤ moment s v := by
  have h := weighted_coefficient_norm_le_moment s v w hw 0
  simp only [mFourier_zero, ContinuousMap.one_apply, map_one, mul_one,
    integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
  rwa [abs_of_nonneg (integral_nonneg (fun _ => by positivity))] at h

/-- The shifted monomial system on `1,...,N` is controlled by the genuine
Vinogradov integral, at every order and every integer right-hand side. -/
theorem monomial_shift_le_meanValue (s k N : ℕ) (h : Fin k → ℤ) :
    (differenceCount (tupleFrequency s
      (fun n : Fin N => monomialFrequency k (n.val + 1))) h : ℝ) ≤ meanValue s k N :=
  tuple_differenceCount_le_moment s _ h

end
end RiemannGaussian.VinogradovShiftedMoment
