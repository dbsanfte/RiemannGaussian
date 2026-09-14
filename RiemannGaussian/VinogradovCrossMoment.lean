/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovProductEnergy
import RiemannGaussian.VinogradovInterpolation

/-!
# Full complex cross moments and frequency dilation

Orthogonality retains every matching-frequency complex correlation between
arbitrary original coefficient families. The resulting Cauchy bound uses
their actual self energies. Nonzero integer frequency dilation preserves
all even weighted moments exactly, including their phase correlations.
-/

namespace RiemannGaussian.VinogradovCrossMoment
noncomputable section
open MeasureTheory UnitAddTorus
open scoped BigOperators ComplexConjugate Classical
open VinogradovMeanValue VinogradovPartitionEnergy
/-- The original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The complete complex correlation between two original finite frequency families. -/
def crossGram {ι κ d : Type*} [Fintype ι] [Fintype κ] (v : ι → d → ℤ) (u : κ → d → ℤ)
    (w : ι → ℂ) (z : κ → ℂ) : ℂ :=
  ∑ i, ∑ j, if v i = u j then w i * conj (z j) else 0

/-- Orthogonality recovers every matching-frequency complex cross term exactly. -/
theorem crossGram_eq_integral {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (v : ι → d → ℤ) (u : κ → d → ℤ) (w : ι → ℂ) (z : κ → ℂ) :
    crossGram v u w z = ∫ theta : UnitAddTorus d,
      polynomial v w theta * conj (polynomial u z theta) := by
  have hi (i : ι) (j : κ) : Integrable (fun theta : UnitAddTorus d =>
      (w i * conj (z j)) * (mFourier (v i) theta * conj (mFourier (u j) theta))) :=
    (by fun_prop : Continuous _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have he (theta : UnitAddTorus d) : polynomial v w theta * conj (polynomial u z theta) =
      ∑ i, ∑ j, (w i * conj (z j)) * (mFourier (v i) theta * conj (mFourier (u j) theta)) := by
    simp only [polynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi'
    apply Finset.sum_congr rfl
    intro j hj'
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  unfold crossGram
  apply Finset.sum_congr rfl
  intro i hi'
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j hj'
  rw [integral_const_mul, VinogradovMeanValue.integral_pair]
  split_ifs <;> simp

/-- The full cross correlation is bounded by the actual two self energies, with zero functions included. -/
theorem crossGram_norm_le {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (v : ι → d → ℤ) (u : κ → d → ℤ) (w : ι → ℂ) (z : κ → ℂ) :
    ‖crossGram v u w z‖ ≤
      (∫ theta : UnitAddTorus d, ‖polynomial v w theta‖ ^ 2) ^ (1 / 2 : ℝ) *
      (∫ theta : UnitAddTorus d, ‖polynomial u z theta‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have hr (a : ℂ) : (‖a‖ ^ 2) ^ (1 / 2 : ℝ) = ‖a‖ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  have he := VinogradovInterpolation.integral_geometric_le (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    (fun theta : UnitAddTorus d => ‖polynomial v w theta‖ ^ 2)
    (fun theta : UnitAddTorus d => ‖polynomial u z theta‖ ^ 2)
    ((continuous_polynomial v w).norm.pow 2) ((continuous_polynomial u z).norm.pow 2)
    (fun _ => by positivity) (fun _ => by positivity)
  norm_num only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hr] at he
  rw [crossGram_eq_integral]
  apply (norm_integral_le_integral_norm _).trans
  simpa only [norm_mul, Complex.norm_conj] using he

/-- All ordered pairs with equal full frequency vectors, for two possibly different index families. -/
def crossCount {ι κ d : Type*} [Fintype ι] [Fintype κ] (v : ι → d → ℤ) (u : κ → d → ℤ) : ℕ :=
  (Finset.univ.filter (fun ij : ι × κ => v ij.1 = u ij.2)).card

/-- Unit coefficients retain the exact original cross-collision count. -/
theorem crossGram_one {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (v : ι → d → ℤ) (u : κ → d → ℤ) :
    crossGram v u (fun _ => 1) (fun _ => 1) = (crossCount v u : ℂ) := by
  rw [crossCount, Finset.card_filter]
  push_cast
  rw [Fintype.sum_prod_type]
  unfold crossGram
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> norm_num

/-- Every actual cross-collision count receives the actual two continuous self energies. -/
theorem crossCount_le_energies {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (v : ι → d → ℤ) (u : κ → d → ℤ) :
    (crossCount v u : ℝ) ≤
      (∫ theta : UnitAddTorus d, ‖polynomial v (fun _ => 1) theta‖ ^ 2) ^ (1 / 2 : ℝ) *
      (∫ theta : UnitAddTorus d, ‖polynomial u (fun _ => 1) theta‖ ^ 2) ^ (1 / 2 : ℝ) := by
  have he := crossGram_norm_le v u (fun _ => 1) (fun _ => 1)
  simpa only [crossGram_one, Complex.norm_natCast] using he

/-- Multiplying every full integer frequency by a nonzero integer preserves the original complex cross correlation. -/
theorem crossGram_dilation {ι κ d : Type*} [Fintype ι] [Fintype κ]
    (m : ℤ) (hm : m ≠ 0) (v : ι → d → ℤ) (u : κ → d → ℤ) (w : ι → ℂ) (z : κ → ℂ) :
    crossGram (fun i j => m * v i j) (fun i j => m * u i j) w z = crossGram v u w z := by
  have he (i : ι) (j : κ) : (fun d => m * v i d) = (fun d => m * u j d) ↔ v i = u j := by
    constructor
    · intro hij
      funext d
      exact mul_left_cancel₀ hm (congrFun hij d)
    · intro hij
      rw [hij]
  simp only [crossGram, he]

/-- The exact even moment is the full self correlation of original weighted tuples. -/
theorem even_moment_eq_crossGram {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (v : ι → d → ℤ) (w : ι → ℂ) :
    ((∫ theta : UnitAddTorus d, ‖polynomial v w theta‖ ^ (2 * s) : ℝ) : ℂ) =
      crossGram (VinogradovShiftedMoment.tupleFrequency s v)
        (VinogradovShiftedMoment.tupleFrequency s v)
        (VinogradovShiftedMoment.tupleWeight s w) (VinogradovShiftedMoment.tupleWeight s w) := by
  have he := VinogradovShiftedMoment.weighted_moment_coefficient s v w 0
  simp only [mFourier_zero, ContinuousMap.one_apply, map_one, mul_one,
    integral_complex_ofReal, crossGram, VinogradovShiftedMoment.weightedShift, add_zero, polynomial] at he ⊢
  convert he using 1
  congr!

/-- Every actual even torus moment is unchanged by nonzero integer frequency dilation, retaining arbitrary original complex weights. -/
theorem weighted_even_moment_dilation {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (m : ℤ) (hm : m ≠ 0) (v : ι → d → ℤ) (w : ι → ℂ) :
    (∫ theta : UnitAddTorus d, ‖polynomial (fun i j => m * v i j) w theta‖ ^ (2 * s)) =
      ∫ theta : UnitAddTorus d, ‖polynomial v w theta‖ ^ (2 * s) := by
  have ht : VinogradovShiftedMoment.tupleFrequency s (fun i j => m * v i j) =
      fun x j => m * VinogradovShiftedMoment.tupleFrequency s v x j := by
    funext x j
    simp only [VinogradovShiftedMoment.tupleFrequency, Finset.sum_apply, Finset.mul_sum]
  apply Complex.ofReal_injective
  rw [even_moment_eq_crossGram, even_moment_eq_crossGram, ht]
  exact crossGram_dilation m hm _ _ _ _

end
end RiemannGaussian.VinogradovCrossMoment
