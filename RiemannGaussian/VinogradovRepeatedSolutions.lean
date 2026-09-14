/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovRepeatedMoment

/-!
# Repeated original solutions and their actual moment deficit

An injective compression preserves the full frequency of a tuple with two
equal entries. Exact complex polynomial identities and the repeated-factor
Holder bound control its collision count. Permuting positions transports
the same estimate to every prescribed distinct pair of positions.
-/

namespace RiemannGaussian.VinogradovRepeatedSolutions
noncomputable section
open scoped Classical BigOperators ComplexConjugate
open UnitAddTorus MeasureTheory VinogradovPartitionEnergy VinogradovMeanValue
open VinogradovShiftedMoment VinogradovProductEnergy
open VinogradovCrossMoment VinogradovRepeatedMoment
/-- The original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle Haar measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
/-- One repeated entry and all the remaining original coordinates retain their complete frequency. -/
def repeatedFrequency {ι d : Type*} (s : ℕ) (v : ι → d → ℤ)
    (z : ι × (Fin s → ι)) : d → ℤ :=
  (fun j => 2 * v z.1 j) + tupleFrequency s v z.2
/-- Unit-weight tuple sums are the exact original polynomial power. -/
theorem tuple_polynomial_one {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (v : ι → d → ℤ) (theta : UnitAddTorus d) :
    polynomial (tupleFrequency s v) (fun _ => 1) theta = polynomial v (fun _ => 1) theta ^ s := by
  symm
  simpa only [tupleWeight, Finset.prod_const_one, polynomial] using weighted_power_expansion s v (fun _ => 1) theta
/-- The repeated entry forces frequency dilation by two before any norm. -/
theorem repeated_polynomial {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (v : ι → d → ℤ) (theta : UnitAddTorus d) :
    polynomial (repeatedFrequency s v) (fun _ => 1) theta =
      polynomial (fun i j => (2 : ℤ) * v i j) (fun _ => 1) theta *
        polynomial v (fun _ => 1) theta ^ s := by
  unfold repeatedFrequency
  have hp := polynomial_prod (fun i j => (2 : ℤ) * v i j) (tupleFrequency s v)
    (fun _ => 1) (fun _ => 1) theta
  simpa only [one_mul, tuple_polynomial_one] using hp
/-- The actual compressed repeated-entry collision count receives the proved fractional moment deficit. -/
theorem repeated_crossCount_le {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (v : ι → d → ℤ) :
    (crossCount (repeatedFrequency s v) (tupleFrequency (s + 2) v) : ℝ) ≤
      moment (s + 2) v ^ (1 - 1 / ((2 * (s + 2) : ℕ) : ℝ)) := by
  have he := congrArg norm (crossGram_one (repeatedFrequency s v) (tupleFrequency (s + 2) v))
  rw [Complex.norm_natCast] at he
  rw [← he, crossGram_eq_integral]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ = ∫ theta : UnitAddTorus d,
        ‖polynomial (fun i j => (2 : ℤ) * v i j) (fun _ => 1) theta‖ *
          ‖polynomial v (fun _ => 1) theta‖ ^ (2 * (s + 2) - 2) := by
      apply integral_congr_ae
      filter_upwards [] with theta
      rw [norm_mul, Complex.norm_conj, repeated_polynomial, tuple_polynomial_one, norm_mul,
        norm_pow, norm_pow, mul_assoc, ← pow_add]
      congr 2
      omega
    _ ≤ _ := repeated_coordinate_integral_le (by omega) v
/-- Original two-sided collisions whose first two left coordinates coincide. -/
def repeatedPairCount {ι d : Type*} [Fintype ι] (s : ℕ) (v : ι → d → ℤ) : ℕ :=
  (Finset.univ.filter (fun xy : (Fin (s + 2) → ι) × (Fin (s + 2) → ι) =>
    xy.1 0 = xy.1 1 ∧ tupleFrequency (s + 2) v xy.1 = tupleFrequency (s + 2) v xy.2)).card
/-- Compression reconstructs the complete original frequency when the first two entries coincide. -/
theorem tupleFrequency_eq_repeated {ι d : Type*} (s : ℕ) (v : ι → d → ℤ)
    (x : Fin (s + 2) → ι) (hx : x 0 = x 1) :
    tupleFrequency (s + 2) v x = repeatedFrequency s v (x 0, fun j => x j.succ.succ) := by
  funext j
  simp only [tupleFrequency, repeatedFrequency, Pi.add_apply, Finset.sum_apply, Fin.sum_univ_succ]
  change x 0 = x (0 : Fin (s + 1)).succ at hx
  rw [← hx]
  ring
/-- Compress only repeated original inputs; injectivity and the full equations precede the count comparison. -/
theorem repeatedPairCount_le_crossCount {ι d : Type*} [Fintype ι]
    (s : ℕ) (v : ι → d → ℤ) :
    repeatedPairCount s v ≤ crossCount (repeatedFrequency s v) (tupleFrequency (s + 2) v) := by
  unfold repeatedPairCount crossCount
  apply Finset.card_le_card_of_injOn
    (fun xy => ((xy.1 0, fun j => xy.1 j.succ.succ), xy.2))
  · intro xy hxy
    have hx := (Finset.mem_filter.mp hxy).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← tupleFrequency_eq_repeated s v xy.1 hx.1]
    exact hx.2
  · intro xy hxy zw hzw he
    have hx := (Finset.mem_filter.mp hxy).2.1
    have hz := (Finset.mem_filter.mp hzw).2.1
    have hhead := congrArg (fun z => z.1.1) he
    have htail := congrArg (fun z => z.1.2) he
    have hright := congrArg Prod.snd he
    dsimp only at hhead htail hright
    apply Prod.ext _ hright
    funext i
    refine Fin.cases hhead (fun j => ?_) i
    refine Fin.cases ?_ (fun l => congrFun htail l) j
    exact hx.symm.trans (hhead.trans hz)
/-- The original repeated-coordinate solution count has the actual homogeneous-moment deficit, with no moment estimate assumed. -/
theorem repeatedPairCount_le_moment {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (v : ι → d → ℤ) :
    (repeatedPairCount s v : ℝ) ≤ moment (s + 2) v ^ (1 - 1 / ((2 * (s + 2) : ℕ) : ℝ)) := by
  exact (show (repeatedPairCount s v : ℝ) ≤
    (crossCount (repeatedFrequency s v) (tupleFrequency (s + 2) v) : ℝ) by
      exact_mod_cast repeatedPairCount_le_crossCount s v).trans (repeated_crossCount_le s v)
end
end RiemannGaussian.VinogradovRepeatedSolutions

namespace RiemannGaussian.VinogradovRepeatedSolutions.Pairs
noncomputable section
open scoped Classical BigOperators
open VinogradovShiftedMoment VinogradovRepeatedSolutions VinogradovPartitionEnergy VinogradovMeanValue
/-- Any ordered pair of distinct coordinates can be relocated by a permutation. -/
theorem exists_pair_permutation {α : Type*} (a b c d : α) (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ e : Equiv.Perm α, e a = c ∧ e b = d := by
  have hf : Function.Injective (fun z : Bool => if z then b else a) := by
    intro x y h
    cases x <;> cases y <;> simp_all
  have hg : Function.Injective (fun z : Bool => if z then d else c) := by
    intro x y h
    cases x <;> cases y <;> simp_all
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair _ _ hf hg
  exact ⟨e, by simpa using he false, by simpa using he true⟩
/-- Reordering the original tuple preserves every full integer frequency coordinate. -/
theorem tupleFrequency_comp_perm {ι d : Type*} (s : ℕ) (v : ι → d → ℤ)
    (x : Fin s → ι) (e : Equiv.Perm (Fin s)) :
    tupleFrequency s v (x ∘ e) = tupleFrequency s v x := by
  funext j
  simpa only [tupleFrequency, Finset.sum_apply, Function.comp_apply] using
    Equiv.sum_comp e (fun i => v (x i) j)
/-- Original full-frequency collisions with an arbitrary repeated left pair. -/
def pairCollisionCount {ι d : Type*} [Fintype ι] (s : ℕ) (v : ι → d → ℤ)
    (a b : Fin (s + 2)) : ℕ :=
  (Finset.univ.filter (fun xy : (Fin (s + 2) → ι) × (Fin (s + 2) → ι) =>
    xy.1 a = xy.1 b ∧ tupleFrequency (s + 2) v xy.1 = tupleFrequency (s + 2) v xy.2)).card
/-- An actual coordinate permutation injects any repeated-pair class into the first-pair class. -/
theorem pairCollisionCount_le_first {ι d : Type*} [Fintype ι] (s : ℕ) (v : ι → d → ℤ)
    (a b : Fin (s + 2)) (hab : a ≠ b) :
    pairCollisionCount s v a b ≤ repeatedPairCount s v := by
  obtain ⟨e, he0, he1⟩ := exists_pair_permutation (0 : Fin (s + 2)) 1 a b (by
    have h : (1 : ℕ) < s + 2 := by omega
    exact Fin.zero_ne_one) hab
  unfold pairCollisionCount repeatedPairCount
  apply Finset.card_le_card_of_injOn (fun xy => (xy.1 ∘ e, xy.2))
  · intro xy hxy
    have hx := (Finset.mem_filter.mp hxy).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simpa only [Function.comp_apply, he0, he1] using hx.1
    · simpa only [tupleFrequency_comp_perm] using hx.2
  · intro xy hxy zw hzw he
    have hl := congrArg Prod.fst he
    have hr := congrArg Prod.snd he
    dsimp only at hl hr
    apply Prod.ext _ hr
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    exact congrFun hl i
/-- Every original repeated-pair solution class has the same actual homogeneous moment deficit. -/
theorem pairCollisionCount_le_moment {ι d : Type*} [Fintype ι] [Fintype d]
    (s : ℕ) (v : ι → d → ℤ) (a b : Fin (s + 2)) (hab : a ≠ b) :
    (pairCollisionCount s v a b : ℝ) ≤
      moment (s + 2) v ^ (1 - 1 / ((2 * (s + 2) : ℕ) : ℝ)) := by
  exact (show (pairCollisionCount s v a b : ℝ) ≤ (repeatedPairCount s v : ℝ) by
    exact_mod_cast pairCollisionCount_le_first s v a b hab).trans (repeatedPairCount_le_moment s v)
end
end RiemannGaussian.VinogradovRepeatedSolutions.Pairs
