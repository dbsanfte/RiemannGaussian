/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceUniversalHeight
import RiemannGaussian.SemiprimePaidConstraintRows

/-! # Actual acquired integer constraint cache and copy height
The universal table is produced by the original executed parity/difference
supplier. Zero branches and leftover identity rows require no height advice.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace RiemannGaussian.SemiprimeSourceConstraintHeight
open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes SqrtLog
open SemiprimeMaterializedSourceUniversal SemiprimeSourceUniversalHeight
variable {r Q : ℕ}

/-- One original-input magnitude exponent for cleared constraints and copies. -/
def constraintExponent (A Q R : ℕ) : ℕ := entryExponent A Q R+R+1

/-- Acquired power and entry magnitude caps fit the cleared-constraint exponent. -/
theorem cleared_majorant (A Q R : ℕ) :
    2^R+2^(entryExponent A Q R) ≤ 2^(constraintExponent A Q R) := by
  have hR := Nat.pow_le_pow_right (by decide : 0<2) (show R ≤ entryExponent A Q R+R by omega)
  have hE := Nat.pow_le_pow_right (by decide : 0<2)
    (show entryExponent A Q R ≤ entryExponent A Q R+R by omega)
  calc
    _ ≤ 2^(entryExponent A Q R+R)+2^(entryExponent A Q R+R) := Nat.add_le_add hR hE
    _ = _ := by unfold constraintExponent; rw [pow_succ]; omega

/-- Semantic numerator height is derived from the actual executed supplier. -/
theorem numerator_abs (A R : ℕ) (t : Fin Q) (u y : UniversalType r Q 1) :
    |LayoutNumerator.entry 0 t A R u y| ≤ (2^(entryExponent A Q R):ℕ) := by
  have h := entry_acquired_abs A R t u y
  rw [entry_value A _ (SemiprimeBinomialExecutionTracked.acquiredParity_eq A R)] at h
  exact h

/-- All cleared-defect branches have the same original-input bound. -/
theorem constraint_abs (A R : ℕ) (t : Fin Q) (g : Fin r) (u y : UniversalType r Q 1) :
    |SemiprimeUniversalSourceExecution.constraint A R t g u y| ≤
      (2^(constraintExponent A Q R):ℕ) := by
  have hn := numerator_abs A R t u y
  have hp : |(2:ℤ)^(R-1)| ≤ (2^R:ℕ) := by
    norm_num only [abs_pow,show |(2:ℤ)|=2 by decide]
    exact_mod_cast Nat.pow_le_pow_right (by decide : 0<2) (Nat.sub_le R 1)
  have hmajor : ((2^R:ℕ):ℤ)+(2^(entryExponent A Q R):ℕ) ≤ (2^(constraintExponent A Q R):ℕ) := by
    exact_mod_cast cleared_majorant A Q R
  unfold SemiprimeUniversalSourceExecution.constraint
  split_ifs
  · rw [SemiprimeUniversalSourceExecution.numerator_eq]
    exact (abs_sub _ _).trans ((add_le_add hp hn).trans hmajor)
  · rw [SemiprimeUniversalSourceExecution.numerator_eq]
    simpa only [zero_sub,abs_neg] using hn.trans (by exact_mod_cast
      (Nat.le_add_left (2^(entryExponent A Q R)) (2^R)).trans (cleared_majorant A Q R))
  · simp
  · simp

/-- Every actual read from the acquired cache satisfies the derived bound. -/
theorem read_acquire_abs (A R : ℕ) (keys : List (UniversalType r Q 1))
    (complete : ∀ u,u∈keys) (t : Fin Q) (g : Fin r) (u y : UniversalType r Q 1) :
    |(SemiprimePaidConstraintCache.read (SemiprimePaidConstraintCache.acquire A R keys).value t g u y).value| ≤
      (2^(constraintExponent A Q R):ℕ) := by
  rw [SemiprimePaidConstraintCache.read_acquire A R keys complete]
  exact constraint_abs A R t g u y

/-- The acquired cache itself stores exactly Q times the square bank size integer cells. -/
theorem cache_scalar_cells (A R : ℕ) (keys : List (UniversalType r Q 1)) :
    ((SemiprimePaidConstraintCache.acquire A R keys).value.entries.flatMap
      (fun matrix => matrix.flatMap id)).length=Q*(keys.length*keys.length) :=
  table_scalar_cells A R keys

/-- The denominator register is the actually acquired bounded power, including R=0. -/
theorem cache_denominator_abs (A R : ℕ) (keys : List (UniversalType r Q 1)) :
    |(SemiprimePaidConstraintCache.acquire A R keys).value.denominator| ≤ (2^R:ℕ) :=
  powerTwo_prefix_abs (R-1) R (Nat.sub_le R 1)

/-- All actual block copies and leftover identity branches preserve the derived cap. -/
theorem copy_abs {I : Type} [DecidableEq I] (A R : ℕ)
    (keys : List (UniversalType r Q 1)) (complete : ∀ u,u∈keys)
    (addresses : SemiprimeMaterializedSourcePullback.Addresses I r Q)
    (producer : I → Run (UniversalType r Q 1)) (t : Fin Q) (g : Fin r)
    (j : SemiprimePaidConstraintRows.Index I r Q) (i : I) :
    |(SemiprimePaidConstraintRows.copy addresses producer
      (SemiprimePaidConstraintCache.acquire A R keys).value t g j i).value| ≤
      (2^(constraintExponent A Q R):ℕ) := by
  cases j with
  | inl z =>
    rcases z with ⟨b,u⟩
    simp only [SemiprimePaidConstraintRows.copy]
    split
    · simp
    · split_ifs
      · exact read_acquire_abs A R keys complete t g u _
      · simp
  | inr a =>
    simp only [SemiprimePaidConstraintRows.copy]
    split_ifs
    · norm_num only [abs_one]
      exact_mod_cast (Nat.one_le_pow (constraintExponent A Q R) 2 (by decide))
    · norm_num

end RiemannGaussian.SemiprimeSourceConstraintHeight
