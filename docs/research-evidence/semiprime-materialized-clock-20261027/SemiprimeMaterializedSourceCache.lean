/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMaterializedSourceRows

/-! # Paid finite universal-cache lookup
Every register comparison and list cell is executed and charged. The cache is
created by the actual universal supplier; semantic functions occur only in proofs.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeMaterializedSourceCache
open OAI.Algorithms.SubexponentialSAT
open MulticolorTypes
open SemiprimeMaterializedSourceUniversal
variable {r Q : ℕ}

/-- Exact Boolean register equality from the complete paid finite scan. -/
def same (u y : UniversalType r Q 1) : Run Bool :=
  equalWord Q u.head (u.slot 0) y.head (y.slot 0)

theorem same_correct (u y : UniversalType r Q 1) : (same u y).value=true ↔ u=y := by
  rw [same,equalWord_value]
  constructor
  · intro h
    cases u with | mk uh us =>
      cases y with | mk yh ys =>
        have hh : uh=yh := funext (fun i => (h i).1)
        have hs : us=ys := by
          funext i t
          have hi : i=0 := Subsingleton.elim _ _
          subst i
          exact (h t).2
        cases hh; cases hs; rfl
  · intro h
    subst u
    exact fun _ => ⟨rfl,rfl⟩

theorem same_work (u y : UniversalType r Q 1) : (same u y).work=7*Q+1 :=
  equalWord_work _ _ _ _ _

/-- Actual keyed finite lookup; data and keys are concrete lists, not a function oracle. -/
def lookup {β : Type*} (target : UniversalType r Q 1) :
    List (UniversalType r Q 1) → List β → Run (Option β)
  | [],_ => ⟨none,1⟩
  | _::_,[] => ⟨none,1⟩
  | key::keys,value::values =>
      let eq := same key target
      if eq.value then ⟨some value,eq.work+3⟩
      else
        let tail := lookup target keys values
        ⟨tail.value,eq.work+tail.work+3⟩

/-- A materialized map cache returns its actual matching value. -/
theorem lookup_map {β : Type*} (target : UniversalType r Q 1)
    (keys : List (UniversalType r Q 1)) (f : UniversalType r Q 1 → β) (h : target∈keys) :
    (lookup target keys (keys.map f)).value=some (f target) := by
  induction keys with
  | nil => simp at h
  | cons key keys ih =>
    simp only [List.map_cons,lookup]
    by_cases he : key=target
    · have hs := (same_correct key target).mpr he
      rw [ite_eq_left hs]
      subst key
      rfl
    · have hs : ¬(same key target).value=true := by simpa only [same_correct] using he
      rw [ite_eq_right hs]
      apply ih
      exact (List.mem_cons.mp h).resolve_left (Ne.symm he)

/-- Lookup never executes more than the full key list. -/
theorem lookup_work {β : Type*} (target : UniversalType r Q 1)
    (keys : List (UniversalType r Q 1)) (values : List β) :
    (lookup target keys values).work≤keys.length*(7*Q+4)+1 := by
  induction keys generalizing values with
  | nil => simp [lookup]
  | cons key keys ih =>
    cases values with
    | nil => simp only [lookup,List.length_cons]; omega
    | cons value values =>
      unfold lookup
      dsimp only
      split_ifs <;> dsimp only
      · rw [same_work]
        simp only [List.length_cons]
        nlinarith
      · rw [same_work]
        have ht := ih values
        simp only [List.length_cons]
        nlinarith

/-- Read one array from the actual cached universal family by two paid finite lookups. -/
def read (R : ℕ) (keys : List (UniversalType r Q 1))
    (cache : List (List (Array ℚ))) (u y : UniversalType r Q 1) : Run (Array ℚ) :=
  let outer := lookup u keys cache
  match outer.value with
  | none => ⟨Array.replicate (R+1) 0,outer.work+R+2⟩
  | some row =>
      let inner := lookup y keys row
      ⟨inner.value.getD (Array.replicate (R+1) 0),outer.work+inner.work+R+2⟩

/-- Complete acquired universal caches contain the exact original universal row array. -/
theorem read_acquire (A R : ℕ) (keys : List (UniversalType r Q 1))
    (complete : ∀ u, u∈keys) (u y : UniversalType r Q 1) :
    (read R keys (SemiprimeMaterializedSourceRows.acquire A R keys).value u y).value=
      (SemiprimeUniversalSourceExecution.universalRow A R u y).coefficients := by
  rw [SemiprimeMaterializedSourceRows.acquire_value]
  unfold read
  dsimp only
  rw [lookup_map u keys _ (complete u)]
  dsimp only
  rw [lookup_map y keys _ (complete y)]
  rfl

/-- Both cache scans and the allocated/default array width have explicit finite cost. -/
theorem read_work (R : ℕ) (keys : List (UniversalType r Q 1))
    (cache : List (List (Array ℚ))) (u y : UniversalType r Q 1) :
    (read R keys cache u y).work≤2*(keys.length*(7*Q+4)+1)+R+2 := by
  have ho := lookup_work u keys cache
  unfold read
  dsimp only
  split <;> dsimp only
  · omega
  · have hi := lookup_work y keys ‹List (Array ℚ)›
    omega

end RiemannGaussian.SemiprimeMaterializedSourceCache
