/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecordsReduction
import RiemannGaussian.SemiprimeD1BoundaryRecordsSort
import RiemannGaussian.SemiprimeD1BoundaryRecordsBounds

/-! # Concrete boundary operations preserve dense canonical jets -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsCanonical
open SemiprimeD1BoundaryRecords
open SemiprimeD1BoundaryRecordsReduction
open SemiprimeD1JetAxes (Context)
open SemiprimeD1TensorTables (GoodWords)

/-- Canonical record lists are exactly canonical head and tail. -/
theorem good_cons (ctx : Context) (e : Entry) (es : List Entry) :
    GoodEntries ctx (e::es) ↔ GoodWords ctx e.words ∧ GoodEntries ctx es := by
  simp [GoodEntries]

/-- Sorting copies/permutates complete records without changing payloads. -/
theorem sort_good (ctx : Context) (es : List Entry) (h : GoodEntries ctx es) :
    GoodEntries ctx (sort es).value := by
  intro e he
  exact h e ((SemiprimeD1BoundaryRecordsSort.sort_perm es).mem_iff.mp he)

/-- Sort never loses an existing tensor entry. -/
theorem sort_nonempty (es : List Entry) (h : es≠[]) : (sort es).value≠[] := by
  intro he
  have hl:=SemiprimeD1BoundaryRecordsSort.sort_length es
  rw [he,List.length_nil] at hl
  exact h (List.eq_nil_of_length_eq_zero hl.symm)

/-- Request formation preserves exactly one record per original assignment. -/
theorem requests_length (source target : List Nat) (es : List Entry) :
    (requests source target es).value.length=es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [requests,ih]

/-- A sufficient sequential-cursor budget consumes every request exactly once. -/
theorem lookupFuel_length (ctx : Context) : (fuel : Nat) → (rs ts : List Entry) →
    rs.length+ts.length≤fuel → (lookupFuel ctx fuel rs ts).value.length=rs.length
  | 0,rs,ts,h => by
    have hr : rs=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst rs
    rfl
  | _+1,[],_,_ => rfl
  | fuel+1,r::rs,[],h => by
    simp only [lookupFuel,List.length_cons]
    rw [lookupFuel_length ctx fuel rs []]
    simp only [List.length_cons,List.length_nil,Nat.add_zero] at h ⊢
    omega
  | fuel+1,r::rs,t::ts,h => by
    rw [lookupFuel]
    cases ho : (compareKey r.key t.key).value <;>
      simp only [List.length_cons] <;>
      rw [lookupFuel_length] <;>
      simp only [List.length_cons] at h ⊢ <;> omega

/-- Actual multiplication canonicalizes every joined payload, including a
missing-table zero. No external Fits/canonical result is assumed. -/
theorem lookupFuel_good (ctx : Context) : (fuel : Nat) → (rs ts : List Entry) →
    rs.length+ts.length≤fuel → GoodEntries ctx (lookupFuel ctx fuel rs ts).value
  | 0,rs,ts,h => by
    have hr : rs=[] := List.eq_nil_of_length_eq_zero (by omega)
    subst rs
    simp [lookupFuel,GoodEntries]
  | _+1,[],_,_ => by simp [lookupFuel,GoodEntries]
  | fuel+1,r::rs,[],h => by
    rw [lookupFuel]
    apply good_cons ctx _ _ |>.mpr
    constructor
    · exact SemiprimeD1LeafCounterBounds.mul_good ctx _ _
    · apply lookupFuel_good ctx fuel rs []
      simp only [List.length_cons,List.length_nil,Nat.add_zero] at h ⊢
      omega
  | fuel+1,r::rs,t::ts,h => by
    rw [lookupFuel]
    cases ho : (compareKey r.key t.key).value
    · apply good_cons ctx _ _ |>.mpr
      constructor
      · exact SemiprimeD1LeafCounterBounds.mul_good ctx _ _
      · apply lookupFuel_good ctx fuel rs (t::ts)
        simp only [List.length_cons] at h ⊢; omega
    · apply good_cons ctx _ _ |>.mpr
      constructor
      · exact SemiprimeD1LeafCounterBounds.mul_good ctx _ _
      · apply lookupFuel_good ctx fuel rs (t::ts)
        simp only [List.length_cons] at h ⊢; omega
    · apply lookupFuel_good ctx fuel (r::rs) ts
      simp only [List.length_cons] at h ⊢; omega

/-- Both sorting passes and the actual monotone lookup preserve request count. -/
theorem attach_length (ctx : Context) (source target : List Nat) (acc table : List Entry) :
    (attach ctx source target acc table).value.length=acc.length := by
  unfold attach
  rw [SemiprimeD1BoundaryRecordsSort.sort_length,lookupFuel_length]
  · rw [SemiprimeD1BoundaryRecordsSort.sort_length,requests_length]
  · omega

/-- Every joined assignment is a complete canonical current-context jet. -/
theorem attach_good (ctx : Context) (source target : List Nat) (acc table : List Entry) :
    GoodEntries ctx (attach ctx source target acc table).value := by
  apply sort_good
  apply lookupFuel_good
  omega

/-- Projection preserves exactly the target address width. -/
theorem project_length (bits : List Bool) (source target : List Nat) :
    (project bits source target).value.length=target.length := by
  induction target with
  | nil => rfl
  | cons p ps ih => simp [project,ih]

/-- Boundary rekeying preserves actual coefficient payload canonicality. -/
theorem rekey_good (ctx : Context) (source target : List Nat) (es : List Entry)
    (h : GoodEntries ctx es) : GoodEntries ctx (rekey source target es).value := by
  induction es with
  | nil => simp [rekey,GoodEntries]
  | cons e es ih =>
    apply good_cons ctx _ _ |>.mpr
    constructor
    · exact h e List.mem_cons_self
    · exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- Rekeying keeps every actual address record. -/
theorem rekey_length (source target : List Nat) (es : List Entry) :
    (rekey source target es).value.length=es.length := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [rekey,ih]

/-- Sorting and equal-address reduction preserve full canonical jets. -/
theorem contract_good (ctx : Context) (source target : List Nat) (es : List Entry)
    (h : GoodEntries ctx es) : GoodEntries ctx (contract ctx source target es).value :=
  group_good ctx _ (sort_good ctx _ (rekey_good ctx source target es h))

/-- A nonempty tensor retains a real record after the boundary reduction. -/
theorem contract_nonempty (ctx : Context) (source target : List Nat) (es : List Entry)
    (h : es≠[]) : (contract ctx source target es).value≠[] := by
  apply group_nonempty
  apply sort_nonempty
  intro he
  have hl:=rekey_length source target es
  rw [he,List.length_nil] at hl
  exact h (List.eq_nil_of_length_eq_zero hl.symm)

/-- Every initialized assignment has the actual canonical ring unit, also at p0. -/
theorem seed_good (ctx : Context) (n : Nat) : GoodEntries ctx (seed ctx n).value := by
  intro e he
  obtain ⟨bits,_,rfl⟩:=List.mem_map.mp he
  exact SemiprimeD1LeafCounterBounds.one_good ctx

/-- Zero address dimensions still execute the unique empty assignment. -/
theorem seed_nonempty (ctx : Context) (n : Nat) : (seed ctx n).value≠[] := by
  intro he
  have hl : (seed ctx n).value.length=2^n := by
    simp [seed,SemiprimeD1BoundaryRecordsBounds.assignments_length]
  rw [he,List.length_nil] at hl
  have hp : 0<2^n := by positivity
  omega

end RiemannGaussian.SemiprimeD1BoundaryRecordsCanonical
