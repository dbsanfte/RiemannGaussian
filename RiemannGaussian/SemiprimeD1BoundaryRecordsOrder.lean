/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BoundaryRecords
import Mathlib.Data.List.Sort

/-! # Order laws for the actual paid boundary-key comparator
Keys are literal lexicographic Boolean words, with false first and EOF before
any further bit. Payload words never enter this comparison.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1BoundaryRecordsOrder

/-- The actual comparator reports equality exactly for equal raw key bytes. -/
theorem compareKey_eq (xs ys : List Bool) :
    (SemiprimeD1BoundaryRecords.compareKey xs ys).value=Ordering.eq ↔ xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [SemiprimeD1BoundaryRecords.compareKey]
  | cons x xs ih =>
    cases ys with
    | nil => simp [SemiprimeD1BoundaryRecords.compareKey]
    | cons y ys => cases x <;> cases y <;> simp [SemiprimeD1BoundaryRecords.compareKey,ih]

/-- Proof-side nondecreasing order induced by the actual comparator. -/
def KeyLE (xs ys : List Bool) : Prop := (SemiprimeD1BoundaryRecords.compareKey xs ys).value ≠ Ordering.gt

/-- Every comparator test is decidable from its real finite words. -/
instance keyLEDecidable : DecidableRel KeyLE := fun _ _ => inferInstanceAs (Decidable (_ ≠ _))

/-- Equal words are nondecreasing. -/
theorem keyLE_refl (xs : List Bool) : KeyLE xs xs := by
  have h := (compareKey_eq xs xs).mpr rfl
  simp [KeyLE,h]

/-- Either raw key precedes the other, including unequal lengths and EOF. -/
theorem keyLE_total (xs ys : List Bool) : KeyLE xs ys ∨ KeyLE ys xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [KeyLE,SemiprimeD1BoundaryRecords.compareKey]
  | cons x xs ih =>
    cases ys with
    | nil => simp [KeyLE,SemiprimeD1BoundaryRecords.compareKey]
    | cons y ys => cases x <;> cases y <;> simp_all [KeyLE,SemiprimeD1BoundaryRecords.compareKey]

/-- Nondecreasing order of actual keys is transitive. -/
theorem keyLE_trans (xs ys zs : List Bool) (hxy : KeyLE xs ys) (hyz : KeyLE ys zs) :
    KeyLE xs zs := by
  induction xs generalizing ys zs with
  | nil => cases zs <;> simp [KeyLE,SemiprimeD1BoundaryRecords.compareKey]
  | cons x xs ih =>
    cases ys with
    | nil => simp [KeyLE,SemiprimeD1BoundaryRecords.compareKey] at hxy
    | cons y ys =>
      cases zs with
      | nil => simp [KeyLE,SemiprimeD1BoundaryRecords.compareKey] at hyz
      | cons z zs =>
        cases x <;> cases y <;> cases z <;>
          simp_all [KeyLE,SemiprimeD1BoundaryRecords.compareKey]
        all_goals exact ih _ _ hxy hyz

/-- Mutual nondecreasing comparison forces exact key equality. -/
theorem keyLE_antisymm (xs ys : List Bool) (hxy : KeyLE xs ys) (hyx : KeyLE ys xs) :
    xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [KeyLE,SemiprimeD1BoundaryRecords.compareKey]
  | cons x xs ih =>
    cases ys with
    | nil => simp_all [KeyLE,SemiprimeD1BoundaryRecords.compareKey]
    | cons y ys =>
      cases x <;> cases y <;> simp_all [KeyLE,SemiprimeD1BoundaryRecords.compareKey]
      all_goals exact ih _ hxy hyx

/-- The record order compares keys and preserves every full payload. -/
def EntryLE (a b : SemiprimeD1BoundaryRecords.Entry) : Prop := KeyLE a.key b.key

/-- A finite comparator for the same record relation. -/
instance entryLEDecidable : DecidableRel EntryLE := fun _ _ => inferInstanceAs (Decidable (KeyLE _ _))

/-- Boolean form consumed by Lean's reference merge. -/
def entryLe (a b : SemiprimeD1BoundaryRecords.Entry) : Bool := decide (EntryLE a b)

/-- The record comparison is transitive without requiring equal payload words. -/
theorem entryLE_trans (a b c : SemiprimeD1BoundaryRecords.Entry) (hab : EntryLE a b) (hbc : EntryLE b c) : EntryLE a c :=
  keyLE_trans a.key b.key c.key hab hbc

/-- The record comparison is total, including repeated equal keys. -/
theorem entryLE_total (a b : SemiprimeD1BoundaryRecords.Entry) : EntryLE a b ∨ EntryLE b a := keyLE_total a.key b.key

end RiemannGaussian.SemiprimeD1BoundaryRecordsOrder
