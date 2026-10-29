/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildTableCopy
import RiemannGaussian.SemiprimeD1TensorTapeLeaf

/-! # Active child table copying through the actual sequential tape backend
Every entry retains its original physical gather and individual integer lift.
Only the parent memory read is replaced, and every serialization is paid.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1ChildTableCopyTape
open SemiprimeD1JetAxes SemiprimeD1TensorTables SemiprimeD1ChildTableCopy

/-- Actual gathered assignment, tape serialization/read, then the SAME per-entry lift. -/
def entry {oldDegree : ℕ} (old : Context) (extra : List ℕ) (p : ℕ)
    (table : Table oldDegree) (order : List ℕ) (bits : List Bool) : SemiprimeD1JetRingBits.Run :=
  let selected:=gather bits order
  let value:=SemiprimeD1TensorTapeLookup.fromTable table selected.value
  let copied:=lift old extra p value.words
  ⟨copied.words,selected.work+value.clock+copied.clock+5⟩

/-- Complete eager child table using the actual tape-backed parent read at each leaf. -/
def acquire {oldDegree : ℕ} (old : Context) (extra : List ℕ) (p childDegree : ℕ)
    (table : Acquired oldDegree) (order : List ℕ) : Acquired childDegree :=
  let out:=build childDegree (entry old extra p table.table order)
  ⟨out.table,table.clock+out.clock+order.length+5⟩

/-- Per-entry integer lift is unchanged literally, never replaced by an aggregate lift. -/
theorem entry_words {d : ℕ} (old : Context) (extra : List ℕ) (p : ℕ)
    (table : Table d) (order : List ℕ) (bits : List Bool) :
    (entry old extra p table order bits).words=
      (SemiprimeD1ChildTableCopy.entry old extra p table order bits).words := by
  simp only [entry,SemiprimeD1ChildTableCopy.entry,SemiprimeD1TensorTapeLookup.fromTable_words]

/-- Every entry of the entire constructed child table agrees literally. -/
theorem acquire_table {d : ℕ} (old : Context) (extra : List ℕ) (p childDegree : ℕ)
    (table : Acquired d) (order : List ℕ) :
    (acquire old extra p childDegree table order).table=
      (SemiprimeD1ChildTableCopy.acquire old extra p childDegree table order).table :=
  SemiprimeD1TensorTapeLeaf.build_table_congr childDegree _ _ (entry_words old extra p table.table order)

/-- Every newly copied entry is the original individual integer lift of a parent entry. -/
theorem acquire_value {d : ℕ} (old : Context) (extra : List ℕ) (p childDegree : ℕ)
    (table : Acquired d) (order : List ℕ) (bits : List Bool) (hb : bits.length=childDegree) :
    (lookup (acquire old extra p childDegree table order).table bits).words=
      (lift old extra p (lookup table.table (gather bits order).value).words).words := by
  rw [acquire_table]
  exact SemiprimeD1ChildTableCopy.acquire_value old extra p childDegree table order bits hb

/-- Actual old canonical words imply canonical new data via the original individual lift. -/
theorem acquire_good {d : ℕ} (old : Context) (extra : List ℕ) (p childDegree : ℕ)
    (table : Acquired d) (order : List ℕ) (ht : Good old table.table) (he : 0<extra.prod) :
    Good ⟨extra++old.axes,p⟩ (acquire old extra p childDegree table order).table := by
  rw [acquire_table]
  exact SemiprimeD1ChildTableCopy.acquire_good old extra p childDegree table order ht he

/-- Fixed quadratic scan/serialization allowance in actual literal table storage. -/
def tapeBudget (I : ℕ) : ℕ := 8*(I+1)*I+4

/-- This actual parent table, not an externally supplied lookup clock, controls access. -/
theorem fromTable_clock {d : ℕ} (table : Table d) (bits : List Bool) :
    (SemiprimeD1TensorTapeLookup.fromTable table bits).clock ≤ tapeBudget (storage table) := by
  apply (SemiprimeD1TensorTapeLookup.fromTable_storage_clock table bits).trans
  have h:=SemiprimeD1TensorTapeCodec.tape_le_storage table
  unfold tapeBudget
  gcongr

/-- The complete actual eager-copy loop retains serialization on EVERY assignment. -/
theorem acquire_clock {d : ℕ} (old : Context) (extra : List ℕ) (p childDegree : ℕ)
    (table : Acquired d) (order : List ℕ) (ht : Good old table.table) (he : 0<extra.prod) :
    (acquire old extra p childDegree table order).clock ≤ table.clock+
      (order.length*(4*childDegree+7)+1+tapeBudget (storage table.table)+
        liftBudget old extra p+12)*2^childDegree+order.length := by
  have h:=build_clock childDegree
    (order.length*(4*childDegree+7)+1+tapeBudget (storage table.table)+liftBudget old extra p+5)
    (entry old extra p table.table order) (by
      intro bits hb
      have hg:=gather_clock bits order
      rw [hb] at hg
      have hv:=fromTable_clock table.table (gather bits order).value
      have hvGood : GoodWords old (SemiprimeD1TensorTapeLookup.fromTable table.table (gather bits order).value).words := by
        rw [SemiprimeD1TensorTapeLookup.fromTable_words]
        exact lookup_good old table.table ht _
      have hl:=lift_clock old extra p _ hvGood he
      change (gather bits order).work+
        (SemiprimeD1TensorTapeLookup.fromTable table.table (gather bits order).value).clock+
        (lift old extra p (SemiprimeD1TensorTapeLookup.fromTable table.table (gather bits order).value).words).clock+5 ≤ _
      omega)
  change (build childDegree (entry old extra p table.table order)).clock+5 ≤
    (order.length*(4*childDegree+7)+1+tapeBudget (storage table.table)+
      liftBudget old extra p+12)*2^childDegree at h
  change table.clock+(build childDegree (entry old extra p table.table order)).clock+order.length+5 ≤ _
  omega

/-- Original current-context coefficient bounds give a concrete table-storage cap. -/
def tableCap (old : Context) (D : ℕ) : ℕ := (old.rank*(3*old.precision+4)+3)*2^D

/-- Derived input shape, not an intermediate Fits or table-value premise. -/
theorem storage_le_cap {d : ℕ} (ctx : Context) (table : Table d) (hg : Good ctx table)
    (D : ℕ) (hd : d ≤ D) : storage table ≤ tableCap ctx D := by
  have h:=storage_bound ctx table hg
  have hp:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hd
  unfold tableCap
  exact (Nat.le_add_right _ 1).trans (h.trans (Nat.mul_le_mul_left _ hp))

/-- Tape scan allowance is a fixed polynomial in its actual storage argument. -/
theorem tapeBudget_mono {I J : ℕ} (h : I ≤ J) : tapeBudget I ≤ tapeBudget J := by
  unfold tapeBudget
  gcongr

end RiemannGaussian.SemiprimeD1ChildTableCopyTape
