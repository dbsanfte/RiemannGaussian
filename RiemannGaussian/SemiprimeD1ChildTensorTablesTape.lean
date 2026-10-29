/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildTableCopyTape
import RiemannGaussian.SemiprimeD1ChildTensorTables

/-! # Actual tape-backed activated old tensor construction
The inactive unit and the per-entry integer lift remain literal original data.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1ChildTensorTablesTape
open SemiprimeD1TensorTables SemiprimeD1JetAxes
open SemiprimeD1ChildTensorTables (Result unit unit_good unit_clock)

/-- The current parent table is supplied literally; all routing metadata is acquired
from the actual cached endpoint permutation, and every old coordinate is kept. -/
def fromCache {n F a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (data : SemiprimeD1ChildPortPullback.Acquired n F a arity) (v : Fin (n+F))
    (old : Context) (extra : List ℕ) (p : ℕ)
    (parent : Table (SemiprimeD1ChildTableOrder.acquire owner data v).old.length) : Result :=
  let ports := SemiprimeD1ChildTableOrder.acquire owner data v
  if (data.activation.bits[v.val]?).getD false then
    let out := SemiprimeD1ChildTableCopyTape.acquire old extra p ports.child.length ⟨parent,0⟩ ports.order
    ⟨ports.child.length,out.table,ports.clock+out.clock+5⟩
  else
    let out := unit ⟨extra++old.axes,p⟩
    ⟨0,out.table,ports.clock+out.clock+5⟩

/-- Inactive old vertices literally acquire a zero-port scalar-one table. -/
theorem fromCache_inactive {n F a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (data : SemiprimeD1ChildPortPullback.Acquired n F a arity) (v : Fin (n+F))
    (old : Context) (extra : List ℕ) (p : ℕ)
    (parent : Table (SemiprimeD1ChildTableOrder.acquire owner data v).old.length)
    (ha : (data.activation.bits[v.val]?).getD false=false) :
    (fromCache owner data v old extra p parent).degree=0 ∧
    HEq (fromCache owner data v old extra p parent).table (unit ⟨extra++old.axes,p⟩).table := by
  have he : fromCache owner data v old extra p parent=
      ⟨0,(unit ⟨extra++old.axes,p⟩).table,
        (SemiprimeD1ChildTableOrder.acquire owner data v).clock+(unit ⟨extra++old.axes,p⟩).clock+5⟩ := by
    dsimp only [fromCache]
    rw [ha]
    rfl
  rw [he]
  exact ⟨rfl,HEq.rfl⟩

/-- Every resulting table has intrinsic canonical shape in the CURRENT child ring. -/
theorem fromCache_good {n F a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (data : SemiprimeD1ChildPortPullback.Acquired n F a arity) (v : Fin (n+F))
    (old : Context) (extra : List ℕ) (p : ℕ)
    (parent : Table (SemiprimeD1ChildTableOrder.acquire owner data v).old.length)
    (hp : Good old parent) (he : 0<extra.prod) :
    Good ⟨extra++old.axes,p⟩ (fromCache owner data v old extra p parent).table := by
  dsimp only [fromCache]
  by_cases ha : (data.activation.bits[v.val]?).getD false=true
  · rw [ha]
    exact SemiprimeD1ChildTableCopyTape.acquire_good old extra p _ ⟨parent,0⟩ _ hp he
  · have hf : (data.activation.bits[v.val]?).getD false=false := Bool.eq_false_iff.mpr ha
    rw [hf]
    exact unit_good _

/-- Active copied entries read the original literal table in the computed cache order. -/
theorem fromCache_active_value {n F a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (data : SemiprimeD1ChildPortPullback.Acquired n F a arity) (v : Fin (n+F))
    (old : Context) (extra : List ℕ) (p : ℕ)
    (parent : Table (SemiprimeD1ChildTableOrder.acquire owner data v).old.length)
    (ha : (data.activation.bits[v.val]?).getD false=true)
    (bits : List Bool) (hb : bits.length=(SemiprimeD1ChildTableOrder.acquire owner data v).child.length) :
    (lookup (fromCache owner data v old extra p parent).table bits).words=
      (SemiprimeD1ChildTableCopy.lift old extra p
        (lookup parent (SemiprimeD1ChildTableCopy.gather bits
          (SemiprimeD1ChildTableOrder.acquire owner data v).order).value).words).words := by
  dsimp only [fromCache]
  rw [ha]
  exact SemiprimeD1ChildTableCopyTape.acquire_value old extra p _ ⟨parent,0⟩ _ bits hb

/-- Degree and entire literal table, deliberately excluding acquisition reports. -/
def payload (out : Result) : (d : ℕ) × Table d := ⟨out.degree,out.table⟩

/-- Actual new construction preserves all literal data, not its changed clock. -/
theorem fromCache_payload {n F a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (data : SemiprimeD1ChildPortPullback.Acquired n F a arity) (v : Fin (n+F))
    (old : Context) (extra : List ℕ) (p : ℕ)
    (parent : Table (SemiprimeD1ChildTableOrder.acquire owner data v).old.length) :
    payload (fromCache owner data v old extra p parent)=
      payload (SemiprimeD1ChildTensorTables.fromCache owner data v old extra p parent) := by
  cases ha : (data.activation.bits[v.val]?).getD false with
  | false => simp only [fromCache,SemiprimeD1ChildTensorTables.fromCache,ha,Bool.false_eq_true,ite_false]
  | true =>
    simp only [fromCache,SemiprimeD1ChildTensorTables.fromCache,ha,ite_true]
    change (⟨_,(SemiprimeD1ChildTableCopyTape.acquire old extra p _ ⟨parent,0⟩ _).table⟩ : (d : ℕ) × Table d)=_
    rw [SemiprimeD1ChildTableCopyTape.acquire_table]
    rfl

/-- Complete actual activated-table budget, with repeated serialization retained. -/
def cacheBudget (old : Context) (extra : List ℕ) (p D I : ℕ) : ℕ :=
  (D*(4*D+7)+1+SemiprimeD1ChildTableCopyTape.tapeBudget I+
    SemiprimeD1ChildTableCopy.liftBudget old extra p+12)*2^D+D+
    (9*p+(extra++old.axes).prod+13)+5

/-- Only actual degree/shape inputs are used; no table read or copy-clock advice. -/
theorem fromCache_clock {n F a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (data : SemiprimeD1ChildPortPullback.Acquired n F a arity) (v : Fin (n+F))
    (old : Context) (extra : List ℕ) (p D : ℕ)
    (table : Table (SemiprimeD1ChildTableOrder.acquire owner data v).old.length)
    (hg : Good old table) (he : 0<extra.prod)
    (ho : (SemiprimeD1ChildTableOrder.acquire owner data v).old.length ≤ D)
    (hc : (SemiprimeD1ChildTableOrder.acquire owner data v).child.length ≤ D) :
    (fromCache owner data v old extra p table).clock ≤
      (SemiprimeD1ChildTableOrder.acquire owner data v).clock+cacheBudget old extra p D (storage table) := by
  let ports:=SemiprimeD1ChildTableOrder.acquire owner data v
  have horder : ports.order.length ≤ D := (SemiprimeD1ChildTableOrder.order_length owner data v).le.trans ho
  have hcopy:=SemiprimeD1ChildTableCopyTape.acquire_clock old extra p ports.child.length
    (⟨table,0⟩ : Acquired ports.old.length) ports.order hg he
  have hcoef : ports.order.length*(4*ports.child.length+7)+1+
      SemiprimeD1ChildTableCopyTape.tapeBudget (storage table)+
      SemiprimeD1ChildTableCopy.liftBudget old extra p+12 ≤
    D*(4*D+7)+1+SemiprimeD1ChildTableCopyTape.tapeBudget (storage table)+
      SemiprimeD1ChildTableCopy.liftBudget old extra p+12 := by gcongr
  have hpow: (2:ℕ)^ports.child.length ≤ 2^D := Nat.pow_le_pow_right (by decide) hc
  have hprod:=Nat.mul_le_mul hcoef hpow
  have hu : (unit ⟨extra++old.axes,p⟩).clock ≤ 9*p+(extra++old.axes).prod+13 :=
    unit_clock (⟨extra++old.axes,p⟩ : Context)
  dsimp only at hcopy
  simp only [Nat.zero_add] at hcopy
  change (fromCache owner data v old extra p table).clock ≤ ports.clock+cacheBudget old extra p D (storage table)
  dsimp only [fromCache]
  split
  · change ports.clock+(SemiprimeD1ChildTableCopyTape.acquire old extra p ports.child.length
      ⟨table,0⟩ ports.order).clock+5 ≤ _
    unfold cacheBudget
    omega
  · change ports.clock+(unit ⟨extra++old.axes,p⟩).clock+5 ≤ _
    unfold cacheBudget
    omega

/-- Increasing literal input inventory only enlarges the numerical cache envelope. -/
theorem cacheBudget_mono (old : Context) (extra : List ℕ) (p D : ℕ) {I J : ℕ}
    (h : I ≤ J) : cacheBudget old extra p D I ≤ cacheBudget old extra p D J := by
  unfold cacheBudget SemiprimeD1ChildTableCopyTape.tapeBudget
  gcongr

end RiemannGaussian.SemiprimeD1ChildTensorTablesTape
