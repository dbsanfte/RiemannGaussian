/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildTableCopy
import RiemannGaussian.SemiprimeD1ChildTableOrder

/-! # Actual cached old-vertex tables in a child group
The original/current tensor is concrete literal data. Active vertices copy and
reindex it by the computed port cache; inactive vertices get the zero-port one
table. No truth callback is accepted, including for isolated old vertices.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1ChildTensorTables
open SemiprimeD1TensorTables SemiprimeD1JetAxes

/-- Concrete zero-port scalar-one table in every current coefficient coordinate. -/
def unit (ctx : Context) : Acquired 0 :=
  let one := SemiprimeD1JetScalarBits.reduce ctx.precision [true]
  let words := if ctx.rank=0 then [] else one.bits::List.replicate (ctx.rank-1) []
  ⟨.leaf words,one.clock+ctx.rank+8⟩

/-- All scalar-one coefficients are canonical at the actual target precision. -/
theorem unit_good (ctx : Context) : Good ctx (unit ctx).table := by
  change GoodWords ctx (if ctx.rank=0 then [] else
    (SemiprimeD1JetScalarBits.reduce ctx.precision [true]).bits::List.replicate (ctx.rank-1) [])
  split_ifs with hz
  · exact ⟨by simpa only [List.length_nil] using hz.symm,by simp⟩
  · refine ⟨by simp only [List.length_cons,List.length_replicate];omega,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact ⟨SemiprimeD1JetScalarBits.reduce_compact _ _,SemiprimeD1JetScalarBits.reduce_length _ _⟩
    · have he : w=[] := (List.mem_replicate.mp hw).2
      subst w
      exact ⟨True.intro,Nat.zero_le _⟩

/-- The zero-port unit is built from a literal bit and explicit zero cells. -/
theorem unit_clock (ctx : Context) : (unit ctx).clock≤9*ctx.precision+ctx.rank+13 := by
  have h := SemiprimeD1JetScalarBits.reduce_clock ctx.precision [true]
  change (SemiprimeD1JetScalarBits.reduce ctx.precision [true]).clock+ctx.rank+8≤_
  omega

/-- A concrete table whose degree is acquired from the actual physical mask/cache. -/
structure Result where
  /-- Zero if masked out; otherwise the actual child-local port count. -/
  degree : ℕ
  /-- Entire acquired literal table. -/
  table : Table degree
  /-- Complete cached-order, physical table-copy and new table allocation report. -/
  clock : ℕ

/-- The current parent table is supplied literally; all routing metadata is acquired
from the actual cached endpoint permutation, and every old coordinate is kept. -/
def fromCache {n F a : ℕ} {arity : Fin F→ℕ}
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (data : SemiprimeD1ChildPortPullback.Acquired n F a arity) (v : Fin (n+F))
    (old : Context) (extra : List ℕ) (p : ℕ)
    (parent : Table (SemiprimeD1ChildTableOrder.acquire owner data v).old.length) : Result :=
  let ports := SemiprimeD1ChildTableOrder.acquire owner data v
  if (data.activation.bits[v.val]?).getD false then
    let out := SemiprimeD1ChildTableCopy.acquire old extra p ports.child.length ⟨parent,0⟩ ports.order
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
    exact SemiprimeD1ChildTableCopy.acquire_good old extra p _ ⟨parent,0⟩ _ hp he
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
  exact SemiprimeD1ChildTableCopy.acquire_value old extra p _ ⟨parent,0⟩ _ bits hb

end RiemannGaussian.SemiprimeD1ChildTensorTables
