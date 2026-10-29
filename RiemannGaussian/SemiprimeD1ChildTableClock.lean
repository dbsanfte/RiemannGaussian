/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ChildOldEntrySemantics
import RiemannGaussian.SemiprimeD1ChildStateResources

/-! # Actual eager old-table alignment and copied-child clock
Every cached lookup, alignment table and copied table is retained. Bounds here
are on the existing physical-arithmetic plus native-list reports, not a whole
address/tape clock. Metadata acquisition remains explicit in the order report.
-/
set_option autoImplicit false
set_option maxHeartbeats 120000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildTableClock
open SemiprimeD1JetAxes SemiprimeD1TensorTables SemiprimeD1ChildNetwork

/-- Whole cached lookup budget at the actual context and original table degree. -/
def lookupBudget (ctx : Context) (degree : ℕ) : ℕ := ctx.rank*(3*ctx.precision+4)+1+4*degree

/-- Lookup budget is monotone in the literal table degree. -/
theorem lookupBudget_mono (ctx : Context) (d D : ℕ) (h : d ≤ D) :
    lookupBudget ctx d ≤ lookupBudget ctx D :=
  Nat.add_le_add_left (Nat.mul_le_mul_left 4 h) _

/-- Actual eager reindex/copy clock, including all repeated literal table reads. -/
theorem copyTable_clock (ctx : Context) (ports : List ℕ) {degree : ℕ}
    (table : Table degree) (hg : Good ctx table) :
    (copyTable ports table).2 ≤ (lookupBudget ctx degree+7)*2^ports.length := by
  have h := build_clock ports.length (lookupBudget ctx degree) (lookup table)
    (fun bits _ => lookup_clock ctx table hg bits)
  change (build ports.length (lookup table)).clock+3 ≤ _
  omega

/-- Full old-table copy component before its already retained order report. -/
def cacheBudget (old : Context) (extra : List ℕ) (p D : ℕ) : ℕ :=
  (D*(4*D+7)+1+old.rank*(3*old.precision+4)+1+4*D+
    SemiprimeD1ChildTableCopy.liftBudget old extra p+12)*2^D+D+
    (9*p+(extra++old.axes).prod+13)+5

/-- Actual activation branch either constructs every copied entry or the
literal zero-port unit; no activation or table-value oracle is assumed. -/
theorem fromCache_clock {n F a : ℕ} {arity : Fin F → ℕ}
    (owner : ((e : Fin F)×Fin (arity e)) → Fin n)
    (data : SemiprimeD1ChildPortPullback.Acquired n F a arity) (v : Fin (n+F))
    (old : Context) (extra : List ℕ) (p D : ℕ)
    (table : Table (SemiprimeD1ChildTableOrder.acquire owner data v).old.length)
    (hg : Good old table) (he : 0 < extra.prod)
    (ho : (SemiprimeD1ChildTableOrder.acquire owner data v).old.length ≤ D)
    (hc : (SemiprimeD1ChildTableOrder.acquire owner data v).child.length ≤ D) :
    (SemiprimeD1ChildTensorTables.fromCache owner data v old extra p table).clock ≤
      (SemiprimeD1ChildTableOrder.acquire owner data v).clock+cacheBudget old extra p D := by
  let ports := SemiprimeD1ChildTableOrder.acquire owner data v
  have horder : ports.order.length ≤ D := (SemiprimeD1ChildTableOrder.order_length owner data v).le.trans ho
  have hcopy := SemiprimeD1ChildTableCopy.acquire_clock old extra p ports.child.length
    (⟨table,0⟩ : Acquired ports.old.length) ports.order hg he
  have hcoef : ports.order.length*(4*ports.child.length+7)+1+old.rank*(3*old.precision+4)+1+
      4*ports.old.length+SemiprimeD1ChildTableCopy.liftBudget old extra p+12 ≤
      D*(4*D+7)+1+old.rank*(3*old.precision+4)+1+4*D+
        SemiprimeD1ChildTableCopy.liftBudget old extra p+12 := by
    gcongr
  have hpow : (2:ℕ)^ports.child.length ≤ 2^D := Nat.pow_le_pow_right (by decide) hc
  have hprod := Nat.mul_le_mul hcoef hpow
  have hu := SemiprimeD1ChildTensorTables.unit_clock (⟨extra++old.axes,p⟩ : Context)
  dsimp only [SemiprimeD1ChildTensorTables.fromCache]
  split
  · change ports.clock+(SemiprimeD1ChildTableCopy.acquire old extra p ports.child.length
      ⟨table,0⟩ ports.order).clock+5 ≤ ports.clock+cacheBudget old extra p D
    dsimp only [cacheBudget]
    simp only [Nat.zero_add] at hcopy
    omega
  · change ports.clock+(SemiprimeD1ChildTensorTables.unit ⟨extra++old.axes,p⟩).clock+5 ≤ ports.clock+cacheBudget old extra p D
    have hu' : (SemiprimeD1ChildTensorTables.unit ⟨extra++old.axes,p⟩).clock ≤
        9*p+(extra++old.axes).prod+13 := hu
    dsimp only [cacheBudget]
    omega

/-- Fixed eager-table budget for one actual old child vertex. -/
def leftBudget (old : Context) (extra : List ℕ) (p D O v : ℕ) : ℕ :=
  2*O+(lookupBudget old D+7)*2^D+cacheBudget old extra p D+
    (lookupBudget ⟨extra++old.axes,p⟩ D+7)*2^D+D+v+12

/-- The actual old-vertex builder pays alignment, physical copied table and
canonical-port recopy separately. Its routing producer report is counted twice,
as the existing runtime invokes it twice. -/
theorem leftOne_clock {a : ℕ} (net : SemiprimeD1TensorNetwork.Network)
    (data : Pullback net a) (old : Context) (extra : List ℕ) (p D : ℕ)
    (v : Fin (net.leftCount+net.rows.length))
    (hg : SemiprimeD1TensorNetwork.Good old net) (he : 0 < extra.prod)
    (ho : (SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v).old.length ≤ D)
    (hc : (SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v).child.length ≤ D)
    (hp : (SemiprimeD1TensorNetwork.leftPorts (SemiprimeD1TensorNetworkLayout.childRows data.graph) v).length ≤ D)
    (hd : (parentVertex net v).ports.length ≤ D) :
    (leftOne net data old extra p v).2 ≤ leftBudget old extra p D
      (SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v).clock v.val := by
  let order := SemiprimeD1ChildTableOrder.acquire (SemiprimeD1TensorNetwork.owner net.rows) data v
  let parent := parentVertex net v
  let aligned := build order.old.length (lookup parent.table)
  let copied := SemiprimeD1ChildTensorTables.fromCache (SemiprimeD1TensorNetwork.owner net.rows)
    data v old extra p aligned.table
  let ports := SemiprimeD1TensorNetwork.leftPorts (SemiprimeD1TensorNetworkLayout.childRows data.graph) v
  have hparent := parentVertex_good old net hg v
  have haligned := build_clock order.old.length (lookupBudget old parent.ports.length)
    (lookup parent.table) (fun bits _ => lookup_clock old parent.table hparent bits)
  have haGood : Good old aligned.table := build_good old _ _ (fun bits _ => lookup_good old _ hparent bits)
  have hcClock := fromCache_clock (SemiprimeD1TensorNetwork.owner net.rows) data v old extra p D
    aligned.table haGood he ho hc
  have hcGood := SemiprimeD1ChildTensorTables.fromCache_good (SemiprimeD1TensorNetwork.owner net.rows)
    data v old extra p aligned.table haGood he
  have hcopy := copyTable_clock ⟨extra++old.axes,p⟩ ports copied.table hcGood
  have hdegree : copied.degree ≤ D := by
    dsimp only [copied,SemiprimeD1ChildTensorTables.fromCache]
    split
    · exact hc
    · exact Nat.zero_le _
  have hA : (lookupBudget old parent.ports.length+7)*2^order.old.length ≤
      (lookupBudget old D+7)*2^D := by
    apply Nat.mul_le_mul
    · exact Nat.add_le_add_right (lookupBudget_mono old _ D hd) 7
    · exact Nat.pow_le_pow_right (by decide) ho
  have hC : (lookupBudget ⟨extra++old.axes,p⟩ copied.degree+7)*2^ports.length ≤
      (lookupBudget ⟨extra++old.axes,p⟩ D+7)*2^D := by
    apply Nat.mul_le_mul
    · exact Nat.add_le_add_right (lookupBudget_mono ⟨extra++old.axes,p⟩ _ D hdegree) 7
    · exact Nat.pow_le_pow_right (by decide) hp
  have hleft : (leftOne net data old extra p v).2 =
      order.clock+aligned.clock+copied.clock+(copyTable ports copied.table).2+ports.length+v.val+12 := rfl
  have ha' : aligned.clock ≤ (lookupBudget old D+7)*2^D :=
    (Nat.le_trans (Nat.le_add_right aligned.clock 5) haligned).trans hA
  have hc' : copied.clock ≤ order.clock+cacheBudget old extra p D := hcClock
  have hr' : (copyTable ports copied.table).2 ≤
      (lookupBudget ⟨extra++old.axes,p⟩ D+7)*2^D := hcopy.trans hC
  have hports : ports.length ≤ D := hp
  rw [hleft]
  calc
    _ ≤ order.clock+(lookupBudget old D+7)*2^D+
        (order.clock+cacheBudget old extra p D)+
        (lookupBudget ⟨extra++old.axes,p⟩ D+7)*2^D+D+v.val+12 := by
      exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (le_refl order.clock) ha') hc') hr') hports)
          (le_refl v.val)) (le_refl 12)
    _ = _ := by unfold leftBudget;ring

end RiemannGaussian.SemiprimeD1ChildTableClock
