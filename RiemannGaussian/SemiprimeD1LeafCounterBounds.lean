/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1LeafCounter
import RiemannGaussian.SemiprimeD1JetRingBounds

/-! # Actual eager leaf reports, canonical data and storage
All scalar arithmetic is the physical existing word backend. Literal index-list
reads, table construction/copies and every producer report are retained. Native
Nat indices/route/control and full tape/address simulation remain explicit.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1LeafCounterBounds
open SemiprimeD1LeafCounter SemiprimeD1JetAxes
open SemiprimeD1TensorTables (GoodWords)

/-- Literal physical word vector unit has canonical shape and width. -/
theorem one_good (ctx : Context) : GoodWords ctx (SemiprimeD1JetAffineCoefficient.one ctx).words := by
  have hg:=SemiprimeD1JetAffineCoefficientBounds.one_good ctx
  refine ⟨hg.1,?_⟩
  intro w hw
  refine ⟨?_,hg.2 w hw⟩
  rcases List.mem_map.mp hw with ⟨i,_,rfl⟩
  split_ifs
  · exact SemiprimeD1JetScalarBits.reduce_compact _ _
  · trivial

/-- Actual physical multiplication always returns canonical current-context data. -/
theorem mul_good (ctx : Context) (a b : List (List Bool)) :
    GoodWords ctx (SemiprimeD1JetRingBits.mul ctx a b).words :=
  ⟨SemiprimeD1JetRingBits.mul_shape _ _ _,fun w hw =>
    ⟨SemiprimeD1JetRingBits.mul_compact _ _ _ w hw,SemiprimeD1JetRingBits.mul_bounded _ _ _ w hw⟩⟩

/-- Actual physical addition always returns canonical current-context data. -/
theorem add_good (ctx : Context) (a b : List (List Bool)) :
    GoodWords ctx (SemiprimeD1JetRingBits.add ctx a b).words :=
  ⟨SemiprimeD1JetRingBits.add_shape _ _ _,fun w hw =>
    ⟨SemiprimeD1JetRingBits.add_compact _ _ _ w hw,SemiprimeD1JetRingBits.add_bounded _ _ _ w hw⟩⟩

/-- Actual lookup inherits the literal table's current-context invariant. -/
theorem evaluateVertex_good (ctx : Context) (v : Vertex)
    (hv : SemiprimeD1TensorTables.Good ctx v.table) (bits : List Bool) :
    GoodWords ctx (evaluateVertex v bits).words :=
  SemiprimeD1TensorTables.lookup_good ctx v.table hv _

/-- Every actual assignment product is canonical, with no output Fits premise. -/
theorem evaluateAssignment_good (ctx : Context) (vertices : List Vertex) (bits : List Bool) :
    GoodWords ctx (evaluateAssignment ctx vertices bits).words := by
  cases vertices with
  | nil => exact one_good ctx
  | cons v vs => exact mul_good _ _ _

/-- Every materialized global-assignment table entry is an actually executed canonical product. -/
theorem globalTable_good (M : ℕ) (ctx : Context) (vertices : List Vertex) :
    SemiprimeD1TensorTables.Good ctx
      (SemiprimeD1TensorTables.build M (evaluateAssignment ctx vertices)).table :=
  SemiprimeD1TensorTables.build_good ctx M _ (fun bits _ => evaluateAssignment_good ctx vertices bits)

/-- All physically summed literal tables preserve canonical shape. -/
theorem sumTable_good (ctx : Context) {n : ℕ} (table : SemiprimeD1TensorTables.Table n)
    (ht : SemiprimeD1TensorTables.Good ctx table) : GoodWords ctx (sumTable ctx table).words := by
  cases table with
  | leaf words => simpa only [sumTable,copyVector_value,SemiprimeD1TensorTables.Good] using ht
  | fork low high => exact add_good _ _ _

/-- The executed whole leaf counter derives canonical output directly from its actual table. -/
theorem run_good (M : ℕ) (ctx : Context) (vertices : List Vertex) :
    GoodWords ctx (run M ctx vertices).words :=
  sumTable_good ctx _ (globalTable_good M ctx vertices)

/-- Each actual assignment read visits at most the full assignment list. -/
theorem readBit_clock (bits : List Bool) (i : ℕ) : (readBit bits i).clock≤3*bits.length+1 := by
  induction bits generalizing i with
  | nil => simp [readBit]
  | cons b bs ih =>
    cases i with
    | zero => simp only [readBit,List.length_cons];omega
    | succ i => have h:=ih i;simp only [readBit,List.length_cons];omega

/-- Ordered port gathering pays every actual read and copied Boolean cell. -/
theorem gather_clock (bits : List Bool) (ports : List ℕ) :
    (gather bits ports).clock≤ports.length*(3*bits.length+4)+1 := by
  induction ports with
  | nil => simp [gather]
  | cons p ps ih =>
    have h:=readBit_clock bits p
    change (readBit bits p).clock+(gather bits ps).clock+3≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Current vector copy/report polynomial. -/
def copyBudget (ctx : Context) : ℕ := ctx.rank*(3*ctx.precision+4)+1

/-- Actual global-jet product/report polynomial. -/
def productBudget (ctx : Context) : ℕ :=
  SemiprimeD1JetRingBounds.mulBudget ctx.axes.length ctx.rank ctx.precision ctx.precision

/-- Actual global-jet addition/report polynomial. -/
def additionBudget (ctx : Context) : ℕ :=
  ctx.rank*(6*ctx.rank+11*ctx.precision+9*ctx.precision+17)+10*ctx.rank+5

/-- Physical unit acquisition/report polynomial. -/
def oneBudget (ctx : Context) : ℕ := 9*ctx.precision+3*ctx.rank+8

/-- One actual gathered local table entry has a closed original-data read/copy budget. -/
theorem evaluateVertex_clock (M : ℕ) (ctx : Context) (v : Vertex)
    (hv : SemiprimeD1TensorTables.Good ctx v.table) (bits : List Bool) (hb : bits.length=M) :
    (evaluateVertex v bits).clock≤v.ports.length*(3*M+9)+copyBudget ctx+4 := by
  have hg:=gather_clock bits v.ports
  have hl:=SemiprimeD1TensorTables.lookup_clock ctx v.table hv (gather bits v.ports).bits
  change (gather bits v.ports).clock+
    (SemiprimeD1TensorTables.lookup v.table (gather bits v.ports).bits).clock+3≤_
  rw [hb] at hg
  dsimp [copyBudget]
  nlinarith

/-- Total literal scope/index-list size, counting repeated local ports too. -/
def scopeSize (vertices : List Vertex) : ℕ := (vertices.map fun v => v.ports.length).sum

/-- Fixed polynomial assignment-work envelope in actual source dimensions. -/
def assignmentBudget (M : ℕ) (ctx : Context) (vertices : List Vertex) : ℕ :=
  oneBudget ctx+scopeSize vertices*(3*M+9)+vertices.length*(copyBudget ctx+productBudget ctx+8)

/-- Closed actual assignment producer work, without an entry-clock or Fits oracle. -/
theorem evaluateAssignment_clock (M : ℕ) (ctx : Context) (vertices : List Vertex)
    (hg : Good ctx vertices) (bits : List Bool) (hb : bits.length=M) :
    (evaluateAssignment ctx vertices bits).clock≤assignmentBudget M ctx vertices := by
  induction vertices with
  | nil =>
    have h:=SemiprimeD1JetScalarBits.reduce_clock ctx.precision [true]
    change (SemiprimeD1JetScalarBits.reduce ctx.precision [true]).clock+3*ctx.rank+3≤_
    simp only [assignmentBudget,scopeSize,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,
      Nat.add_zero,oneBudget]
    omega
  | cons v vs ih =>
    have hv:=hg v List.mem_cons_self
    have hh:=evaluateVertex_clock M ctx v hv bits hb
    have ht:=ih (fun w hw => hg w (List.mem_cons_of_mem v hw))
    have hhead:=evaluateVertex_good ctx v hv bits
    have htail:=evaluateAssignment_good ctx vs bits
    have hm:=SemiprimeD1JetRingBounds.mul_clock ctx (evaluateVertex v bits).words
      (evaluateAssignment ctx vs bits).words ctx.precision hhead.1.le htail.1.le
      (fun w hw => (hhead.2 w hw).2) (fun w hw => (htail.2 w hw).2)
    change (evaluateVertex v bits).clock+(evaluateAssignment ctx vs bits).clock+
      (SemiprimeD1JetRingBits.mul ctx (evaluateVertex v bits).words (evaluateAssignment ctx vs bits).words).clock+3≤_
    simp only [assignmentBudget,scopeSize,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul] at *
    dsimp [productBudget] at *
    omega

/-- Closed actual addition budget from the two canonical source vectors. -/
theorem add_clock (ctx : Context) (a b : List (List Bool)) (ha : GoodWords ctx a) (hb : GoodWords ctx b) :
    (SemiprimeD1JetRingBits.add ctx a b).clock≤additionBudget ctx :=
  SemiprimeD1JetRingBounds.add_clock ctx a b ctx.precision ha.1.le hb.1.le
    (fun w hw => (ha.2 w hw).2) (fun w hw => (hb.2 w hw).2)

/-- ALL actual recursive table-sum reports have the exact eager exponential scale. -/
theorem sumTable_clock (ctx : Context) {n : ℕ} (table : SemiprimeD1TensorTables.Table n)
    (ht : SemiprimeD1TensorTables.Good ctx table) :
    (sumTable ctx table).clock+(additionBudget ctx+3)≤
      (copyBudget ctx+additionBudget ctx+3)*2^n := by
  induction table with
  | leaf words =>
    have h:=copyVector_clock_le words ctx.precision (fun w hw => (ht.2 w hw).2)
    simp only [sumTable,ht.1,pow_zero,Nat.mul_one,copyBudget] at *
    omega
  | @fork n low high ihlow ihhigh =>
    have hl:=ihlow ht.1
    have hh:=ihhigh ht.2
    have ha:=add_clock ctx (sumTable ctx low).words (sumTable ctx high).words
      (sumTable_good ctx low ht.1) (sumTable_good ctx high ht.2)
    change (sumTable ctx low).clock+(sumTable ctx high).clock+
      (SemiprimeD1JetRingBits.add ctx (sumTable ctx low).words (sumTable ctx high).words).clock+3+
        (additionBudget ctx+3)≤_
    rw [pow_succ,←Nat.mul_assoc]
    omega

/-- Explicit original-dimension eager leaf work, with every source producer retained. -/
def budget (M : ℕ) (ctx : Context) (vertices : List Vertex) : ℕ :=
  (assignmentBudget M ctx vertices+copyBudget ctx+additionBudget ctx+13)*2^M

/-- The actual complete leaf call has a fixed polynomial times2^M report bound. -/
theorem run_clock (M : ℕ) (ctx : Context) (vertices : List Vertex) (hg : Good ctx vertices) :
    (run M ctx vertices).clock≤budget M ctx vertices := by
  have hb:=SemiprimeD1TensorTables.build_clock M (assignmentBudget M ctx vertices)
    (evaluateAssignment ctx vertices) (fun bits h => evaluateAssignment_clock M ctx vertices hg bits h)
  have hs:=sumTable_clock ctx _ (globalTable_good M ctx vertices)
  have hp : 1≤2^M := Nat.one_le_two_pow
  change (SemiprimeD1TensorTables.build M (evaluateAssignment ctx vertices)).clock+
    (sumTable ctx (SemiprimeD1TensorTables.build M (evaluateAssignment ctx vertices)).table).clock+3≤_
  dsimp [budget]
  nlinarith

/-- Actual allocated eager output-table storage, separately from held input tables. -/
theorem run_table_storage (M : ℕ) (ctx : Context) (vertices : List Vertex) :
    SemiprimeD1TensorTables.storage (run M ctx vertices).table+1≤
      (ctx.rank*(3*ctx.precision+4)+3)*2^M :=
  SemiprimeD1TensorTables.storage_bound ctx _ (globalTable_good M ctx vertices)

end RiemannGaussian.SemiprimeD1LeafCounterBounds
