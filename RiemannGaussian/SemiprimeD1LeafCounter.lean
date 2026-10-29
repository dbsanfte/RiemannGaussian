/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTables
import RiemannGaussian.SemiprimeD1JetAffineCoefficientBounds

/-! # Actual eager leaf contraction from literal local tensor tables
Only ordered native port lists and literal current coefficient-word tables are
runtime inputs. Each global assignment is gathered by paid list reads, evaluated
by physical table lookup/products, and stored once. Actual physical sums then
contract the complete table. Native index/control lowering remains separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1LeafCounter
open scoped BigOperators
open SemiprimeD1JetAxes SemiprimeD1JetInterpretation SemiprimeD1JetOperations
/-- Physical current-context coefficient vector and its retained report. -/
abbrev JetRun := SemiprimeD1JetRingBits.Run

/-- A literal local tensor and its actual ordered global variable indices. -/
structure Vertex where
  /-- Actual ordered global bit indices, never an entry evaluator closure. -/
  ports : List ℕ
  /-- Entire current local tensor table. -/
  table : SemiprimeD1TensorTables.Table ports.length

/-- Actual data well-formedness: every local port is a global variable. -/
def WellFormed (M : ℕ) (vertices : List Vertex) : Prop :=
  ∀v∈vertices,∀p∈v.ports,p<M

/-- Every actual stored table is canonical in the current context. -/
def Good (ctx : Context) (vertices : List Vertex) : Prop :=
  ∀v∈vertices,SemiprimeD1TensorTables.Good ctx v.table

/-- One actual Boolean list-read report. -/
structure BitRead where
  /-- Copied selected bit, with false default. -/
  bit : Bool
  /-- Visited list cells and finite branch/copy charges. -/
  clock : ℕ

/-- Bounded actual global assignment read, not a semantic assignment callback. -/
def readBit : List Bool → ℕ → BitRead
  | [],_ => ⟨false,1⟩
  | b::_,0 => ⟨b,3⟩
  | _::bs,i+1 => let tail:=readBit bs i;⟨tail.bit,tail.clock+3⟩

/-- Actual bit reads preserve literal list values and defaults. -/
theorem readBit_value (bits : List Bool) (i : ℕ) :
    (readBit bits i).bit=(bits[i]?).getD false := by
  induction bits generalizing i with
  | nil => simp [readBit]
  | cons b bs ih => cases i <;> simp [readBit,ih]

/-- The complete actual local assignment and retained read/copy reports. -/
structure Gathered where
  /-- Local assignment in the literal port ordering. -/
  bits : List Bool
  /-- Every selected global read and copied local cell. -/
  clock : ℕ

/-- Gather each local bit exactly once by its actual ordered port index. -/
def gather (bits : List Bool) : List ℕ → Gathered
  | [] => ⟨[],1⟩
  | p::ps =>
    let head:=readBit bits p
    let tail:=gather bits ps
    ⟨head.bit::tail.bits,head.clock+tail.clock+3⟩

/-- Gathered assignment size is exactly the literal local scope. -/
theorem gather_length (bits : List Bool) (ports : List ℕ) :
    (gather bits ports).bits.length=ports.length := by
  induction ports with
  | nil => rfl
  | cons p ps ih => simp [gather,ih]

/-- Every gathered bit is the original actual global read. -/
theorem gather_value (bits : List Bool) (ports : List ℕ) :
    (gather bits ports).bits=ports.map (fun p => (bits[p]?).getD false) := by
  induction ports with
  | nil => rfl
  | cons p ps ih => simp [gather,readBit_value,ih]

/-- Actual local lookup, retaining the gathered assignment report. -/
def evaluateVertex (v : Vertex) (bits : List Bool) : JetRun :=
  let localBits:=gather bits v.ports
  let entry:=SemiprimeD1TensorTables.lookup v.table localBits.bits
  ⟨entry.words,localBits.clock+entry.clock+3⟩

/-- Proof-side local assignment; no function-valued entry occurs in runtime data. -/
def localAssignment {M : ℕ} (bits : Fin M→Bool) (v : Vertex) : Fin v.ports.length→Bool :=
  fun j => ((List.ofFn bits)[v.ports[j.val]]?).getD false

/-- Actual physical gather and lookup recovers the literal ordered-port tensor entry. -/
theorem evaluateVertex_value {M : ℕ} (v : Vertex) (bits : Fin M→Bool) :
    (evaluateVertex v (List.ofFn bits)).words=
      SemiprimeD1TensorTables.valueAt v.table (localAssignment bits v) := by
  change (SemiprimeD1TensorTables.lookup v.table (gather (List.ofFn bits) v.ports).bits).words=_
  rw [SemiprimeD1TensorTables.lookup_value _ _ (gather_length _ _)]
  congr 1
  funext j
  simp only [gather_value,List.getElem_map,localAssignment]

/-- The actual multiplicative assignment evaluation, with no entry-value oracle. -/
def evaluateAssignment (ctx : Context) : List Vertex → List Bool → JetRun
  | [],_ => SemiprimeD1JetAffineCoefficient.one ctx
  | v::vs,bits =>
    let head:=evaluateVertex v bits
    let tail:=evaluateAssignment ctx vs bits
    let out:=SemiprimeD1JetRingBits.mul ctx head.words tail.words
    ⟨out.words,head.clock+tail.clock+out.clock+3⟩

/-- Actual assignment evaluation equals the product of its literal local tensor values. -/
theorem evaluateAssignment_value {M : ℕ} (ctx : Context) (hpos : ∀q∈ctx.axes,0<q)
    (vertices : List Vertex) (bits : Fin M→Bool) :
    interpret ctx (evaluateAssignment ctx vertices (List.ofFn bits)).words=
      (vertices.map (fun v => interpret ctx (SemiprimeD1TensorTables.valueAt v.table (localAssignment bits v)))).prod := by
  induction vertices with
  | nil => simpa only [evaluateAssignment,List.map_nil,List.prod_nil] using
      SemiprimeD1JetAffineCoefficient.interpret_one ctx hpos
  | cons v vs ih =>
    change interpret ctx (SemiprimeD1JetRingBits.mul ctx
      (evaluateVertex v (List.ofFn bits)).words (evaluateAssignment ctx vs (List.ofFn bits)).words).words=_
    rw [interpret_mul ctx _ _ hpos,evaluateVertex_value,ih]
    rfl

/-- Physical contraction of every materialized global table leaf. -/
def sumTable (ctx : Context) : {n : ℕ} → SemiprimeD1TensorTables.Table n → JetRun
  | _,.leaf words => let out:=copyVector words;⟨out.1,out.2⟩
  | _,.fork low high =>
    let left:=sumTable ctx low
    let right:=sumTable ctx high
    let out:=SemiprimeD1JetRingBits.add ctx left.words right.words
    ⟨out.words,left.clock+right.clock+out.clock+3⟩

/-- Summing a literal table computes its complete Boolean assignment contraction. -/
theorem sumTable_value (ctx : Context) (hpos : ∀q∈ctx.axes,0<q) {n : ℕ}
    (table : SemiprimeD1TensorTables.Table n) :
    interpret ctx (sumTable ctx table).words=
      ∑bits : Fin n→Bool,interpret ctx (SemiprimeD1TensorTables.valueAt table bits) := by
  induction table with
  | leaf words => simp [sumTable,copyVector_value,SemiprimeD1TensorTables.valueAt]
  | @fork n low high ihlow ihhigh =>
    change interpret ctx (SemiprimeD1JetRingBits.add ctx (sumTable ctx low).words (sumTable ctx high).words).words=_
    rw [interpret_add ctx _ _ hpos,ihlow,ihhigh]
    rw [← (Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Bool)))]
    simp only [Fintype.sum_prod_type,Fintype.sum_bool,SemiprimeD1TensorTables.valueAt,
      Fin.consEquiv_apply,Fin.cons_zero,Fin.cons_succ,Bool.false_eq_true,ite_false,ite_true]
    exact add_comm _ _

/-- Every built table entry is the actual assignment producer result. -/
theorem build_valueAt (n : ℕ) (producer : List Bool→JetRun) (bits : Fin n→Bool) :
    SemiprimeD1TensorTables.valueAt (SemiprimeD1TensorTables.build n producer).table bits=
      (producer (List.ofFn bits)).words := by
  have hl:=SemiprimeD1TensorTables.lookup_value (SemiprimeD1TensorTables.build n producer).table
    (List.ofFn bits) (by simp)
  have hb:=SemiprimeD1TensorTables.build_value n producer (List.ofFn bits) (by simp)
  simpa only [List.getElem_ofFn] using hl.symm.trans hb

/-- Actual global eager table and its physically summed result. -/
structure LeafRun (M : ℕ) where
  /-- The entire actual assignment table; permitted subexponential-space storage. -/
  table : SemiprimeD1TensorTables.Table M
  /-- Physical contracted coefficient vector. -/
  words : List (List Bool)
  /-- All assignment-table producer/allocation and summation reports retained. -/
  clock : ℕ

/-- Eager leaf counter from literal original network data, without entry or count advice. -/
def run (M : ℕ) (ctx : Context) (vertices : List Vertex) : LeafRun M :=
  let table:=SemiprimeD1TensorTables.build M (evaluateAssignment ctx vertices)
  let total:=sumTable ctx table.table
  ⟨table.table,total.words,table.clock+total.clock+3⟩

/-- The executed leaf counter is the EXACT contraction of the actual literal network tables. -/
theorem run_value (M : ℕ) (ctx : Context) (hpos : ∀q∈ctx.axes,0<q) (vertices : List Vertex) :
    interpret ctx (run M ctx vertices).words=
      ∑bits : Fin M→Bool,(vertices.map (fun v => interpret ctx
        (SemiprimeD1TensorTables.valueAt v.table (localAssignment bits v)))).prod := by
  rw [run,sumTable_value ctx hpos]
  apply Finset.sum_congr rfl
  intro bits _
  rw [build_valueAt]
  exact evaluateAssignment_value ctx hpos vertices bits

end RiemannGaussian.SemiprimeD1LeafCounter
