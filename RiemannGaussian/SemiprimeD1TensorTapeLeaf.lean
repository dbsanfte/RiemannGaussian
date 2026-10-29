/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeOriginal
import RiemannGaussian.SemiprimeD1LeafCounterBounds

/-! # Eager leaf contraction with actual sequential tape table reads
Each vertex call serializes its own literal table and scans both selected and
unselected subtrees. Physical products/sums retain every repeated read report.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1TensorTapeLeaf
open SemiprimeD1JetAxes SemiprimeD1LeafCounter
open SemiprimeD1LeafCounterBounds SemiprimeD1TensorTables

/-- Actual gathered local bits feed the sequential serialized-table backend. -/
def evaluateVertex (v : Vertex) (bits : List Bool) : JetRun :=
  let localBits:=gather bits v.ports
  let entry:=SemiprimeD1TensorTapeLookup.fromTable v.table localBits.bits
  ⟨entry.words,localBits.clock+entry.clock+3⟩

/-- Actual physical products of the actual tape-read vertex entries. -/
def evaluateAssignment (ctx : Context) : List Vertex → List Bool → JetRun
  | [],_ => SemiprimeD1JetAffineCoefficient.one ctx
  | v::vs,bits =>
    let head:=evaluateVertex v bits
    let tail:=evaluateAssignment ctx vs bits
    let out:=SemiprimeD1JetRingBits.mul ctx head.words tail.words
    ⟨out.words,head.clock+tail.clock+out.clock+3⟩

/-- Complete eager assignment enumeration, followed by physical jet addition. -/
def run (M : ℕ) (ctx : Context) (vertices : List Vertex) : LeafRun M :=
  let table:=build M (evaluateAssignment ctx vertices)
  let total:=sumTable ctx table.table
  ⟨table.table,total.words,table.clock+total.clock+3⟩

/-- One actual tape-backed read returns exactly the former literal table entry. -/
theorem evaluateVertex_words (v : Vertex) (bits : List Bool) :
    (evaluateVertex v bits).words=(SemiprimeD1LeafCounter.evaluateVertex v bits).words :=
  SemiprimeD1TensorTapeLookup.fromTable_words v.table _

/-- Every physical product has exactly the original word output. -/
theorem evaluateAssignment_words (ctx : Context) (vertices : List Vertex) (bits : List Bool) :
    (evaluateAssignment ctx vertices bits).words=
      (SemiprimeD1LeafCounter.evaluateAssignment ctx vertices bits).words := by
  induction vertices with
  | nil => rfl
  | cons v vs ih =>
    simp only [evaluateAssignment,SemiprimeD1LeafCounter.evaluateAssignment,evaluateVertex_words,ih]

/-- Eager construction preserves the complete literal table under word equality. -/
theorem build_table_congr (M : ℕ) (f g : List Bool → JetRun)
    (h : ∀bits,(f bits).words=(g bits).words) :
    (build M f).table=(build M g).table := by
  induction M generalizing f g with
  | zero => exact congrArg Table.leaf (h [])
  | succ M ih =>
    change Table.fork (build M (fun bits => f (false::bits))).table
      (build M (fun bits => f (true::bits))).table =
      Table.fork (build M (fun bits => g (false::bits))).table
      (build M (fun bits => g (true::bits))).table
    rw [ih _ _ (fun bits => h (false::bits)),ih _ _ (fun bits => h (true::bits))]

/-- The new executed leaf constructs exactly the original global assignment table. -/
theorem run_table (M : ℕ) (ctx : Context) (vertices : List Vertex) :
    (run M ctx vertices).table=(SemiprimeD1LeafCounter.run M ctx vertices).table :=
  build_table_congr M _ _ (evaluateAssignment_words ctx vertices)

/-- Full literal output equality, with no count/evaluator/Fits premise. -/
theorem run_words (M : ℕ) (ctx : Context) (vertices : List Vertex) :
    (run M ctx vertices).words=(SemiprimeD1LeafCounter.run M ctx vertices).words := by
  change (sumTable ctx (run M ctx vertices).table).words=
    (sumTable ctx (SemiprimeD1LeafCounter.run M ctx vertices).table).words
  rw [run_table]

/-- The actual network leaf uses the new backend on all literal vertices. -/
def leaf (ctx : Context) (net : SemiprimeD1TensorNetwork.Network) :
    LeafRun (SemiprimeD1TensorNetwork.edgeCount net) :=
  run (SemiprimeD1TensorNetwork.edgeCount net) ctx (SemiprimeD1TensorNetwork.vertices net)

/-- Closed literal network refinement, in particular for every WF/Good network. -/
theorem leaf_words (ctx : Context) (net : SemiprimeD1TensorNetwork.Network) :
    (leaf ctx net).words=(SemiprimeD1TensorNetwork.leaf ctx net).words :=
  run_words _ _ _

/-- Physical product output shape follows from the real executed multiplication. -/
theorem evaluateAssignment_good (ctx : Context) (vertices : List Vertex) (bits : List Bool) :
    GoodWords ctx (evaluateAssignment ctx vertices bits).words := by
  rw [evaluateAssignment_words]
  exact SemiprimeD1LeafCounterBounds.evaluateAssignment_good ctx vertices bits

/-- Fixed polynomial work for repeated full serialization and sequential table scans. -/
def tapeBudget (I : ℕ) : ℕ := 8*(I+1)*I+4

/-- Actual per-assignment report envelope, retaining every repeated table read. -/
def assignmentBudget (M : ℕ) (ctx : Context) (vertices : List Vertex) (I : ℕ) : ℕ :=
  oneBudget ctx+scopeSize vertices*(3*M+4)+
    vertices.length*(tapeBudget I+productBudget ctx+7)

/-- Internal bound uses literal stored input inventory, not an entry-clock oracle. -/
theorem evaluateVertex_clock (M : ℕ) (v : Vertex) (bits : List Bool) (hb : bits.length=M)
    (I : ℕ) (hi : storage v.table ≤ I) :
    (evaluateVertex v bits).clock ≤ v.ports.length*(3*M+4)+tapeBudget I+4 := by
  have hg:=gather_clock bits v.ports
  rw [hb] at hg
  have ht:=SemiprimeD1TensorTapeLookup.fromTable_storage_clock v.table (gather bits v.ports).bits
  have hs:=(SemiprimeD1TensorTapeCodec.tape_le_storage v.table).trans hi
  have ht' : (SemiprimeD1TensorTapeLookup.fromTable v.table (gather bits v.ports).bits).clock ≤ tapeBudget I := by
    apply ht.trans
    unfold tapeBudget
    gcongr
  change (gather bits v.ports).clock+
    (SemiprimeD1TensorTapeLookup.fromTable v.table (gather bits v.ports).bits).clock+3 ≤ _
  omega

/-- Closed product-loop bound from actual input shapes and literal inventories. -/
theorem evaluateAssignment_clock (M : ℕ) (ctx : Context) (vertices : List Vertex)
    (hg : SemiprimeD1LeafCounter.Good ctx vertices) (bits : List Bool) (hb : bits.length=M)
    (I : ℕ) (hi : ∀v∈vertices,storage v.table ≤ I) :
    (evaluateAssignment ctx vertices bits).clock ≤ assignmentBudget M ctx vertices I := by
  induction vertices with
  | nil =>
    have h:=SemiprimeD1JetScalarBits.reduce_clock ctx.precision [true]
    change (SemiprimeD1JetScalarBits.reduce ctx.precision [true]).clock+3*ctx.rank+3 ≤ _
    simp only [assignmentBudget,scopeSize,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.add_zero,oneBudget]
    omega
  | cons v vs ih =>
    have hv:=hg v List.mem_cons_self
    have hh:=evaluateVertex_clock M v bits hb I (hi v List.mem_cons_self)
    have ht:=ih (fun w hw => hg w (List.mem_cons_of_mem v hw))
      (fun w hw => hi w (List.mem_cons_of_mem v hw))
    have hhead : GoodWords ctx (evaluateVertex v bits).words := by
      rw [evaluateVertex_words]
      exact SemiprimeD1LeafCounterBounds.evaluateVertex_good ctx v hv bits
    have htail:=evaluateAssignment_good ctx vs bits
    have hm:=SemiprimeD1JetRingBounds.mul_clock ctx (evaluateVertex v bits).words
      (evaluateAssignment ctx vs bits).words ctx.precision hhead.1.le htail.1.le
      (fun w hw => (hhead.2 w hw).2) (fun w hw => (htail.2 w hw).2)
    change (evaluateVertex v bits).clock+(evaluateAssignment ctx vs bits).clock+
      (SemiprimeD1JetRingBits.mul ctx (evaluateVertex v bits).words (evaluateAssignment ctx vs bits).words).clock+3 ≤ _
    simp only [assignmentBudget,scopeSize,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul] at *
    dsimp [productBudget] at *
    omega

/-- All assignment enumeration, repeated serializations, products and sums are paid. -/
theorem run_clock (M : ℕ) (ctx : Context) (vertices : List Vertex)
    (hg : SemiprimeD1LeafCounter.Good ctx vertices) (I : ℕ)
    (hi : ∀v∈vertices,storage v.table ≤ I) :
    (run M ctx vertices).clock ≤
      (assignmentBudget M ctx vertices I+copyBudget ctx+additionBudget ctx+13)*2^M := by
  have hb:=build_clock M (assignmentBudget M ctx vertices I) (evaluateAssignment ctx vertices)
    (fun bits h => evaluateAssignment_clock M ctx vertices hg bits h I hi)
  have hgtable:=build_good ctx M (evaluateAssignment ctx vertices)
    (fun bits _ => evaluateAssignment_good ctx vertices bits)
  have hs:=sumTable_clock ctx _ hgtable
  have hp : 1 ≤ 2^M := Nat.one_le_two_pow
  change (build M (evaluateAssignment ctx vertices)).clock+
    (sumTable ctx (build M (evaluateAssignment ctx vertices)).table).clock+3 ≤ _
  nlinarith

/-- Original literal network data discharge the inventory premise internally. -/
theorem leaf_clock (ctx : Context) (net : SemiprimeD1TensorNetwork.Network)
    (hg : SemiprimeD1TensorNetwork.Good ctx net) :
    (leaf ctx net).clock ≤
      (assignmentBudget (SemiprimeD1TensorNetwork.edgeCount net) ctx
        (SemiprimeD1TensorNetwork.vertices net) (SemiprimeD1NetworkStateResources.inventory net)+
        copyBudget ctx+additionBudget ctx+13)*2^(SemiprimeD1TensorNetwork.edgeCount net) := by
  apply run_clock _ _ _ hg
  intro v hv
  have h:=SemiprimeD1TensorTapeOriginal.member_le_sum (SemiprimeD1TensorNetwork.vertices net)
    (fun w => storage w.table+w.ports.length+1) v hv
  unfold SemiprimeD1NetworkStateResources.inventory
  omega

end RiemannGaussian.SemiprimeD1TensorTapeLeaf
