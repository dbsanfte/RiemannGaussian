/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexRead

/-! # Exact executed vertex read from original physical argument tapes -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackVertexReadExecution
open SemiprimeD1StackVertexRead
open SemiprimeD1TensorTapeCodec (tape vectorBits)
namespace P
export SemiprimeD1StackProcedureTrace (At Runs included_call runs_trans halt_run)
end P
namespace M
export SemiprimeD1StackMultiplierLink (DataRel)
end M
local notation "ctl" => SemiprimeD1StackVertexRead.control

/-- Byte specification of already prepared unary original port indices. -/
def portTape (ports : List ℕ) : List Bool := vectorBits (ports.map (fun i => List.replicate i true))

/-- Original physical arguments; acquisition of these tapes remains a caller operation. -/
def input (v : SemiprimeD1LeafCounter.Vertex) (assignment portTail tableTail : List Bool) :
    Stack → List Bool :=
  data (portTape v.ports++portTail) assignment [] [] [] [] (tape v.table++tableTail) [] []

/-- Physical intermediate store: gathered bits are already the actual tree path. -/
def gathered (v : SemiprimeD1LeafCounter.Vertex) (assignment portTail tableTail : List Bool) :
    Stack → List Bool :=
  data portTail assignment [] [] [] (SemiprimeD1LeafCounter.gather assignment v.ports).bits
    (tape v.table++tableTail) [] []

/-- Exact output encoded jet vector and exact preserved original argument suffixes. -/
def output (v : SemiprimeD1LeafCounter.Vertex) (assignment portTail tableTail : List Bool) :
    Stack → List Bool :=
  data portTail assignment [] [] [] [] tableTail []
    (vectorBits (SemiprimeD1TensorTapeLeaf.evaluateVertex v assignment).words)

/-- Literal original local assignment matches the table reader's path width. -/
theorem gathered_drop (v : SemiprimeD1LeafCounter.Vertex) (assignment : List Bool) :
    (SemiprimeD1LeafCounter.gather assignment v.ports).bits.drop v.ports.length=[] := by
  rw [←SemiprimeD1LeafCounter.gather_length assignment v.ports]
  exact List.drop_length

/-- Exact byte payload equality, with no new evaluation/representation premise. -/
theorem lookup_words (v : SemiprimeD1LeafCounter.Vertex) (assignment : List Bool) :
    (SemiprimeD1TensorTables.lookup v.table (SemiprimeD1LeafCounter.gather assignment v.ports).bits).words=
      (SemiprimeD1TensorTapeLeaf.evaluateVertex v assignment).words := by
  exact (SemiprimeD1TensorTapeLookup.fromTable_words v.table _).symm

/-- Closed actual instruction budget, retaining both calls and final halt. -/
def budget (assignment ports tableTape : ℕ) : ℕ :=
  SemiprimeD1StackGatherBytecode.budget assignment ports+
    SemiprimeD1StackTreeBytecode.budget tableTape+3

/-- Actual gather call puts the original local bits directly on the tree path stack. -/
theorem gather_call (v : SemiprimeD1LeafCounter.Vertex) (assignment portTail tableTail : List Bool) :
    ∃m≤SemiprimeD1StackGatherBytecode.budget assignment.length (portTape v.ports).length+1,
      P.Runs code m (ctl .start) (input v assignment portTail tableTail)
        (ctl .gathered) (gathered v assignment portTail tableTail) := by
  obtain ⟨m,hm,hr⟩ := SemiprimeD1StackGatherBytecode.original_gather_run assignment v.ports portTail []
  simp only [List.append_nil] at hr
  refine ⟨m+1,?_,?_⟩
  · simpa only [portTape] using Nat.add_le_add_right hm 1
  apply P.included_call code gatherStack gatherLabel gatherStack_injective G.code G.entry
    (fun _ => rfl) (ctl .start) (ctl .gathered) rfl m _ _
    (input v assignment portTail tableTail) (gathered v assignment portTail tableTail) rfl rfl hr
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk
      cases k with
      | ports => exact (hk .input rfl).elim
      | assignment => exact (hk .assignment rfl).elim
      | reader => exact (hk .reader rfl).elim
      | scratch => exact (hk .scratch rfl).elim
      | accumulator => exact (hk .accumulator rfl).elim
      | path => exact (hk .output rfl).elim
      | tableTape => rfl
      | tasks => rfl
      | output => rfl

/-- Actual tree call scans selected/skipped subtrees and produces the original entry. -/
theorem tree_call (v : SemiprimeD1LeafCounter.Vertex) (assignment portTail tableTail : List Bool) :
    ∃m≤SemiprimeD1StackTreeBytecode.budget (tape v.table).length+1,
      P.Runs code m (ctl .gathered) (gathered v assignment portTail tableTail)
        (ctl .done) (output v assignment portTail tableTail) := by
  obtain ⟨m,hm,hr⟩ := SemiprimeD1StackTreeBytecode.tree_run v.table
    (SemiprimeD1LeafCounter.gather assignment v.ports).bits tableTail
  rw [gathered_drop,lookup_words] at hr
  refine ⟨m+1,by omega,?_⟩
  apply P.included_call code treeStack treeLabel treeStack_injective T.code T.entry
    (fun _ => rfl) (ctl .gathered) (ctl .done) rfl m _ _
    (gathered v assignment portTail tableTail) (output v assignment portTail tableTail) rfl rfl hr
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk
      cases k with
      | ports => rfl
      | assignment => rfl
      | reader => rfl
      | scratch => exact (hk .scratch rfl).elim
      | accumulator => rfl
      | path => exact (hk .path rfl).elim
      | tableTape => exact (hk .input rfl).elim
      | tasks => exact (hk .tasks rfl).elim
      | output => exact (hk .output rfl).elim

/-- Closed original vertex pipeline executes both literal callees, then cleanly halts. -/
theorem vertex_run (v : SemiprimeD1LeafCounter.Vertex) (assignment portTail tableTail : List Bool) :
    ∃m≤budget assignment.length (portTape v.ports).length (tape v.table).length,
      C.run code m ⟨some (ctl .start),none,none,input v assignment portTail tableTail,[]⟩=
      some ⟨none,none,none,output v assignment portTail tableTail,[]⟩ := by
  obtain ⟨m,hm,hg⟩ := gather_call v assignment portTail tableTail
  obtain ⟨n,hn,ht⟩ := tree_call v assignment portTail tableTail
  have both := P.runs_trans code m n _ _ _ _ _ _ hg ht
  obtain ⟨last,hr,hl⟩ := both []
    (⟨some (ctl .start),none,none,input v assignment portTail tableTail,[]⟩ : C.State Stack Label)
    ⟨rfl,rfl,rfl⟩
  have hend := P.halt_run code (ctl .done) rfl (output v assignment portTail tableTail) [] last hl
  refine ⟨m+n+1,by unfold budget; omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,hend]

end RiemannGaussian.SemiprimeD1StackVertexReadExecution
