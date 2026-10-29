/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftVertexFrames
/-! # Actual whole child-table call followed by exact canonical vertex serialization
Every coefficient, table/port field, frame and terminator is acquired by the
same literal136-role source. Parent-record extraction and activation selection
are still caller work; the front door contains exactly seven physical words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftVertexOriginal
open SemiprimeD1StackChildLiftVertex SemiprimeD1StackChildLiftVertexPrimitives
open SemiprimeD1StackChildLiftVertexFrames SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (tape vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace O
export SemiprimeD1StackChildLiftTableOriginal (done)
end O
namespace B
export SemiprimeD1StackChildLiftTableBounds (polynomial source_run_bounded)
end B
variable {d : ℕ}
/-- Complete eagerly lifted table in the actual canonical child scope. -/
def vertex (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : SemiprimeD1LeafCounter.Vertex :=
  ⟨ports,SemiprimeD1StackChildLiftTableMeaning.table old extra (SemiprimeBitArithmetic.bitValue newp) ports.length parent order⟩
/-- All134 fields are the actual whole-table halted bank; no record answer is an input. -/
def tableData (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : T.Stack→List Bool :=
  (O.done old extra oldp newp parent order (ports.map unary)).data
/-- Actual original six-word template and seventh canonical-scope word. -/
def originalInitial (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : C.State Stack Label :=
  initial (tape parent) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
    (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp (vectorBits (ports.map unary))
/-- Whole actual halted bank retains every source word and clears framing work. -/
def done (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : C.State Stack Label :=
  ⟨none,none,none,bank (tableData old extra oldp newp parent order ports)
    (SemiprimeD1StackVertexProduct.records [vertex old extra newp parent order ports]) [],[]⟩
/-- Own clock includes the actual source call/return, both field scans, tags and true halt. -/
def timeBound (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) : ℕ :=
  B.polynomial old extra oldp newp parent order (ports.map unary)+
    6*(tape (vertex old extra newp parent order ports).table).length+
    6*(SemiprimeD1StackVertexReadExecution.portTape ports).length+14
/-- The actual retained scope bytes are precisely the original canonical port codec. -/
theorem table_scope (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) :
    tableData old extra oldp newp parent order ports (SemiprimeD1StackVectorTable.counter .bank)=
      SemiprimeD1StackVertexReadExecution.portTape ports := rfl
/-- Entire acquired table bytes, without alignment or a second canonical recopy. -/
theorem table_output (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) :
    tableData old extra oldp newp parent order ports (SemiprimeD1StackVectorTable.aux .output)=
      tape (vertex old extra newp parent order ports).table := by
  exact (SemiprimeD1StackChildLiftTableOriginal.output_original old extra oldp newp parent order (ports.map unary)).trans
    (congrArg (fun n => tape (SemiprimeD1StackChildLiftTableMeaning.table old extra
      (SemiprimeBitArithmetic.bitValue newp) n parent order)) (List.length_map (f:=unary) (as:=ports)))
/-- Every actual whole136-source execution from its seven real operands reaches exact native record bytes. -/
theorem source_run (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (parent : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old parent)
    (order ports : List ℕ) :
    ∃t≤timeBound old extra oldp newp parent order ports,
      SemiprimeD1StackCalls.run program t (originalInitial old extra oldp newp parent order ports)=
        some (done old extra oldp newp parent order ports) := by
  obtain ⟨t,ht,hr,_hout⟩:=B.source_run_bounded old ho extra he oldp newp hp parent hg order (ports.map unary)
  have h0:=table_call t _ _ rfl rfl rfl rfl hr
  have h1:=frames_run (tableData old extra oldp newp parent order ports)
    (SemiprimeD1StackVertexReadExecution.portTape ports) (tape (vertex old extra newp parent order ports).table)
    (table_scope old extra oldp newp parent order ports) (table_output old extra oldp newp parent order ports)
  have hrecord:=record_original (vertex old extra newp parent order ports)
  change record (SemiprimeD1StackVertexReadExecution.portTape ports) (tape (vertex old extra newp parent order ports).table)=
    SemiprimeD1StackVertexProduct.records [vertex old extra newp parent order ports] at hrecord
  rw [hrecord] at h1
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  obtain ⟨finish,hfinish,hAt⟩:=h [] (originalInitial old extra oldp newp parent order ports) ⟨rfl,rfl,rfl⟩
  refine ⟨(t+1)+(6*(tape (vertex old extra newp parent order ports).table).length+
    6*(SemiprimeD1StackVertexReadExecution.portTape ports).length+12)+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    exact halt_run program (.local .done) rfl _ [] finish hAt
/-- The final bytes and every134 retained source word come from this SAME real whole run. -/
theorem output_original (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ) :
    (done old extra oldp newp parent order ports).data (aux .record)=
      SemiprimeD1StackVertexProduct.records [vertex old extra newp parent order ports] ∧
    (∀k,(done old extra oldp newp parent order ports).data (table k)=tableData old extra oldp newp parent order ports k) ∧
    (done old extra oldp newp parent order ports).data (aux .scratch)=[] := ⟨rfl,fun _=>rfl,rfl⟩
end RiemannGaussian.SemiprimeD1StackChildLiftVertexOriginal
