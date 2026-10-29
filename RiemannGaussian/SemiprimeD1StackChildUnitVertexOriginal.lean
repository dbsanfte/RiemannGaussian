/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildUnitVertexFrames
import RiemannGaussian.SemiprimeD1StackChildUnitVertexSpec
import RiemannGaussian.SemiprimeD1StackVertexProduct
/-! # Whole inactive vertex acquisition from two actual context headers
The same finite source acquires context dimensions, constructs the literal unit,
frames its table and emits every record bit. It takes no unit/table/rank advice.
Activation branching and the parent-stream loop remain separate caller work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildUnitVertexOriginal
open SemiprimeD1StackChildUnitVertex SemiprimeD1StackChildUnitVertexCalls
open SemiprimeD1StackChildUnitVertexFrames SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Actual original two-header input, before acquisition of either rank or precision markers. -/
def originalInitial (axes : List ℕ) (precision : List Bool) : C.State Stack Label :=
  initial (vectorBits (axes.map unary)) precision
/-- Full actual32-role halt; both transient flags and actual saved-return stack are empty. -/
def done (axes : List ℕ) (precision : List Bool) : C.State Stack Label :=
  ⟨none,none,none,result axes precision,[]⟩
/-- Own whole-source time pays both real producer calls, one table frame, six literal bits and true halt. -/
def timeBound (axes : List ℕ) (precision : List Bool) : ℕ :=
  1000*(SemiprimeD1StackJetContextBounds.resource axes precision+1)^2+
    SemiprimeD1StackJetUnitExecution.totalTime (width axes precision) (rank axes precision)+
    6*(tableWord axes precision).length+14
/-- The actual acquired unit table is byte-identical to the ENTIRE original inactive table. -/
theorem table_original (axes : List ℕ) (precision : List Bool) (hp : ∀q∈axes,0<q) :
    tableWord axes precision=tape (SemiprimeD1StackChildUnitVertexSpec.vertex (ctx axes precision)).table :=
  SemiprimeD1StackChildUnitVertexSpec.table_tape (ctx axes precision) hp
/-- Actual literal scope and record tags coincide with the existing canonical whole-vertex codec. -/
theorem record_original (axes : List ℕ) (precision : List Bool) (hp : ∀q∈axes,0<q) :
    recordWord axes precision=SemiprimeD1StackVertexProduct.records [SemiprimeD1StackChildUnitVertexSpec.vertex (ctx axes precision)] := by
  unfold recordWord
  rw [table_original axes precision hp]
  rfl
/-- SAME finite32-role source acquires the complete inactive unit record from ONLY original two-header words. -/
theorem source_run (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool) :
    ∃t≤timeBound axes precision,
      SemiprimeD1StackCalls.run program t (originalInitial axes precision)=some (done axes precision) := by
  obtain ⟨t,ht,h0⟩:=context_call axes hp precision
  have h1:=unit_call axes precision
  have h2:=assemble_run axes precision
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0 (runs_trans program _ _ _ _ _ _ _ _ h1 h2)
  obtain ⟨finish,hfinish,hAt⟩:=h [] (originalInitial axes precision) ⟨rfl,rfl,rfl⟩
  refine ⟨t+(SemiprimeD1StackJetUnitExecution.totalTime (width axes precision) (rank axes precision)+1+
    (6*(tableWord axes precision).length+11))+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    exact halt_run program (.local .done) rfl _ [] finish hAt
/-- Complete output and source run concern the SAME actual data bank and existing original codec. -/
theorem source_original (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool) :
    ∃t≤timeBound axes precision,
      SemiprimeD1StackCalls.run program t (originalInitial axes precision)=some (done axes precision) ∧
      (done axes precision).data (aux .record)=
        SemiprimeD1StackVertexProduct.records [SemiprimeD1StackChildUnitVertexSpec.vertex (ctx axes precision)] := by
  obtain ⟨t,ht,hr⟩:=source_run axes hp precision
  exact ⟨t,ht,hr,record_original axes precision hp⟩
end RiemannGaussian.SemiprimeD1StackChildUnitVertexOriginal
