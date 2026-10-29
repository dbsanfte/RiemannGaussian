/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWidthSetup
import RiemannGaussian.SemiprimeD1StackRecoveryWidthFinish
/-! # Whole actual two-metadata-word recovery-width template source
No grid size, width, gate value, polynomial evaluator or template is supplied.
The SAME fixed program acquires N by physical doubling, executes all64 gates,
emits every template cell and physically clears every arithmetic register.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWidthExecution
open SemiprimeD1StackRecoveryWidth SemiprimeD1StackRecoveryWidthEncoding
open SemiprimeD1StackRecoveryWidthPrimitives SemiprimeD1StackRecoveryWidthSetup
open SemiprimeD1StackRecoveryWidthLoop SemiprimeD1StackRecoveryWidthFinish SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary)
/-- Own whole source cap includes actual N acquisition, every real gate, W-value output, all64 drains and final halt. -/
def runBound (a M:Nat) :Nat:=setupTime a+64*gateCap a M (gridSize a)+finishBound a M (gridSize a)+1
/-- Actual empty front door has only acquired unary a and M, with N and ALL64 outputs generated inside. -/
theorem source_trace (a M:Nat) :
    ∃q≤runBound a M-1,Runs program q .start (input (unary a) (unary M)) .done (result a M) :=by
  have h0:=setup_run a M
  obtain ⟨q,hq,h1⟩:=gates_loop a M (gridSize a) 64 0 rfl
  obtain ⟨p,hp,h2⟩:=finish_run a M (gridSize a)
  have hwidth:V.value 63 a M (gridSize a)=SemiprimeD1RecoveryNodeBits.width a M:=
    SemiprimeD1StackRecoveryWidthPolynomial.last_original a M
  rw [hwidth] at h2
  refine ⟨_,?_,join (join h0 h1) h2⟩
  unfold runBound
  omega
/-- Actual whole halt clears flags and all real return cells within this SAME program's physically paid clock. -/
theorem source_run (a M:Nat) :
    ∃q≤runBound a M,SemiprimeD1StackCalls.run program q (initial (unary a) (unary M))=some (done a M) :=by
  obtain ⟨q,hq,h⟩:=source_trace a M
  obtain ⟨finish,hfin,hAt⟩:=h [] (initial (unary a) (unary M)) ⟨rfl,rfl,rfl⟩
  have hp:0<runBound a M:=by unfold runBound;omega
  refine ⟨q+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hfin,Option.bind_some]
  exact halt_run program .done rfl (result a M) [] finish hAt
/-- The genuine fixed72-role machine has the same complete VALUE-paid source execution certificate. -/
noncomputable def widthInTime (a M:Nat) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (initial (unary a) (unary M)))
      (some (SemiprimeD1StackCalls.configuration (done a M))) (runBound a M):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .a) (aux .output) .start program
  let h:=source_run a M
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Every returned FALSE cell equals the authoritative old original-dimension template, byte for byte. -/
theorem output_original (a M:Nat) :(done a M).data (aux .output)=
    List.replicate (SemiprimeD1RecoveryNodeBits.width a M) false:=rfl
/-- Grid cardinality was physically generated and remains paid/retained by VALUE. -/
theorem grid_acquired (a M:Nat) :(done a M).data (aux .grid)=unary (2^(a+1)):=rfl
/-- Both already acquired original metadata words survive the actual width computation. -/
theorem inputs_retained (a M:Nat) :(done a M).data (aux .a)=unary a ∧ (done a M).data (aux .m)=unary M:=⟨rfl,rfl⟩
/-- Every64-gate intermediate is physically cleared before the real source halt. -/
theorem registers_clear (a M:Nat) (g:W.Gate) :(done a M).data (reg g)=[]:=rfl
end RiemannGaussian.SemiprimeD1StackRecoveryWidthExecution
