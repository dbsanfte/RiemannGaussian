/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineOriginalInput
/-! # Whole original five-word actual affine acquisition, with its OWN complete source clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineExecution
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
namespace E
export SemiprimeD1StackRecoveryAffineEncoding (retained resultWords result done)
end E
namespace A
export SemiprimeD1StackRecoveryAffineOriginalInput (slopes slopes_run loop_run)
end A
/-- SAME whole Grid/true-q source, actual copied row reversal, every convolution source operation and true halt. -/
def timeBound (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):Nat:=
  SemiprimeD1StackRecoveryAffineSource.entryBound a M u selected t width+
    SemiprimeD1StackRecoveryAffineSlopes.runBound (A.slopes a M u selected width)+
    SemiprimeD1StackRecoveryAffineLoop.runBound (SemiprimeD1StackRecoveryAffineSource.counted a M u selected t width)
      width (E.retained a M u selected) (A.slopes a M u selected width).reverse [SemiprimeJetBits.oneWord]+1
/-- Complete fixed112-role source trace acquires exact native affine bytes internally from only five actual words. -/
theorem source_trace (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:bitValue t=selected.val):
    ∃s,s+1≤timeBound a M u selected t width ∧ Runs program s (.local .start)
      (input (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)
      (.local .done) (E.result a M u selected t width):=by
  obtain ⟨p,hp,h0⟩:=SemiprimeD1StackRecoveryAffineSource.entry_trace a M u selected t width ht
  have h1:=A.slopes_run a M u selected t width
  obtain ⟨q,hq,h2⟩:=A.loop_run a M u selected t width
  refine ⟨p+SemiprimeD1StackRecoveryAffineSlopes.runBound (A.slopes a M u selected width)+q,?_,
    SemiprimeD1StackRecoveryAffinePrimitives.join (SemiprimeD1StackRecoveryAffinePrimitives.join h0 h1) h2⟩
  unfold timeBound
  omega
/-- SAME actual finite source reaches its real halt with ALL104 original words, actual q and exact original array retained. -/
theorem source_run (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:bitValue t=selected.val):
    ∃s≤timeBound a M u selected t width,
      SemiprimeD1StackCalls.run program s (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width)=
        some (E.done a M u selected t width):=by
  obtain ⟨s,hs,h⟩:=source_trace a M u selected t width ht
  obtain ⟨finish,hf,hAt⟩:=h [] (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .done) rfl (E.result a M u selected t width) [] finish hAt
  refine ⟨s+1,hs,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh
/-- Whole genuine finite-machine certificate uses this SAME actual source and its SAME own complete budget. -/
noncomputable def affineInTime (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool)
    (ht:bitValue t=selected.val):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (List.replicate a true) (List.replicate M true) (List.replicate u true) t width))
      (some (SemiprimeD1StackCalls.configuration (E.done a M u selected t width))) (timeBound a M u selected t width):=by
  apply SemiprimeD1StackCalls.evalsCorrect (oldAux .originalA) (aux .array) (.local .start) program
  let h:=source_run a M u selected t width ht
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackRecoveryAffineExecution
