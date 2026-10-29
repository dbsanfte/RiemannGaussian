/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1BinaryPublicAcquisition

/-! # Exact shared-metadata acquisition calls
The proof views below describe reached stores. The program acquires them through
actual nested calls; neither view nor any elapsed-time witness is a runtime input.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionComponents
open SemiprimeD1BinaryPublicAcquisition SemiprimeD1StackProcedureTrace
open SemiprimeMacroParameters

/-- Reached store after the complete original-input digit stage. -/
def afterDigits (bits : List Bool) : Stack→List Bool :=
  store (SemiprimeD1BinaryDigitAcquisitionExecution.result bits) (fun _=>[]) (fun _=>[])
/-- Reached store after constructing both constant words with shared metadata. -/
def afterFermat (bits : List Bool) : Stack→List Bool :=
  store (SemiprimeD1BinaryDigitAcquisitionExecution.result bits)
    (fun b=>SemiprimeD1StackFermatExecution.result bits (.inr b)) (fun _=>[])
/-- Final physical parameter/digit payload, retaining all original data. -/
def result (bits : List Bool) : Stack→List Bool :=
  store (SemiprimeD1BinaryDigitAcquisitionExecution.result bits)
    (fun b=>SemiprimeD1StackFermatExecution.result bits (.inr b))
    (fun i=>SemiprimeD1StackAxesExecution.result bits (.inr i))
/-- Constant local execution includes its actual final halt. -/
def fermatTime (n : ℕ) : ℕ := 14*transformLength n+6*transformExponent n+17
/-- Axis/depth local execution includes its actual final halt. -/
def axesTime (n : ℕ) : ℕ := 10*transformExponent n+12+
  SemiprimeD1StackAxesLoop.loopTime 0 (transformExponent n/2)
    (SemiprimeD1StackAxesArithmetic.odd (transformExponent n))

/-- Exact local constant trace starting from metadata ALREADY acquired. -/
theorem fermat_stage_run (bits : List Bool) :
    C.run Fermat.program (fermatTime bits.length)
      (⟨some (.inl .modStart),none,none,
        SemiprimeD1StackFermatComponents.data (SemiprimeD1StackTransformExecution.result bits)
          [] [] [] [] [],[]⟩:C.State Fermat.Stack Fermat.Label)=
      some (SemiprimeD1StackFermatExecution.done bits) := by
  obtain ⟨finish,hf,hout⟩:=SemiprimeD1StackFermatExecution.ready bits []
    (⟨some (.inl .modStart),none,none,
      SemiprimeD1StackFermatComponents.data (SemiprimeD1StackTransformExecution.result bits)
        [] [] [] [] [],[]⟩:C.State Fermat.Stack Fermat.Label) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run Fermat.program (.inl .halt) rfl
    (SemiprimeD1StackFermatExecution.result bits) [] finish hout
  rw [show fermatTime bits.length=
      (14*transformLength bits.length+6*transformExponent bits.length+16)+1 by
        unfold fermatTime;omega,SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh

/-- Exact local axes/depth trace starting from the SAME acquired metadata. -/
theorem axes_stage_run (bits : List Bool) :
    C.run Axes.program (axesTime bits.length)
      (⟨some (.inl .ready),none,none,
        SemiprimeD1StackAxesComponents.data (SemiprimeD1StackTransformExecution.result bits)
          [] [] [] [] [] [],[]⟩:C.State Axes.Stack Axes.Label)=
      some (SemiprimeD1StackAxesExecution.done bits) := by
  obtain ⟨finish,hf,hout⟩:=SemiprimeD1StackAxesExecution.ready bits []
    (⟨some (.inl .ready),none,none,
      SemiprimeD1StackAxesComponents.data (SemiprimeD1StackTransformExecution.result bits)
        [] [] [] [] [] [],[]⟩:C.State Axes.Stack Axes.Label) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run Axes.program (.inl .halt) rfl
    (SemiprimeD1StackAxesExecution.result bits) [] finish hout
  rw [show axesTime bits.length=
      (10*transformExponent bits.length+11+
        SemiprimeD1StackAxesLoop.loopTime 0 (transformExponent bits.length/2)
          (SemiprimeD1StackAxesArithmetic.odd (transformExponent bits.length)))+1 by
        unfold axesTime;omega,SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hh

/-- The WHOLE original-input digit acquisition is a real included call. -/
theorem digit_call (bits : List Bool) (hb : bits≠[]) :
    ∃t ≤ SemiprimeD1BinaryDigitAcquisitionExecution.timeBound bits,
      Runs program (t+1) (mainLabel .start) (input bits)
        (mainLabel .fermatCall) (afterDigits bits) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1BinaryDigitAcquisitionExecution.source_run bits hb
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program digitStack digitLabel Sum.inl_injective
    Digits.program (SemiprimeD1BinaryDigitAcquisition.mainLabel .start) (fun _=>rfl)
    (mainLabel .start) (mainLabel .fermatCall) rfl t (Digits.initial bits)
    (⟨none,none,none,SemiprimeD1BinaryDigitAcquisitionExecution.result bits,[]⟩:C.State Digits.Stack Digits.Label)
    (input bits) (afterDigits bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact False.elim (hk k rfl)
      · rcases k with k|k <;> rfl

/-- Both constants are constructed without repeating the metadata/digit stage. -/
theorem fermat_call (bits : List Bool) :
    Runs program (fermatTime bits.length+1) (mainLabel .fermatCall) (afterDigits bits)
      (mainLabel .axesCall) (afterFermat bits) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program fermatStack fermatLabel fermatStack_injective
    Fermat.program (.inl .modStart) (fun _=>rfl) (mainLabel .fermatCall) (mainLabel .axesCall) rfl
    (fermatTime bits.length)
    (⟨some (.inl .modStart),none,none,
      SemiprimeD1StackFermatComponents.data (SemiprimeD1StackTransformExecution.result bits)
        [] [] [] [] [],[]⟩:C.State Fermat.Stack Fermat.Label)
    (SemiprimeD1StackFermatExecution.done bits) (afterDigits bits) (afterFermat bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact fermat_stage_run bits
  · constructor
    · intro k
      rcases k with k|b
      · cases k <;> rfl
      · cases b <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      rcases k with k|b
      · cases k <;> rfl
      · rfl
    · intro k hk
      rcases k with k|k
      · rcases k with k|k
        · exact False.elim (hk (.inl k) rfl)
        · rfl
      · rcases k with b|i
        · exact False.elim (hk (.inr b) rfl)
        · rfl

/-- Both axes and depth are constructed with the shared metadata; ALL acquired
constant and digit cells are preserved by the actual included trace. -/
theorem axes_call (bits : List Bool) :
    Runs program (axesTime bits.length+1) (mainLabel .axesCall) (afterFermat bits)
      (mainLabel .done) (result bits) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program axesStack axesLabel axesStack_injective
    Axes.program (.inl .ready) (fun _=>rfl) (mainLabel .axesCall) (mainLabel .done) rfl
    (axesTime bits.length)
    (⟨some (.inl .ready),none,none,
      SemiprimeD1StackAxesComponents.data (SemiprimeD1StackTransformExecution.result bits)
        [] [] [] [] [] [],[]⟩:C.State Axes.Stack Axes.Label)
    (SemiprimeD1StackAxesExecution.done bits) (afterFermat bits) (result bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact axes_stage_run bits
  · constructor
    · intro k
      rcases k with k|i
      · cases k <;> rfl
      · fin_cases i <;> rfl
    · intro k _;rfl
  · constructor
    · intro k
      rcases k with k|i
      · cases k <;> rfl
      · rfl
    · intro k hk
      rcases k with k|k
      · rcases k with k|k
        · exact False.elim (hk (.inl k) rfl)
        · rfl
      · rcases k with b|i
        · rfl
        · exact False.elim (hk (.inr i) rfl)

end RiemannGaussian.SemiprimeD1BinaryPublicAcquisitionComponents
