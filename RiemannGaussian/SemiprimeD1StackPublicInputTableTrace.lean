/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputTable
import RiemannGaussian.SemiprimeD1StackStaticTableSpec
/-! # Concrete complete trace contract from the frozen actual input checker
There is no unknown checker/acquisition supplier in this instance. The entire
literal52-role source executes for every leaf, with its own proved bit clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicInputTableTrace
open SemiprimeD1StackPublicInputTable SemiprimeD1StackStaticTableSpec
/-- Postcondition of actual original-N/index arithmetic, never a runtime operand. -/
def answer (bits indexWord raw : List Bool) : Bool :=
  SemiprimeD1StackPublicInputMeaning.expected bits raw indexWord
/-- The frozen actual checker's full original-input quadratic bit allowance. -/
def budget (bits indexWord : List Bool) (width : Nat) : Nat :=
  1000000000000*(bits.length+width+indexWord.length+2)^2
/-- Physical template copy and raw reversal match the SAME frozen source input. -/
theorem initial_eq (bits raw indexWord : List Bool) :
    checkerInitial static (inputTemplate bits indexWord) raw=P.initial bits raw indexWord := by
  apply congrArg (fun d=>(⟨some .start,none,none,d,[]⟩:SemiprimeD1StackCalls.State P.Stack P.Label))
    (template_raw_update bits raw indexWord)
/-- The concrete compiler's checker contract is DISCHARGED by the frozen real
source_run_bounded, including active/inactive/first/nonfirst arithmetic cases. -/
theorem actual_trace (bits indexWord : List Bool) (hb : bits≠[]) :
    CheckerTrace static (inputTemplate bits indexWord) (answer bits indexWord) (budget bits indexWord) := by
  intro raw
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackPublicInputBounds.source_run_bounded bits raw indexWord hb
  refine ⟨t,ht,SemiprimeD1StackPublicInputState.done bits raw indexWord,rfl,rfl,?_,rfl⟩
  rw [initial_eq]
  exact hr
/-- Every initialized template field is paid by original N and actual index markers. -/
theorem template_cell_le (bits indexWord : List Bool) (k : P.Stack) :
    (inputTemplate bits indexWord k).length≤ bits.length+indexWord.length := by
  change ((P.initial bits [] indexWord).data k).length≤ bits.length+indexWord.length
  simpa only [List.length_nil,Nat.add_zero] using
    SemiprimeD1StackPublicInputBounds.initial_length bits [] indexWord k
/-- The frozen public initializer has ONLY its one original N input word. -/
theorem public_input_only (bits : List Bool) (k : SemiprimeD1BinaryPublicAcquisition.Stack) :
    SemiprimeD1BinaryPublicAcquisition.input bits k=
      if k=SemiprimeD1BinaryPublicAcquisition.digitStack
        (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input) then bits else [] := by
  have hi:=SemiprimeD1StackCalls.initial_correct
    (SemiprimeD1BinaryPublicAcquisition.digitStack (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input))
    (SemiprimeD1BinaryPublicAcquisition.digitStack
      (SemiprimeD1BinaryPublicAcquisition.Digits.bankStack SemiprimeD1StackDigitBank.output))
    (SemiprimeD1BinaryPublicAcquisition.mainLabel .start) SemiprimeD1BinaryPublicAcquisition.program bits
  have he:=hi.trans (SemiprimeD1BinaryPublicAcquisitionExecution.initial_configuration bits).symm
  have hd:=congrArg (fun cfg:SemiprimeD1BinaryPublicAcquisition.machine.Cfg=>cfg.stk (some k)) he
  exact hd.symm
/-- Exact physical template shape: binary N and descriptor index markers ONLY.
Every raw/result/arithmetic/cache/private/shadow role is initially empty. -/
theorem template_only (bits indexWord : List Bool) (k : P.Stack) :
    inputTemplate bits indexWord k=
      if k=.inl SemiprimeD1StackPublicInput.H.original then bits else if k=P.index then indexWord else [] := by
  rcases k with k|k
  · rcases k with k|k
    · change SemiprimeD1BinaryPublicAcquisition.input bits k=
        if (Sum.inl (Sum.inl k):P.Stack)=.inl SemiprimeD1StackPublicInput.H.original then bits
        else if (Sum.inl (Sum.inl k):P.Stack)=P.index then indexWord else []
      rw [public_input_only]
      simp only [SemiprimeD1StackPublicInputWidth.original,SemiprimeD1StackPublicInput.index,
        Sum.inl.injEq,Sum.inl_ne_inr,ite_false]
    · change (if k=SemiprimeD1StackInputWidth.Stack.indexCache then indexWord else [])=
        if (Sum.inl (Sum.inr k):P.Stack)=.inl SemiprimeD1StackPublicInput.H.original then bits
        else if (Sum.inl (Sum.inr k):P.Stack)=P.index then indexWord else []
      simp only [SemiprimeD1StackPublicInputWidth.original,SemiprimeD1StackPublicInput.index,
        Sum.inl.injEq,Sum.inr_ne_inl,Sum.inr.injEq,ite_false]
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · cases k;rfl
end RiemannGaussian.SemiprimeD1StackPublicInputTableTrace
