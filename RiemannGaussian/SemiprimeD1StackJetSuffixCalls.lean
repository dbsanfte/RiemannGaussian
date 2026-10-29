/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetSuffix

/-! # Actual fixed suffix-acquisition component calls -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackJetSuffixCalls
open SemiprimeD1StackJetSuffix
namespace Trace
export SemiprimeD1StackProcedureTrace (At Runs included_call runs_trans one_base halt_run)
end Trace
namespace M
export SemiprimeD1StackMultiplierLink (instruction DataRel data_initial data_update)
end M
local notation "ctl" => SemiprimeD1StackJetSuffix.control

/-- Source and reverse parsers never alias their own argument/work/output stacks. -/
theorem axesField_injective : Function.Injective axesFieldStack := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => cases a <;> cases b <;> simp [axesFieldStack] at h ⊢
    | inr b => cases a <;> simp [axesFieldStack] at h
  | inr a => cases b with
    | inl b => cases b <;> simp [axesFieldStack] at h
    | inr b => cases a; cases b; rfl

/-- Reverse parser's physical stacks are likewise distinct. -/
theorem reverseField_injective : Function.Injective reverseFieldStack := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => cases a <;> cases b <;> simp [reverseFieldStack] at h ⊢
    | inr b => cases a <;> simp [reverseFieldStack] at h
  | inr a => cases b with
    | inl b => cases b <;> simp [reverseFieldStack] at h
    | inr b => cases a; cases b; rfl

/-- Actual frame work/input/output are distinct for reverse-axis acquisition. -/
theorem reverseFrame_injective : Function.Injective reverseFrameStack := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [reverseFrameStack] at h ⊢

/-- Actual frame work/input/output are distinct for radix-record acquisition. -/
theorem radixFrame_injective : Function.Injective radixFrameStack := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [radixFrameStack] at h ⊢

/-- Actual frame work/input/output are distinct for axis-record acquisition. -/
theorem axisFrame_injective : Function.Injective axisFrameStack := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [axisFrameStack] at h ⊢

/-- Actual product inputs/work/output are distinct. -/
theorem product_injective : Function.Injective productStack := by
  intro a b h
  cases a <;> cases b <;> simp [productStack] at h ⊢

/-- A physical write changes exactly one fixed data stack. -/
@[simp] theorem update_data (axes reverseAxes axis radix product records scratch valid xs : List Bool)
    (k : Stack) : Function.update (data axes reverseAxes axis radix product records scratch valid) k xs=
      data (if k=.axes then xs else axes) (if k=.reverseAxes then xs else reverseAxes)
        (if k=.axis then xs else axis) (if k=.radix then xs else radix)
        (if k=.product then xs else product) (if k=.records then xs else records)
        (if k=.scratch then xs else scratch) (if k=.valid then xs else valid) := by
  funext j
  cases k <;> cases j <;> simp [data]

/-- Every actual included frame call updates ONLY its literal output stack.
All equation hypotheses concern the fixed instruction table/actual input bytes;
concrete callers below discharge them internally. -/
theorem frame_call (stack : Fin 3 → Stack) (label : Fin 11 → Label)
    (hinj : Function.Injective stack)
    (hcode : ∀l,code (label l)=M.instruction stack label (SemiprimeD1StackFrame.code l))
    (pc next : Control) (hcall : code (ctl pc)=.call (label 0) (ctl next))
    (bank : Stack → List Bool) (word tail : List Bool)
    (hin : ∀i,bank (stack i)=SemiprimeD1StackFrame.payload word tail [] i) :
    Trace.Runs code (6*word.length+5) (ctl pc) bank (ctl next)
      (Function.update bank (stack 1) (SemiprimeSourceHistogramKeyBits.frame word tail)) := by
  let source := SemiprimeD1StackFrame.state 0 none word tail []
  let result := SemiprimeD1StackFrame.done word (SemiprimeSourceHistogramKeyBits.frame word tail)
  have hd : M.DataRel stack bank source.store bank := ⟨hin,fun _ _ => rfl⟩
  have hu := M.data_update stack hinj bank source.store bank hd 1
    (SemiprimeSourceHistogramKeyBits.frame word tail)
  have hs : Function.update source.store 1 (SemiprimeSourceHistogramKeyBits.frame word tail)=result.store := by
    funext i
    fin_cases i <;> simp [source,result,SemiprimeD1StackFrame.state,SemiprimeD1StackFrame.done,
      SemiprimeD1StackFrame.payload,Function.update]
  rw [hs] at hu
  simpa only [show 6*word.length+4+1=6*word.length+5 by omega] using
    Trace.included_call code stack label hinj SemiprimeD1StackFrame.code 0 hcode
      (ctl pc) (ctl next) hcall (6*word.length+4) source result bank _ rfl rfl
      (SemiprimeD1StackFrame.frame_words word tail none) hd hu

/-- Original-axis field is actually parsed, with the true flag physically written. -/
theorem axes_read (word tail reverseAxes radix product records : List Bool) :
    Trace.Runs code (8*word.length+7) (ctl .readAxis)
      (data (SemiprimeSourceHistogramKeyBits.frame word tail) reverseAxes [] radix product records [] [])
      (ctl .axisRead) (data tail reverseAxes word radix product records [] [true]) := by
  have hr := SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  simpa only [List.cons_append,List.nil_append,show 8*word.length+6+1=8*word.length+7 by omega] using
    Trace.included_call code axesFieldStack axesField axesField_injective F.code
      (F.active .tagPop (none,false)) (fun _ => rfl) (ctl .readAxis) (ctl .axisRead) rfl
      (8*word.length+6) _ _
      (data (SemiprimeSourceHistogramKeyBits.frame word tail) reverseAxes [] radix product records [] [])
      (data tail reverseAxes word radix product records [] [true]) rfl rfl hr
      (by constructor
          · intro k; cases k with
            | inl k => cases k <;> rfl
            | inr k => cases k; rfl
          · intro k hk; rfl)
      (by constructor
          · intro k; cases k with
            | inl k => cases k <;> rfl
            | inr k => cases k; rfl
          · intro k hk; cases k with
            | axes => exact (hk (.inl .input) rfl).elim
            | reverseAxes => rfl
            | axis => exact (hk (.inl .output) rfl).elim
            | radix => rfl
            | product => rfl
            | records => rfl
            | scratch => exact (hk (.inl .scratch) rfl).elim
            | valid => exact (hk (.inr ()) rfl).elim)

/-- Actual axis framing creates the reverse-axis field cache, preserving its input. -/
theorem reverse_frame (axes reverseAxes word radix product records : List Bool) :
    Trace.Runs code (6*word.length+5) (ctl .reverseFrame)
      (data axes reverseAxes word radix product records [] [])
      (ctl .clearAxis) (data axes (SemiprimeSourceHistogramKeyBits.frame word reverseAxes)
        word radix product records [] []) := by
  have h := frame_call reverseFrameStack reverseFrame reverseFrame_injective (fun _ => rfl)
    .reverseFrame .clearAxis rfl (data axes reverseAxes word radix product records [] []) word reverseAxes
    (by intro k; fin_cases k <;> rfl)
  simpa [reverseFrameStack,update_data] using h

/-- Reverse-axis input fields are actually parsed into counters and a physical true flag. -/
theorem reverse_read (word tail axes radix product records : List Bool) :
    Trace.Runs code (8*word.length+7) (ctl .readReverse)
      (data axes (SemiprimeSourceHistogramKeyBits.frame word tail) [] radix product records [] [])
      (ctl .reverseRead) (data axes tail word radix product records [] [true]) := by
  have hr := SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []
  simpa only [List.cons_append,List.nil_append,show 8*word.length+6+1=8*word.length+7 by omega] using
    Trace.included_call code reverseFieldStack reverseField reverseField_injective F.code
      (F.active .tagPop (none,false)) (fun _ => rfl) (ctl .readReverse) (ctl .reverseRead) rfl
      (8*word.length+6) _ _
      (data axes (SemiprimeSourceHistogramKeyBits.frame word tail) [] radix product records [] [])
      (data axes tail word radix product records [] [true]) rfl rfl hr
      (by constructor
          · intro k; cases k with
            | inl k => cases k <;> rfl
            | inr k => cases k; rfl
          · intro k hk; rfl)
      (by constructor
          · intro k; cases k with
            | inl k => cases k <;> rfl
            | inr k => cases k; rfl
          · intro k hk; cases k with
            | axes => rfl
            | reverseAxes => exact (hk (.inl .input) rfl).elim
            | axis => exact (hk (.inl .output) rfl).elim
            | radix => rfl
            | product => rfl
            | records => rfl
            | scratch => exact (hk (.inl .scratch) rfl).elim
            | valid => exact (hk (.inr ()) rfl).elim)

/-- Actual suffix-divisor record framing preserves the acquired divisor counter. -/
theorem radix_frame (axes reverseAxes word radix product records : List Bool) :
    Trace.Runs code (6*radix.length+5) (ctl .frameRadix)
      (data axes reverseAxes word radix product records [] [])
      (ctl .frameAxis) (data axes reverseAxes word radix product
        (SemiprimeSourceHistogramKeyBits.frame radix records) [] []) := by
  have h := frame_call radixFrameStack radixFrame radixFrame_injective (fun _ => rfl)
    .frameRadix .frameAxis rfl (data axes reverseAxes word radix product records [] []) radix records
    (by intro k; fin_cases k <;> rfl)
  simpa [radixFrameStack,update_data] using h

/-- Actual axis record framing prepends q before the already written suffix divisor. -/
theorem axis_frame (axes reverseAxes word radix product records : List Bool) :
    Trace.Runs code (6*word.length+5) (ctl .frameAxis)
      (data axes reverseAxes word radix product records [] [])
      (ctl .productCall) (data axes reverseAxes word radix product
        (SemiprimeSourceHistogramKeyBits.frame word records) [] []) := by
  have h := frame_call axisFrameStack axisFrame axisFrame_injective (fun _ => rfl)
    .frameAxis .productCall rfl (data axes reverseAxes word radix product records [] []) word records
    (by intro k; fin_cases k <;> rfl)
  simpa [axisFrameStack,update_data] using h

/-- The actual product body consumes q and acquires q*d, retaining d only. -/
theorem product_call (q d : ℕ) (axes reverseAxes records : List Bool) :
    ∃m≤5*(q*(2*d+3)+1)+1,Trace.Runs code m (ctl .productCall)
      (data axes reverseAxes (SemiprimeD1StackUnaryDivmod.unary q)
        (SemiprimeD1StackUnaryDivmod.unary d) [] records [] [])
      (ctl .clearRadix) (data axes reverseAxes [] (SemiprimeD1StackUnaryDivmod.unary d)
        (SemiprimeD1StackUnaryDivmod.unary (q*d)) records [] []) := by
  obtain ⟨m,hm,hr⟩ := SemiprimeD1StackUnaryProduct.product_run q d
  refine ⟨m+1,by omega,?_⟩
  apply Trace.included_call code productStack productLabel product_injective P.code P.entry (fun _ => rfl)
    (ctl .productCall) (ctl .clearRadix) rfl m _ _ _ _ rfl rfl hr
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk; cases k with
      | axes => rfl
      | reverseAxes => rfl
      | axis => exact (hk .multiplier rfl).elim
      | radix => exact (hk .multiplicand rfl).elim
      | product => exact (hk .product rfl).elim
      | records => rfl
      | scratch => exact (hk .scratch rfl).elim
      | valid => rfl

end RiemannGaussian.SemiprimeD1StackJetSuffixCalls
