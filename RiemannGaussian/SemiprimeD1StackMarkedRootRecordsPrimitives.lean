/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecords
/-! # Paid copies, reversals and physical parsers in the marked record source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsPrimitives
open SemiprimeD1StackMarkedRootRecords SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Concatenation in this one literal caller, retaining arbitrary real outer returns. -/
theorem join {m n : Nat} {pc mid finish : Label} {before between after : Stack → List Bool}
    (h : Runs program m pc before mid between) (g : Runs program n mid between finish after) :
    Runs program (m+n) pc before finish after :=
  runs_trans program m n pc mid finish before between after h g
/-- Every real copy reads a distinct retained source and target. -/
theorem copy_source_ne_target (site:Copy) : copySource site≠copyTarget site := by cases site <;> decide
/-- The real restoring scratch is disjoint from every copy target. -/
theorem copy_scratch_ne_target (site:Copy) : scratch≠copyTarget site := by cases site <;> decide
/-- The actual complete restoring-copy call charges all source cells and the real return. -/
theorem copy_call (site:Copy) (pc finish:Control)
    (hcode:program (ctl pc)=.call (copyLabel site 0) (ctl finish))
    (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (copySource site)=xs) (hy:before (copyTarget site)=ys) (hz:before scratch=[]) :
    Runs program (5*xs.length+4) (ctl pc) before (ctl finish)
      (Function.update before (copyTarget site) (xs++ys)) := by
  apply included_call program (copyStack site) (copyLabel site) (copy_injective site)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (ctl pc) (ctl finish) hcode (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs ys []) (SemiprimeD1StackCopy.done xs (xs++ys)) before _
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words xs ys none
  · constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hz
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update before (copyTarget site) (xs++ys) (copySource site)=xs
        rw [Function.update_of_ne (copy_source_ne_target site),hx]
      · exact Function.update_self _ _ _
      · change Function.update before (copyTarget site) (xs++ys) scratch=[]
        rw [Function.update_of_ne (copy_scratch_ne_target site),hz]
    · intro k hk
      exact Function.update_of_ne (fun he=>hk 1 he.symm) _ _
/-- Each real reversal has distinct input and output roles. -/
theorem reverse_ne (second:Bool) : reverseStack second 0≠reverseStack second 1 := by cases second <;> decide
/-- One real consuming reversal call includes every pop/push, EOF, halt and caller return. -/
theorem reverse_call (second:Bool) (pc finish:Control)
    (hcode:program (ctl pc)=.call (reverseLabel second 0) (ctl finish))
    (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (reverseStack second 0)=xs) (hy:before (reverseStack second 1)=ys) :
    Runs program (2*xs.length+3) (ctl pc) before (ctl finish)
      (Function.update (Function.update before (reverseStack second 0) [])
        (reverseStack second 1) (xs.reverse++ys)) := by
  apply included_call program (reverseStack second) (reverseLabel second) (reverse_injective second)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) (ctl pc) (ctl finish) hcode (2*xs.length+2)
    (SemiprimeD1StackReverseWord.state none xs ys) (SemiprimeD1StackReverseWord.done (xs.reverse++ys)) before _
  · rfl
  · rfl
  · exact SemiprimeD1StackReverseWord.reverse_run xs ys none
  · constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update (Function.update before (reverseStack second 0) [])
          (reverseStack second 1) (xs.reverse++ys) (reverseStack second 0)=[]
        rw [Function.update_of_ne (reverse_ne second),Function.update_self]
      · exact Function.update_self _ _ _
    · intro k hk
      rw [Function.update_of_ne (fun he=>hk 1 he.symm),Function.update_of_ne (fun he=>hk 0 he.symm)]
/-- One real included field parser consumes one frame and copies its literal word. -/
theorem parse_call (what:Field) (bank:Stack→List Bool) (word tail:List Bool)
    (hi:bank (fieldReader what)=frame word tail) (ho:bank (fieldTarget what)=[])
    (hs:bank (aux .fieldScratch)=[]) (hv:bank (aux .status)=[]) :
    Runs program (8*word.length+7) (ctl (.field what)) bank (ctl (.valid what))
      (Function.update (Function.update (Function.update bank (fieldReader what) tail)
        (fieldTarget what) word) (aux .status) [true]) :=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:Link.DataRel (fieldStack what) bank before.store bank :=by
    constructor
    · intro k;rcases k with k|k
      · cases k <;> simp [fieldStack,before,SemiprimeD1TensorTapeFieldBytecode.initial,
          SemiprimeD1TensorTapeFieldMachine.contents,hi,ho,hs]
      · cases k;exact hv
    · intro k _;rfl
  apply included_call program (fieldStack what) (fieldLabel what) (field_injective what) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (ctl (.field what)) (ctl (.valid what)) rfl
    (8*word.length+6) before after _ _ rfl rfl
    (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin
  have h0:=Link.data_update (fieldStack what) (field_injective what) bank before.store bank hin (.inl .input) tail
  have h1:=Link.data_update (fieldStack what) (field_injective what) bank _ _ h0 (.inl .output) word
  have h2:=Link.data_update (fieldStack what) (field_injective what) bank _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update before.store (.inl .input) tail)
      (.inl .output) word) (.inr ()) [true]=after.store :=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  simpa only [he,fieldStack] using h2
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsPrimitives
