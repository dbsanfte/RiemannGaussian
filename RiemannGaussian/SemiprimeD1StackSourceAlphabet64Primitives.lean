/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Encoding
/-! # Real copy/reverse/trim/frame calls on the same30-role alphabet source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Primitives
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Same literal program trace fragments compose with arbitrary actual caller return cells. -/
theorem compose {m n:Nat} {pc mid finish:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between finish after) :
    Runs program (m+n) pc before finish after :=runs_trans program _ _ _ _ _ _ _ _ h g
/-- Every paid preserving-copy call changes only its actual destination. -/
theorem copy_call (part:Copy) (pc next:Label) (hc:program pc=.call (.copier part 0) next)
    (bank:Stack→List Bool) (hd:bank (copyStack part 1)=[]) (hs:bank (copyStack part 2)=[]) :
    Runs program (5*(bank (copyStack part 0)).length+4) pc bank next
      (Function.update bank (copyStack part 1) (bank (copyStack part 0))) :=by
  let before:=SemiprimeD1StackCopy.state 0 none (bank (copyStack part 0)) [] []
  let after:=SemiprimeD1StackCopy.done (bank (copyStack part 0)) (bank (copyStack part 0)++[])
  have hin:Link.DataRel (copyStack part) bank before.store bank:=by
    constructor
    · intro i;fin_cases i
      · rfl
      · exact hd
      · exact hs
    · intro k _;rfl
  apply included_call program (copyStack part) (Label.copier part) (copy_injective part)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*(bank (copyStack part 0)).length+3)
    before after _ _ rfl rfl (SemiprimeD1StackCopy.copy_words _ [] none) hin
  have h:=Link.data_update (copyStack part) (copy_injective part) bank before.store bank hin 1 (bank (copyStack part 0))
  have he:Function.update before.store 1 (bank (copyStack part 0))=after.store:=by
    dsimp only [after]
    rw [List.append_nil]
    funext i;fin_cases i <;> rfl
  simpa only [he] using h
/-- Each real reversal consumes only its source and prepends onto the actual destination. -/
theorem reverse_call (part:Reverse) (pc next:Label) (hc:program pc=.call (.reversal part 0) next)
    (bank:Stack→List Bool) :
    Runs program (2*(bank (reverseStack part 0)).length+3) pc bank next
      (Function.update (Function.update bank (reverseStack part 0) []) (reverseStack part 1)
        ((bank (reverseStack part 0)).reverse++bank (reverseStack part 1))) :=by
  let before:=SemiprimeD1StackReverseWord.state none (bank (reverseStack part 0)) (bank (reverseStack part 1))
  let after:=SemiprimeD1StackReverseWord.done ((bank (reverseStack part 0)).reverse++bank (reverseStack part 1))
  have hin:Link.DataRel (reverseStack part) bank before.store bank:=by
    constructor
    · intro i;fin_cases i <;> rfl
    · intro k _;rfl
  apply included_call program (reverseStack part) (Label.reversal part) (reverse_injective part)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) pc next hc (2*(bank (reverseStack part 0)).length+2)
    before after _ _ rfl rfl (SemiprimeD1StackReverseWord.reverse_run _ _ none) hin
  have h0:=Link.data_update (reverseStack part) (reverse_injective part) bank before.store bank hin 0 []
  have h1:=Link.data_update (reverseStack part) (reverse_injective part) bank _ _ h0 1
    ((bank (reverseStack part 0)).reverse++bank (reverseStack part 1))
  have he:Function.update (Function.update before.store 0 []) 1
      ((bank (reverseStack part 0)).reverse++bank (reverseStack part 1))=after.store:=by
    funext i;fin_cases i <;> rfl
  simpa only [he] using h1
/-- Literal fixed return target of each normalization call. -/
def afterTrim :Trim→Label | .id=>.reverseBits | .colour=>.frameColour
/-- The REAL frozen reducer.trim entry consumes actual reverse bits and emits canonical magnitude bytes. -/
theorem trim_call (kind:Trim) (bank:Stack→List Bool)
    (hl:bank (trimStack kind .left)=[]) (hr:bank (trimStack kind .right)=[]) :
    Runs program (SemiprimeD1StackReduceExecution.trimTime (bank (aux .trimScratch))+1) (.normalize kind) bank
      (afterTrim kind)
      (Function.update (Function.update bank (aux .trimScratch) []) (trimStack kind .output)
        (SemiprimeD1StackReduceExecution.trimReverse (bank (aux .trimScratch))++bank (trimStack kind .output))) :=by
  let before:=SemiprimeD1StackReduce.state (some .trim) none [] []
    (bank (aux .trimScratch)) (bank (trimStack kind .output))
  let after:=SemiprimeD1StackReduce.state none none [] [] []
    (SemiprimeD1StackReduceExecution.trimReverse (bank (aux .trimScratch))++bank (trimStack kind .output))
  have hin:Link.DataRel (trimStack kind) bank before.store bank:=by
    constructor
    · intro k;cases k
      · exact hl
      · exact hr
      · rfl
      · rfl
    · intro k _;rfl
  apply included_call program (trimStack kind) (Label.reducer kind) (trim_injective kind) R.code .trim
    (fun _=>rfl) (.normalize kind) _ rfl (SemiprimeD1StackReduceExecution.trimTime (bank (aux .trimScratch)))
    before after _ _ rfl rfl (SemiprimeD1StackReduceExecution.trim_run _ _ none) hin
  have h0:=Link.data_update (trimStack kind) (trim_injective kind) bank before.store bank hin .scratch []
  have h1:=Link.data_update (trimStack kind) (trim_injective kind) bank _ _ h0 .output
    (SemiprimeD1StackReduceExecution.trimReverse (bank (aux .trimScratch))++bank (trimStack kind .output))
  have he:Function.update (Function.update before.store .scratch []) .output
      (SemiprimeD1StackReduceExecution.trimReverse (bank (aux .trimScratch))++bank (trimStack kind .output))=after.store:=by
    funext k;cases k <;> rfl
  simpa only [he,show trimStack kind .scratch=aux .trimScratch from rfl] using h1
/-- Every actual Frame pays its input restoration and adds only that field before the existing buffer. -/
theorem frame_call (part:Frame) (pc next:Label) (hc:program pc=.call (.framer part 0) next)
    (bank:Stack→List Bool) (hs:bank (aux .frameScratch)=[]) :
    Runs program (6*(bank (frameStack part 0)).length+5) pc bank next
      (Function.update bank (aux .frameBuffer)
        (SemiprimeSourceHistogramKeyBits.frame (bank (frameStack part 0)) (bank (aux .frameBuffer)))) :=by
  let before:=SemiprimeD1StackFrame.state 0 none (bank (frameStack part 0)) (bank (aux .frameBuffer)) []
  let after:=SemiprimeD1StackFrame.done (bank (frameStack part 0))
    (SemiprimeSourceHistogramKeyBits.frame (bank (frameStack part 0)) (bank (aux .frameBuffer)))
  have hin:Link.DataRel (frameStack part) bank before.store bank:=by
    constructor
    · intro i;fin_cases i
      · rfl
      · rfl
      · exact hs
    · intro k _;rfl
  apply included_call program (frameStack part) (Label.framer part) (frame_injective part) SemiprimeD1StackFrame.code
    0 (fun _=>rfl) pc next hc (6*(bank (frameStack part 0)).length+4) before after _ _ rfl rfl
    (SemiprimeD1StackFrame.frame_words _ _ none) hin
  have h:=Link.data_update (frameStack part) (frame_injective part) bank before.store bank hin 1
    (SemiprimeSourceHistogramKeyBits.frame (bank (frameStack part 0)) (bank (aux .frameBuffer)))
  have he:Function.update before.store 1
      (SemiprimeSourceHistogramKeyBits.frame (bank (frameStack part 0)) (bank (aux .frameBuffer)))=after.store:=by
    funext i;fin_cases i <;> rfl
  simpa only [he,show frameStack part 1=aux .frameBuffer from rfl] using h
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Primitives
