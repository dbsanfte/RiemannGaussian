/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputFirst
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputFinish
/-! # Actual verdict and side branches of marked coefficient acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputBody
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackMarkedPublicInputFirst SemiprimeD1StackMarkedPublicInputFinish
open SemiprimeD1StackMarkedPublicInputMetadata SemiprimeD1StackMarkedPublicInputPrimitives
open SemiprimeD1StackProcedureTrace
/-- Actual first-side suffix bytes awaiting physical cleanup. -/
def suffix (bits raw : List Bool) : List Bool :=
  raw.drop (SemiprimeD1StackPublicInputMeaning.cached bits).length
/-- Own sum of the actual three branch caps; no native-table cost is used. -/
def bodyBound (bits raw indexWord : List Bool) : Nat :=
  firstBound bits raw indexWord+
  finishTime (acquired bits raw indexWord) [] [] [] []+
  finishTime (acquired bits raw indexWord) [] [] [] [true]+
  finishTime (acquired bits raw indexWord) (suffix bits raw)
    (SemiprimeD1StackPublicInputMeaning.word bits raw) (radixWord bits raw indexWord)
    (marked (shiftCount bits raw indexWord) (SemiprimeD1StackPublicInputMeaning.word bits raw))+5
/-- Every branch inspects only actual singleton cells and then executes the
same actual width fit, retaining all52 checker fields and the descriptor side. -/
theorem body_run (bits raw indexWord : List Bool) (side : Bool) (hb : bits≠[]) :
    ∃ t ≤ bodyBound bits raw indexWord,
      Runs program t (ctl .checked) (data (acquired bits raw indexWord) {side := [side]})
        (ctl .done) (result bits raw indexWord side) := by
  let p := acquired bits raw indexWord
  have h0 := peek_run .checked (ctl .bad) (ctl .zero) (ctl .side)
    (checker P.output) (data p {side := [side]})
    [SemiprimeD1StackPublicInputMeaning.expected bits raw indexWord] rfl rfl
  cases ha : SemiprimeD1StackPublicInputMeaning.expected bits raw indexWord with
  | false =>
    have h1 : Runs program 1 (ctl .zero) (data p {side := [side]})
        (ctl .widthA) (data p {side := [side]}) :=
      one_base program _ _ _ _ _ rfl rfl rfl
    have h2 := finish_run p [] [] [] [side] []
    have h00 : Runs program 1 (ctl .checked) (data p {side := [side]})
        (ctl .zero) (data p {side := [side]}) := by
      simpa only [ha,SemiprimeD1StackBytecode.choose,List.head?_cons] using h0
    have hh := join (join h00 h1) h2
    refine ⟨_,?_,by simpa only [p,ellAt,template,ellWord,shiftCount,result,coefficient,operand,ha,Bool.false_eq_true,ite_false] using hh⟩
    dsimp only [bodyBound,p,shiftCount,ellWord]
    omega
  | true =>
    have h00 : Runs program 1 (ctl .checked) (data p {side := [side]})
        (ctl .side) (data p {side := [side]}) := by
      simpa only [ha,SemiprimeD1StackBytecode.choose,List.head?_cons] using h0
    have hs := peek_run .side (ctl .bad) (ctl .raw) (ctl .one) (aux .side)
      (data p {side := [side]}) [side] rfl rfl
    cases side with
    | false =>
      have h01 : Runs program 1 (ctl .side) (data p {side := [false]})
          (ctl .raw) (data p {side := [false]}) := hs
      obtain ⟨t,ht,h1⟩ := first_run bits raw indexWord hb
      have h2 := finish_run p (suffix bits raw) (SemiprimeD1StackPublicInputMeaning.word bits raw)
        (radixWord bits raw indexWord) [false]
        (marked (shiftCount bits raw indexWord) (SemiprimeD1StackPublicInputMeaning.word bits raw))
      have hh := join (join (join h00 h01) h1) h2
      refine ⟨_,?_,by simpa only [p,ellAt,template,ellWord,shiftCount,result,coefficient,operand,ha,ite_true,Bool.false_eq_true,ite_false] using hh⟩
      dsimp only [bodyBound,p,shiftCount,ellWord]
      omega
    | true =>
      have h01 : Runs program 1 (ctl .side) (data p {side := [true]})
          (ctl .one) (data p {side := [true]}) := hs
      have h1 := push_run .one (ctl .widthA) (aux .shifted) true (data p {side := [true]}) rfl
      rw [data_shifted,update_shifted] at h1
      have h2 := finish_run p [] [] [] [true] [true]
      have hh := join (join (join h00 h01) h1) h2
      refine ⟨_,?_,by simpa only [p,ellAt,template,ellWord,shiftCount,result,coefficient,operand,ha,ite_true] using hh⟩
      dsimp only [bodyBound,p,shiftCount,ellWord]
      omega
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputBody

