/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreComponents
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreEmit
open SemiprimeD1StackOwnerFibre SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame frame_length)
/-- Exact real preserving Frame call on this actual parsed scope-ID. -/
theorem frame_call (query reader value raw:List Bool) :
    Runs program (6*value.length+5) .frame (data query reader [] [] [] [] value raw [] [])
      .reverse (data query reader [] [] [] [] value raw (frame value []) []) := by
  apply included_call program frameStack Label.frameCode frame_injective SemiprimeD1StackFrame.code 0
    (fun _=>rfl) .frame .reverse rfl (6*value.length+4)
    (SemiprimeD1StackFrame.state 0 none value [] []) (SemiprimeD1StackFrame.done value (frame value []))
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words value [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> rfl
      · cases k <;> first | rfl | exact (hk 1 rfl).elim
/-- Exact physical frame reversal onto the existing ordered collector. -/
theorem row_reverse_call (query reader value raw:List Bool) :
    Runs program (2*(frame value []).length+3) .reverse
      (data query reader [] [] [] [] value raw (frame value []) []) .clear
      (data query reader [] [] [] [] value ((frame value []).reverse++raw) [] []) := by
  apply included_call program (reverseStack false) (Label.reverseCode false) (reverse_injective false)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) .reverse .clear rfl
    (2*(frame value []).length+2)
    (SemiprimeD1StackReverseWord.state none (frame value []) raw)
    (SemiprimeD1StackReverseWord.done ((frame value []).reverse++raw))
  · rfl
  · rfl
  · exact SemiprimeD1StackReverseWord.reverse_run _ _ none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · cases k <;> rfl
      · cases k <;> first | rfl | exact (hk 0 rfl).elim | exact (hk 1 rfl).elim
/-- Exact final whole-collector reversal, including the real output delimiter. -/
theorem final_reverse_call (query reader raw:List Bool) :
    Runs program (2*raw.length+3) .finishReverse (data query reader [] [] [] [] [] raw [] [])
      .done (data query reader [] [] [] [] [] [] [] raw.reverse) := by
  apply included_call program (reverseStack true) (Label.reverseCode true) (reverse_injective true)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) .finishReverse .done rfl
    (2*raw.length+2) (SemiprimeD1StackReverseWord.state none raw [])
    (SemiprimeD1StackReverseWord.done (raw.reverse++[]))
  · rfl
  · rfl
  · exact SemiprimeD1StackReverseWord.reverse_run _ _ none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> simp [reverseStack,data,SemiprimeD1StackReverseWord.done,SemiprimeD1StackReverseWord.payload]
    · intro k hk
      rcases k with k|k
      · cases k <;> rfl
      · cases k <;> first | rfl | exact (hk 0 rfl).elim | exact (hk 1 rfl).elim
/-- A selected row marker is physically pushed before the frame is reversed. -/
theorem tag_run (query reader value raw:List Bool) :
    Runs program 1 .emitTag (data query reader [] [] [] [] value raw [] [])
      .frame (data query reader [] [] [] [] value (true::raw) [] []) := by
  apply one_base program .emitTag .frame (.push (.inr .reversed) true .frame) _ _ rfl
  · rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
/-- Every emitted scope ID executes real tag/Frame/Reverse code exactly once. -/
theorem emit_run (query reader value raw:List Bool) :
    Runs program (10*value.length+11) .emitTag (data query reader [] [] [] [] value raw [] [])
      .clear (data query reader [] [] [] [] value ((true::frame value []).reverse++raw) [] []) := by
  have h:=runs_trans program _ _ _ _ _ _ _ _ (tag_run query reader value raw)
    (runs_trans program _ _ _ _ _ _ _ _ (frame_call query reader value (true::raw))
      (row_reverse_call query reader value (true::raw)))
  have ht:1+((6*value.length+5)+(2*(frame value []).length+3))=10*value.length+11 := by
    rw [frame_length]
    simp only [List.length_nil]
    omega
  rw [ht] at h
  simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using h
/-- The final false vector marker is physically pushed, not preloaded. -/
theorem final_tag_run (query reader raw:List Bool) :
    Runs program 1 .finishTag (data query reader [] [] [] [] [] raw [] [])
      .finishReverse (data query reader [] [] [] [] [] (false::raw) [] []) := by
  apply one_base program .finishTag .finishReverse (.push (.inr .reversed) false .finishReverse) _ _ rfl
  · rfl
  · funext k;rcases k with k|k <;> cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackOwnerFibreEmit
