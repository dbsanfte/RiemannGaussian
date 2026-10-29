/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceEnvironmentCounter
/-! # Actual chosen-ID extension of the retained prefix dictionary
Every payload copy, canonicalization, marker/key Frame, compact successor and
cleanup is executed by the same finite program. No chosen index/key/count is
supplied to the source beyond its actual retained words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceEnvironmentExtend
open SemiprimeD1StackSourceEnvironment SemiprimeD1StackSourceEnvironmentPrimitives
open SemiprimeD1StackSourceEnvironmentEncoding SemiprimeD1StackSourceEnvironmentCounter
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Exactly the physical temporary words required clear before an extension. -/
def ExtendClear (before:Stack→List Bool) :Prop :=
  ∀k∈[Aux.markedValue,.copyWork,.copyScratch,.trimScratch,.frameScratch,.incNext,.incScratch],before (aux k)=[]
/-- One actual extension retains all caller words except its dictionary and actual next-key counter. -/
theorem extend_trace (before:Stack→List Bool) (dict word chosen:List Bool)
    (hd:before (aux .dictionary)=dict) (hw:before (aux .nextKey)=word)
    (hc:before (aux .chosenID)=chosen) (hs:ExtendClear before) :
    ∃q≤100*(chosen.length+word.length+1),Runs program q (ctl .extend) before (ctl .resume)
      (Function.update (Function.update before (aux .dictionary)
        (true::frame word (frame (marked chosen) dict))) (aux .nextKey) (successor word)) :=by
  have hm:=hs .markedValue (by simp)
  have hcopy:=hs .copyWork (by simp)
  have hcs:=hs .copyScratch (by simp)
  have ht:=hs .trimScratch (by simp)
  have hf:=hs .frameScratch (by simp)
  have hn:=hs .incNext (by simp)
  have hi:=hs .incScratch (by simp)
  let b1:=Function.update before (aux .copyWork) chosen
  let b2:=Function.update before (aux .trimScratch) chosen.reverse
  let b3:=Function.update before (aux .markedValue) (normalize chosen)
  let b4:=Function.update before (aux .markedValue) (marked chosen)
  let b5:=Function.update b4 (aux .dictionary) (frame (marked chosen) dict)
  let b6:=Function.update b4 (aux .dictionary) (frame word (frame (marked chosen) dict))
  let b7:=Function.update b4 (aux .dictionary) (true::frame word (frame (marked chosen) dict))
  have h1:=copy_call .chosen .extend .reverseChosen rfl before chosen [] hc hcopy hcs
  simp only [List.append_nil] at h1
  change Runs program _ _ _ _ b1 at h1
  have h2:=reverse_call .chosen .reverseChosen .trimChosen rfl b1 chosen [] rfl
    (by simpa [b1,reverseStack,aux,Function.update] using ht)
  simp only [List.append_nil] at h2
  have he2:Function.update (Function.update b1 (reverseStack .chosen 0) []) (reverseStack .chosen 1) chosen.reverse=b2:=by
    funext k
    rcases k with k|k
    · rfl
    · cases k <;> simp [b1,b2,reverseStack,aux,Function.update]
      all_goals exact hcopy
  rw [he2] at h2
  have h3:=trim_call .chosen .trimChosen .tagMarked rfl b2 chosen.reverse []
    (by simpa [b2,trimStack,aux,Function.update] using hcopy)
    (by simpa [b2,trimStack,aux,Function.update] using hf) rfl
    (by simpa [b2,trimStack,aux,Function.update] using hm)
  simp only [List.append_nil] at h3
  have he3:Function.update (Function.update b2 (trimStack .chosen .scratch) []) (trimStack .chosen .output)
      (SemiprimeD1StackReduceExecution.trimReverse chosen.reverse)=b3:=by
    funext k
    rcases k with k|k
    · rfl
    · cases k <;> simp [b2,b3,trimStack,aux,Function.update,SemiprimeD1StackSourceEnvironmentEncoding.normalize]
      all_goals exact ht
  rw [he3] at h3
  have h4:=push_run .tagMarked (ctl .frameValue) (aux .markedValue) true b3 rfl
  change Runs program 1 _ _ _ (Function.update b3 (aux .markedValue) (marked chosen)) at h4
  simp only [b3,Function.update_idem] at h4
  change Runs program 1 _ _ _ b4 at h4
  have h5:=frame_call .value .frameValue .frameKey rfl b4 (marked chosen) dict rfl
    (by simpa [b4,frameStack,aux,Function.update] using hd)
    (by simpa [b4,frameStack,aux,Function.update] using hf)
  change Runs program _ _ _ _ b5 at h5
  have h6:=frame_call .key .frameKey .rowTag rfl b5 word (frame (marked chosen) dict)
    (by simpa [b5,b4,frameStack,aux,Function.update] using hw) rfl
    (by simpa [b5,b4,frameStack,aux,Function.update] using hf)
  change Runs program _ _ _ _ (Function.update b5 (aux .dictionary) (frame word (frame (marked chosen) dict))) at h6
  simp only [b5,Function.update_idem] at h6
  change Runs program _ _ _ _ b6 at h6
  have h7:=push_run .rowTag (ctl .increment) (aux .dictionary) true b6 rfl
  change Runs program 1 _ _ _ (Function.update b6 (aux .dictionary) (true::frame word (frame (marked chosen) dict))) at h7
  simp only [b6,Function.update_idem] at h7
  change Runs program 1 _ _ _ b7 at h7
  obtain ⟨q,hq,h8⟩:=counter_run b7 word
    (by simpa [b7,b4,aux,Function.update] using hw)
    (by simpa [b7,b4,aux,Function.update] using hn)
    (by simpa [b7,b4,aux,Function.update] using hi)
    (by simpa [b7,b4,aux,Function.update] using ht)
    (by simpa [b7,b4,aux,Function.update] using hcopy)
    (by simpa [b7,b4,aux,Function.update] using hf)
  have h9:=drain_loop .clearMarked (ctl .resume) (aux .markedValue) rfl
    (Function.update b7 (aux .nextKey) (successor word)) (marked chosen)
    (by simp [b7,b4,aux,Function.update])
  have he9:Function.update (Function.update b7 (aux .nextKey) (successor word)) (aux .markedValue) []=
      Function.update (Function.update before (aux .dictionary) (true::frame word (frame (marked chosen) dict)))
        (aux .nextKey) (successor word):=by
    funext k
    rcases k with k|k
    · rfl
    · cases k <;> simp [b7,b4,aux,Function.update]
      all_goals exact hm
  rw [he9] at h9
  have h:=join (join (join (join (join (join (join (join h1 h2) h3) h4) h5) h6) h7) h8) h9
  refine ⟨_,?_,h⟩
  have htrim:=SemiprimeD1StackReduceExecution.trimTime_le chosen.reverse
  have hnorm:=normalize_length chosen
  simp only [List.length_reverse] at htrim
  simp only [marked,List.length_cons] at *
  omega
end RiemannGaussian.SemiprimeD1StackSourceEnvironmentExtend
