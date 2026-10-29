/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesView
/-! # Actual compact-key normalization and occurrence-pair emission
The real reversed-bit trim and both preserving binary-key Frames execute on
this same source. One actual occurrence marker is pushed for each logged pair.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrencesOperations
open SemiprimeD1StackSourceOccurrences SemiprimeD1StackSourceOccurrencesPrimitives
open SemiprimeD1StackSourceOccurrencesView SemiprimeD1StackSourceOccurrencesEncoding
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1StackNetworkOwnerIndexEncoding (pairBytes)
local notation "ctl" => Label.local
/-- Exact real reverse/trim on the actual parsed/copied binary word; no native normalizer executes. -/
theorem normalize_run (part:Trim) (before:Stack→List Bool) (word:List Bool)
    (hw:before .word=word) (hs:before .normScratch=[])
    (hl:before .fieldScratch=[]) (hr:before .copyScratch=[])
    (ho:before (trimStack part .output)=[]) :
    ∃q≤4*word.length+6,Runs program q (ctl (.normalizeReverse part)) before (afterTrim part)
      (Function.update (Function.update before .word []) (trimStack part .output) (normal word)) :=by
  let b1:=Function.update (Function.update before .word []) .normScratch word.reverse
  have h0:=reverse_call .normalize (.normalizeReverse part) (.normalize part) rfl before word [] hw hs
  simp only [List.append_nil] at h0
  have h1:=trim_call part b1
    (by simpa [b1,trimStack,Function.update] using hl)
    (by simpa [b1,trimStack,Function.update] using hr)
  have he:Function.update (Function.update b1 .normScratch []) (trimStack part .output)
      (SemiprimeD1StackReduceExecution.trimReverse (b1 .normScratch)++b1 (trimStack part .output))=
      Function.update (Function.update before .word []) (trimStack part .output) (normal word):=by
    cases part <;> simp only [trimStack] at ho
    all_goals
      funext k
      cases k <;> simp [b1,trimStack,Function.update,normal,hs,ho]
  rw [he] at h1
  have h:=join h0 h1
  refine ⟨(2*word.length+3)+(SemiprimeD1StackReduceExecution.trimTime (b1 .normScratch)+1),?_,h⟩
  have ht:=SemiprimeD1StackReduceExecution.trimTime_le word.reverse
  simp only [List.length_reverse] at ht
  have hb:b1 .normScratch=word.reverse:=Function.update_self _ _ _
  rw [hb]
  omega
/-- Exact physical pair history result; factor key and every unrelated cache word are retained. -/
def emitAfter (before:Stack→List Bool) (owner factor hist:List Bool) :Stack→List Bool :=
  Function.update (Function.update (Function.update before .ownerKey []) .frameBuffer []) .history
    ((pairBytes (owner,factor)).reverse++hist)
/-- Two real binary-key Frames, tag/reversal, owner cleanup and a real M-marker push emit one exact original pair. -/
theorem emit_pair (before:Stack→List Bool) (owner factor hist occurrences:List Bool)
    (hk:before .ownerKey=owner) (hf:before .factorKey=factor) (hh:before .history=hist)
    (hb:before .frameBuffer=[]) (hs:before .frameScratch=[]) (hm:before .occurrences=occurrences) :
    Runs program (10*factor.length+11*owner.length+22) (ctl .frameFactor) before (ctl .ownerTag)
      (Function.update (emitAfter before owner factor hist) .occurrences (true::occurrences)) :=by
  let b1:=Function.update before .frameBuffer (frame factor [])
  let b2:=Function.update b1 .frameBuffer (frame owner (frame factor []))
  let b3:=Function.update b2 .frameBuffer (pairBytes (owner,factor))
  let b4:=Function.update (Function.update b3 .frameBuffer []) .history ((pairBytes (owner,factor)).reverse++hist)
  let b5:=Function.update b4 .ownerKey []
  have h0:=frame_call .factor .frameFactor .frameOwner rfl before factor [] hf hb hs
  have h1:=frame_call .owner .frameOwner .pairTag rfl b1 owner (frame factor [])
    (by simpa [b1,frameStack,Function.update] using hk) (by simp [b1]) (by simpa [b1,Function.update] using hs)
  have h2:=push_run .pairTag (ctl .pairReverse) .frameBuffer true b2 rfl
  have he2:Function.update b2 .frameBuffer (true::b2 .frameBuffer)=b3:=by
    simp only [b2,b3,b1,Function.update_self,Function.update_idem,pairBytes]
  rw [he2] at h2
  have h3:=reverse_call .pair .pairReverse .clearOwner rfl b3 (pairBytes (owner,factor)) hist
    (by simp [b3,reverseStack]) (by simpa [b3,b2,b1,reverseStack,Function.update] using hh)
  have h4:=drain_loop .clearOwner (ctl .countOccurrence) .ownerKey rfl b4 owner
    (by simpa [b4,b3,b2,b1,Function.update] using hk)
  have h5:=push_run .countOccurrence (ctl .ownerTag) .occurrences true b5 rfl
  have he5:b5 .occurrences=occurrences:=by simpa [b5,b4,b3,b2,b1,Function.update] using hm
  rw [he5] at h5
  have h:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  have he:b5=emitAfter before owner factor hist:=by
    funext k;cases k <;> simp [b5,b4,b3,b2,b1,emitAfter,Function.update]
  rw [he] at h
  have hlen:=SemiprimeD1StackNetworkOwnerIndexEncoding.pairBytes_length owner factor
  convert h using 1; omega
end RiemannGaussian.SemiprimeD1StackSourceOccurrencesOperations
