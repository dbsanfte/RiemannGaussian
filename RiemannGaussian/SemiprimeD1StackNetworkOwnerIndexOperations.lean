/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexPrimitives
import RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexEncoding
/-! # Actual complete pair emission and binary owner-counter transfer
These are traces of the SAME literal17-role source. Every frame, tag, reversal,
key cleanup and carry pop is physically executed; invariants are not operands.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexOperations
open SemiprimeD1StackNetworkOwnerIndex SemiprimeD1StackNetworkOwnerIndexPrimitives
open SemiprimeD1StackNetworkOwnerIndexEncoding SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Exact real pair-emission result; the original owner and ALLother physical fields are retained. -/
def emitAfter (before:Stack→List Bool) (key owner hist:List Bool) :Stack→List Bool :=
  Function.update (Function.update (Function.update before .key []) .frameBuffer []) .history
    ((pairBytes (key,owner)).reverse++hist)
/-- Two real Frames, one true tag, a real reverse and a physical key drain emit the exact pair bytes. -/
theorem emit_pair (before:Stack→List Bool) (key owner hist:List Bool)
    (hk:before .key=key) (ho:before .owner=owner) (hh:before .history=hist)
    (hb:before .frameBuffer=[]) (hs:before .frameScratch=[]) :
    Runs program (10*owner.length+11*key.length+21) (ctl .valueFrame) before (ctl .portLoop)
      (emitAfter before key owner hist) :=by
  let b1:=Function.update before .frameBuffer (frame owner [])
  let b2:=Function.update b1 .frameBuffer (frame key (frame owner []))
  let b3:=Function.update b2 .frameBuffer (pairBytes (key,owner))
  let b4:=Function.update (Function.update b3 .frameBuffer []) .history ((pairBytes (key,owner)).reverse++hist)
  have h0:=frame_call .value .valueFrame .keyFrame rfl before owner [] ho hb hs
  have h1:=frame_call .key .keyFrame .pairTag rfl b1 key (frame owner [])
    (by simpa [b1,frameStack,Function.update] using hk) (by simp [b1]) (by simpa [b1,Function.update] using hs)
  have h2:=push_run .pairTag (ctl .reversePair) .frameBuffer true b2 rfl
  have he2:Function.update b2 .frameBuffer (true::b2 .frameBuffer)=b3:=by
    simp only [b2,b3,b1,Function.update_self,Function.update_idem,pairBytes]
  rw [he2] at h2
  have h3:=reverse_call .pair .reversePair .clearKey rfl b3 (pairBytes (key,owner)) hist
    (by simp [b3,reverseStack]) (by simpa [b3,b2,b1,reverseStack,Function.update] using hh)
  have h4:=drain_loop .clearKey (ctl .portLoop) .key rfl b4 key
    (by simpa [b4,b3,b2,b1,Function.update] using hk)
  have hh0:=join (join (join (join h0 h1) h2) h3) h4
  have he:Function.update b4 .key []=emitAfter before key owner hist:=by
    funext k
    cases k <;> simp [b4,b3,b2,b1,emitAfter,Function.update]
  rw [he] at hh0
  have hlen:=pairBytes_length key owner
  have ht:(6*owner.length+5)+(6*key.length+5)+1+(2*(pairBytes (key,owner)).length+3)+(key.length+1)=
      10*owner.length+11*key.length+21:=by omega
  rw [ht] at hh0
  exact hh0
/-- Actual Increment call, false-carry pop and TWO real reversals transfer the owner without changing bit order. -/
theorem increment_transfer (before:Stack→List Bool) (n v:Nat) (hv:v<n)
    (ho:before .owner=ownerWord n v) (hn:before .ownerNext=[]) (hs:before .incrementScratch=[]) :
    ∃q≤ 14*(n+1)+23,Runs program q (ctl .increment) before (ctl .owners)
      (Function.update before .owner (ownerWord n (v+1))) :=by
  let word:=ownerWord n v
  let next:=SemiprimeD1StackIncrement.wrapped word
  let b1:=Function.update (Function.update before .owner []) .ownerNext (false::next)
  let b2:=Function.update b1 .ownerNext next
  let b3:=Function.update (Function.update b2 .ownerNext []) .incrementScratch next.reverse
  let b4:=Function.update (Function.update b3 .incrementScratch []) .owner next
  obtain ⟨b,hb,h0⟩:=increment_call before word ho hs hn
  rw [ownerWord_no_overflow n v (by omega)] at h0
  have h1:=pop_run .carry (ctl .abort) (ctl .ownerFirst) (ctl .abort) .ownerNext b1 (false::next) rfl (by simp [b1])
  have h2:=reverse_call .ownerFirst .ownerFirst .ownerSecond rfl b2 next []
    (by simp [b2,reverseStack]) (by simpa [b2,b1,reverseStack,Function.update] using hs)
  simp only [List.append_nil] at h2
  have h3:=reverse_call .ownerSecond .ownerSecond .owners rfl b3 next.reverse []
    (by simp [b3,reverseStack]) (by simp [b3,b2,b1,reverseStack,Function.update])
  simp only [List.reverse_reverse,List.append_nil] at h3
  have hh0:=join (join (join h0 h1) h2) h3
  have hnext:next=ownerWord n (v+1):=ownerWord_succ n v hv
  have he:b4=Function.update before .owner (ownerWord n (v+1)):=by
    funext k
    cases k <;> simp [b4,b3,b2,b1,Function.update,hn,hs,hnext]
  change Runs program (b+1+(2*next.length+3)+(2*next.reverse.length+3)) (ctl .increment) before (ctl .owners) b4 at hh0
  rw [he] at hh0
  refine ⟨b+1+(2*next.length+3)+(2*next.reverse.length+3),?_,hh0⟩
  rw [List.length_reverse]
  have hlen:next.length=n+1:=by rw [SemiprimeD1StackIncrement.wrapped_length,ownerWord_length n v (by omega)]
  have hword:word.length=n+1:=ownerWord_length n v (by omega)
  rw [hlen]
  rw [hword] at hb
  omega
end RiemannGaussian.SemiprimeD1StackNetworkOwnerIndexOperations
