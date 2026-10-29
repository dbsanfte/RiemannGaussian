/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPacketInventory
/-! # Real sparse-inventory copy, sentinel, frame, reversal and counter calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPacketInventoryPrimitives
open SemiprimeD1StackPacketInventory SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
local notation "ctl" => Label.local
/-- Exact chronological source-fragment composition preserves every real outer return. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after) :
    Runs program (m+n) pc before next after :=runs_trans program m n pc mid next before between after h g
/-- Actual complete preserving copy, including both restoration loops and its real caller return. -/
theorem copy_call (what:Copy) (pc next:Control)
    (hc:program (ctl pc)=.call (.copier what 0) (ctl next)) (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (copyStack what 0)=xs) (hy:before (copyStack what 1)=ys) (hs:before (copyStack what 2)=[]) :
    Runs program (5*xs.length+4) (ctl pc) before (ctl next)
      (Function.update before (copyStack what 1) (xs++ys)) :=by
  let start:=SemiprimeD1StackCopy.state 0 none xs ys []
  let stop:=SemiprimeD1StackCopy.done xs (xs++ys)
  have hi:Link.DataRel (copyStack what) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (copyStack what) (copy_injective what) before start.store before hi (1:Fin 3) (xs++ys)
  have he:Function.update start.store 1 (xs++ys)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (copyStack what) (Label.copier what) (copy_injective what) SemiprimeD1StackCopy.code 0
    (fun _=>rfl) (ctl pc) (ctl next) hc (5*xs.length+3) start stop before _ rfl rfl
    (SemiprimeD1StackCopy.copy_words xs ys none) hi ho
/-- Real preserving Frame writes a physical field onto its existing dictionary/vector tail. -/
theorem frame_call (right:Frame) (pc next:Control)
    (hc:program (ctl pc)=.call (.frame right 0) (ctl next)) (before:Stack→List Bool) (word buffer:List Bool)
    (hw:before (frameStack right 0)=word) (hb:before (frameStack right 1)=buffer) (hs:before (frameStack right 2)=[]) :
    Runs program (6*word.length+5) (ctl pc) before (ctl next)
      (Function.update before (frameStack right 1) (frame word buffer)) :=by
  let start:=SemiprimeD1StackFrame.state 0 none word buffer []
  let stop:=SemiprimeD1StackFrame.done word (frame word buffer)
  have hi:Link.DataRel (frameStack right) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hw
      · exact hb
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (frameStack right) (frame_injective right) before start.store before hi (1:Fin 3) (frame word buffer)
  have he:Function.update start.store 1 (frame word buffer)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact included_call program (frameStack right) (Label.frame right) (frame_injective right) SemiprimeD1StackFrame.code 0 (fun _=>rfl)
    (ctl pc) (ctl next) hc (6*word.length+4) start stop before _ rfl rfl
    (SemiprimeD1StackFrame.frame_words word buffer none) hi ho
/-- Every coordinate/key/slot reversal consumes its real source and pays all bytes and return cells. -/
theorem reverse_call (what:Reverse) (pc next:Control)
    (hc:program (ctl pc)=.call (.reverse what 0) (ctl next)) (before:Stack→List Bool) (xs ys:List Bool)
    (hx:before (reverseStack what 0)=xs) (hy:before (reverseStack what 1)=ys) :
    Runs program (2*xs.length+3) (ctl pc) before (ctl next)
      (Function.update (Function.update before (reverseStack what 0) []) (reverseStack what 1) (xs.reverse++ys)) :=by
  let start:=SemiprimeD1StackReverseWord.state none xs ys
  let stop:=SemiprimeD1StackReverseWord.done (xs.reverse++ys)
  have hi:Link.DataRel (reverseStack what) before start.store before:=by
    constructor
    · intro k;fin_cases k
      · exact hx
      · exact hy
    · intro k _;rfl
  have h0:=Link.data_update (reverseStack what) (reverse_injective what) before start.store before hi (0:Fin 2) []
  have h1:=Link.data_update (reverseStack what) (reverse_injective what) before _ _ h0 (1:Fin 2) (xs.reverse++ys)
  have he:Function.update (Function.update start.store 0 []) 1 (xs.reverse++ys)=stop.store:=by funext k;fin_cases k <;> rfl
  rw [he] at h1
  exact included_call program (reverseStack what) (Label.reverse what) (reverse_injective what)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) (ctl pc) (ctl next) hc (2*xs.length+2) start stop before _ rfl rfl
    (SemiprimeD1StackReverseWord.reverse_run xs ys none) hi h1
/-- One literal local push preserves the entire other physical bank and all real outer returns. -/
theorem push_run (pc:Control) (next:Label) (k:Stack) (b:Bool) (before:Stack→List Bool)
    (hc:program (ctl pc)=.base (.push k b next)) :
    Runs program 1 (ctl pc) before next (Function.update before k (b::before k)) :=
  one_base program _ _ _ _ _ hc rfl rfl
/-- One literal local pop consumes ONLYthe actual physical Boolean head. -/
theorem pop_run (pc:Control) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program (ctl pc)=.base (.pop k empty low high)) (hx:before k=xs) :
    Runs program 1 (ctl pc) before (SemiprimeD1StackBytecode.choose empty low high xs.head?) (Function.update before k xs.tail) :=by
  apply one_base program (ctl pc) _ (.pop k empty low high) before _ hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · simp only [SemiprimeD1StackBytecode.execute,hx]
/-- Real EOF peek does not silently discard any remaining singleton-result bytes. -/
theorem peek_run (pc:Control) (empty low high:Label) (k:Stack) (before:Stack→List Bool) (xs:List Bool)
    (hc:program (ctl pc)=.base (.peek k empty low high)) (hx:before k=xs) :
    Runs program 1 (ctl pc) before (SemiprimeD1StackBytecode.choose empty low high xs.head?) before :=by
  apply one_base program (ctl pc) _ (.peek k empty low high) before before hc
  · simp only [SemiprimeD1StackBytecode.execute,hx]
  · rfl
/-- Every colour/key/cursor cleanup actually visits every byte and its final empty branch. -/
theorem drain_loop (pc:Control) (next:Label) (k:Stack)
    (hc:program (ctl pc)=.base (.pop k next (ctl pc) (ctl pc))) (before:Stack→List Bool) (xs:List Bool) (hx:before k=xs) :
    Runs program (xs.length+1) (ctl pc) before next (Function.update before k []) :=by
  induction xs generalizing before with
  | nil=>exact pop_run pc next (ctl pc) (ctl pc) k before [] hc hx
  | cons b xs ih=>
    have h0:=pop_run pc next (ctl pc) (ctl pc) k before (b::xs) hc hx
    have h1:=ih (Function.update before k xs) (Function.update_self _ _ _)
    have hh:=join (by cases b <;> exact h0) h1
    simpa only [List.length_cons,Function.update_idem,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
/-- Real sentinel generation preserves the raw byte key and restores its separate scratch. -/
theorem sentinel_call (part:Sentinel) (pc next:Control)
    (hc:program (ctl pc)=.call (.sentinel part (.inl 0)) (ctl next)) (before:Stack→List Bool) (word:List Bool)
    (hw:before (sentinelStack part 0)=word) (hq:before query=[]) (hs:before scratch=[]) :
    Runs program (5*word.length+7) (ctl pc) before (ctl next) (Function.update before query (word++[true])) :=by
  let start:=SemiprimeD1StackOwnerEqualityKey.initial word
  let stop:=SemiprimeD1StackOwnerEqualityKey.done word
  have hi:Link.DataRel (sentinelStack part) before start.data before:=by
    constructor
    · intro k;fin_cases k
      · exact hw
      · exact hq
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (sentinelStack part) (sentinel_injective part) before start.data before hi (1:Fin 3) (word++[true])
  have he:Function.update start.data 1 (word++[true])=stop.data:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  exact SemiprimeD1StackProcedureCallsTrace.included_call program (sentinelStack part) (Label.sentinel part)
    (sentinel_injective part) K.program (.inl 0) (fun _=>rfl) (ctl pc) (ctl next) hc (5*word.length+6)
    start stop before _ rfl rfl rfl rfl (SemiprimeD1StackOwnerEqualityKey.source_run word) hi ho
/-- Real-ret binary increment consumes only the actual old word, preserves OLD-j and every other caller word, and pays its true caller return. -/
theorem counter_call (pc next:Control) (hc:program (ctl pc)=.call (.frequency .increment) (ctl next))
    (before:Stack→List Bool) (word:List Bool) (hw:before oldCount=word)
    (hn:before (frequencyStack (F.aux .incNext))=[]) (hi:before (frequencyStack (F.aux .incScratch))=[])
    (ht:before (frequencyStack (F.aux .trimScratch))=[]) (ho:before count=[])
    (hl:before (lookupStack (.inl .left))=[]) (hr:before (lookupStack (.inl .right))=[]) :
    ∃t ≤ 40*(word.length+1)+2,Runs program t (ctl pc) before (ctl next)
      (Function.update (Function.update before oldCount []) count
        (SemiprimeD1StackSourceEnvironmentEncoding.successor word)) :=by
  let localBank:F.Stack→List Bool:=fun k=>before (frequencyStack k)
  obtain ⟨t,htime,hsource⟩:=SemiprimeD1StackSourceKeyFrequencyCounterEntry.source_run localBank word hw hn hi ht ho hl hr
  let start:C.State F.Stack F.Label:=⟨some .increment,none,none,localBank,[]⟩
  let stop:C.State F.Stack F.Label:=⟨none,none,none,Function.update
    (Function.update localBank SemiprimeD1StackSourceKeyFrequency.oldCount []) (F.aux .count)
      (SemiprimeD1StackSourceEnvironmentEncoding.successor word),[]⟩
  have hin:Link.DataRel frequencyStack before localBank before:=⟨fun _=>rfl,fun _ _=>rfl⟩
  have h0:=Link.data_update frequencyStack frequency_injective before localBank before hin
    SemiprimeD1StackSourceKeyFrequency.oldCount []
  have h1:=Link.data_update frequencyStack frequency_injective before _ _ h0 (F.aux .count)
    (SemiprimeD1StackSourceEnvironmentEncoding.successor word)
  refine ⟨t+1,by omega,?_⟩
  exact SemiprimeD1StackProcedureCallsTrace.included_call program frequencyStack Label.frequency frequency_injective
    F.program .increment (fun _=>rfl) (ctl pc) (ctl next) hc t start stop before _ rfl rfl rfl rfl hsource hin h1
end RiemannGaussian.SemiprimeD1StackPacketInventoryPrimitives
