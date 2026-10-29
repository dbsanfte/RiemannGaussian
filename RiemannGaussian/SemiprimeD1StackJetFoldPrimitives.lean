/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldState
/-! # Paid literal copy/parser/frame/return traces for the same ordered fold -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldPrimitives
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldState SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Actual traces concatenate without introducing any extra source operation. -/
theorem join {m n:Nat} {pc mid next:Label} {before between after:Stack→List Bool}
    (h:Runs program m pc before mid between) (g:Runs program n mid between next after):
    Runs program (m+n) pc before next after:=runs_trans program m n pc mid next before between after h g
/-- Literal source slot for each real preserving-copy site. -/
def copyFrom:Copy→Slot | .children=>.children | .sum=>.sum | .product=>.result
/-- Literal target slot for each real preserving-copy site. -/
def copyTo:Copy→Slot | .children=>.modes | .sum=>.tailSum | .product=>.product
/-- Static source/target addresses stay separate at all three actual sites. -/
theorem copy_ne (site:Copy):address (copyFrom site)≠address (copyTo site):=by cases site <;> decide
/-- Restoring-copy work is separate from each physical destination. -/
theorem copy_work_ne (site:Copy):aux .copyScratch≠address (copyTo site):=by cases site <;> decide
/-- Every preserving copy includes its actual call and physical return. -/
theorem copy_view (site:Copy) (pc next:Control) (v:Values)
    (hc:program (ctl pc)=.call (.copy site 0) (ctl next)):
    Runs program (5*(v (copyFrom site)).length+4) (ctl pc) (data v) (ctl next)
      (data (Function.update v (copyTo site) (v (copyFrom site)++v (copyTo site)))):=by
  rw [data_update]
  apply included_call program (copyStack site) (Label.copy site) (copy_injective site)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) (ctl pc) (ctl next) hc (5*(v (copyFrom site)).length+3)
    (SemiprimeD1StackCopy.state 0 none (v (copyFrom site)) (v (copyTo site)) [])
    (SemiprimeD1StackCopy.done (v (copyFrom site)) (v (copyFrom site)++v (copyTo site))) _ _ rfl rfl
    (SemiprimeD1StackCopy.copy_words _ _ none)
  · constructor
    · intro k;fin_cases k
      · change data v (copyStack site 0)=v (copyFrom site)
        cases site with
        | children=>exact data_get v .children
        | sum=>exact data_get v .sum
        | product=>exact data_get v .result
      · change data v (copyStack site 1)=v (copyTo site)
        cases site with
        | children=>exact data_get v .modes
        | sum=>exact data_get v .tailSum
        | product=>exact data_get v .product
      · exact copy_scratch_empty v
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update (data v) (address (copyTo site)) _ (copyStack site 0)=v (copyFrom site)
        have he:copyStack site 0=address (copyFrom site):=by cases site <;> rfl
        rw [he,Function.update_of_ne (copy_ne site),data_get]
      · have he:copyStack site 1=address (copyTo site):=by cases site <;> rfl
        change Function.update (data v) (address (copyTo site)) _ (copyStack site 1)=_
        rw [he,Function.update_self]
        rfl
      · change Function.update (data v) (address (copyTo site)) _ (aux .copyScratch)=[]
        rw [Function.update_of_ne (copy_work_ne site),copy_scratch_empty]
    · intro k hk
      exact Function.update_of_ne (fun he=>hk 1 (by cases site <;> exact he.symm)) _ _
/-- Literal saved-head source slot; the target is the one real framed activation word. -/
def savedFrom (child:Bool):Slot:=if child then .left else .group
/-- Each real saved-head frame has separate source and destination. -/
theorem save_ne (child:Bool):address (savedFrom child)≠address .frames:=by cases child <;> decide
/-- Every head is physically framed before the tail call, including the real call/return cost. -/
theorem save_view (child:Bool) (pc next:Control) (v:Values)
    (hc:program (ctl pc)=.call (.save child 0) (ctl next)):
    Runs program (6*(v (savedFrom child)).length+5) (ctl pc) (data v) (ctl next)
      (data (Function.update v .frames (frame (v (savedFrom child)) (v .frames)))):=by
  rw [data_update]
  apply included_call program (saveStack child) (Label.save child) (save_injective child)
    SemiprimeD1StackFrame.code 0 (fun _=>rfl) (ctl pc) (ctl next) hc (6*(v (savedFrom child)).length+4)
    (SemiprimeD1StackFrame.state 0 none (v (savedFrom child)) (v .frames) [])
    (SemiprimeD1StackFrame.done (v (savedFrom child)) (frame (v (savedFrom child)) (v .frames))) _ _ rfl rfl
    (SemiprimeD1StackFrame.frame_words _ _ none)
  · constructor
    · intro k;fin_cases k
      · change data v (saveStack child 0)=v (savedFrom child)
        cases child with
        | false=>exact data_get v .group
        | true=>exact data_get v .left
      · exact data_get v .frames
      · exact frame_scratch_empty v
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update (data v) (address .frames) _ (saveStack child 0)=v (savedFrom child)
        have he:saveStack child 0=address (savedFrom child):=by cases child <;> rfl
        rw [he,Function.update_of_ne (save_ne child),data_get]
      · exact Function.update_self _ _ _
      · change Function.update (data v) (address .frames) _ (aux .frameScratch)=[]
        rw [Function.update_of_ne (by decide:aux .frameScratch≠address .frames),frame_scratch_empty]
    · intro k hk
      exact Function.update_of_ne (fun he=>hk 1 he.symm) _ _
/-- Literal reader slot for each real input/saved-head field parser. -/
def readFrom:Parse→Slot | .mode=>.modes | .child=>.group | .restoreMode|.restoreChild=>.frames
/-- Literal output slot for each actual parsed/restored head. -/
def readTo:Parse→Slot | .mode|.restoreMode=>.group | .child|.restoreChild=>.left
/-- Every parser executes the immutable field decoder and writes its true validity marker. -/
theorem field_view (site:Parse) (pc next:Control) (v:Values) (word tail:List Bool)
    (hc:program (ctl pc)=.call (.field site (F.active .tagPop (none,false))) (ctl next))
    (hi:v (readFrom site)=frame word tail) (ho:v (readTo site)=[]) (hv:v .valid=[]):
    Runs program (8*word.length+7) (ctl pc) (data v) (ctl next)
      (data (Function.update (Function.update (Function.update v (readFrom site) tail) (readTo site) word) .valid [true])):=by
  let before:=SemiprimeD1TensorTapeFieldBytecode.initial (frame word tail) []
  let after:SemiprimeD1StackBytecode.State F.Stack F.Label:=
    ⟨none,none,Sum.elim (SemiprimeD1TensorTapeFieldMachine.contents tail [] word) (fun _=>[true])⟩
  have hin:SemiprimeD1StackMultiplierLink.DataRel (fieldStack site) (data v) before.store (data v):=by
    constructor
    · intro k
      rcases k with k|k
      · cases k
        · have he:fieldStack site (.inl .input)=address (readFrom site):=by cases site <;> rfl
          change data v (fieldStack site (.inl .input))=frame word tail
          rw [he,data_get,hi]
        · exact field_scratch_empty v
        · have he:fieldStack site (.inl .output)=address (readTo site):=by cases site <;> rfl
          change data v (fieldStack site (.inl .output))=[]
          rw [he,data_get,ho]
      · cases k
        change data v (address .valid)=[]
        rw [data_get,hv]
    · intro k _;rfl
  apply included_call program (fieldStack site) (Label.field site) (field_injective site) F.code
    (F.active .tagPop (none,false)) (fun _=>rfl) (ctl pc) (ctl next) hc (8*word.length+6)
    before after _ _ rfl rfl (SemiprimeD1TensorTapeFieldBytecode.framed_run word tail []) hin
  have h0:=SemiprimeD1StackMultiplierLink.data_update (fieldStack site) (field_injective site) (data v) before.store (data v) hin (.inl .input) tail
  have h1:=SemiprimeD1StackMultiplierLink.data_update (fieldStack site) (field_injective site) (data v) _ _ h0 (.inl .output) word
  have h2:=SemiprimeD1StackMultiplierLink.data_update (fieldStack site) (field_injective site) (data v) _ _ h1 (.inr ()) [true]
  have he:Function.update (Function.update (Function.update before.store (.inl .input) tail) (.inl .output) word) (.inr ()) [true]=after.store:=by
    funext k;rcases k with k|k <;> cases k <;> rfl
  rw [he] at h2
  have hreader:fieldStack site (.inl .input)=address (readFrom site):=by cases site <;> rfl
  have hword:fieldStack site (.inl .output)=address (readTo site):=by cases site <;> rfl
  have hvalid:fieldStack site (.inr ())=address .valid:=rfl
  rw [hreader,hword,hvalid,←data_update,←data_update,←data_update] at h2
  exact h2
/-- One literal physical push, with the exact live-word update. -/
theorem push_view (pc next:Control) (s:Slot) (b:Bool) (v:Values)
    (hc:program (ctl pc)=.base (.push (address s) b (ctl next))):
    Runs program 1 (ctl pc) (data v) (ctl next) (data (Function.update v s (b::v s))):=by
  rw [data_update]
  exact one_base program _ _ _ _ _ hc rfl (by rw [←data_get v s];rfl)
/-- One literal physical pop; its branch depends only on the actual leading Boolean cell. -/
theorem pop_view (pc empty low high:Control) (s:Slot) (v:Values) (word:List Bool)
    (hc:program (ctl pc)=.base (.pop (address s) (ctl empty) (ctl low) (ctl high))) (hx:v s=word):
    Runs program 1 (ctl pc) (data v)
      (SemiprimeD1StackBytecode.choose (ctl empty) (ctl low) (ctl high) word.head?)
      (data (Function.update v s word.tail)):=by
  rw [data_update]
  apply one_base program _ _ _ _ _ hc
  · simp only [SemiprimeD1StackBytecode.execute,data_get,hx]
  · simp only [SemiprimeD1StackBytecode.execute,data_get,hx]
/-- Every actual cleanup bit and its final EOF are counted. -/
theorem drain_view (pc next:Control) (s:Slot) (v:Values)
    (hc:program (ctl pc)=.base (.pop (address s) (ctl next) (ctl pc) (ctl pc))):
    Runs program ((v s).length+1) (ctl pc) (data v) (ctl next) (data (Function.update v s [])):=by
  generalize hw:v s=word
  induction word generalizing v with
  | nil=>simpa only [hw,List.length_nil,Nat.zero_add,List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose]
      using pop_view pc next pc pc s v [] hc hw
  | cons b word ih=>
    have h0:=pop_view pc next pc pc s v (b::word) hc hw
    have h1:=ih (Function.update v s word) (Function.update_self _ _ _)
    have h:=join (by cases b <;> exact h0) h1
    simpa only [hw,Function.update_idem,List.length_cons,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
/-- Actual recursion pushes and later pops a real fixed-label return symbol, preserving all outer frames. -/
theorem recursive_call (pc entry next:Control) (before after:Stack→List Bool) (time:Nat)
    (hc:program (ctl pc)=.call (ctl entry) (ctl next))
    (hr:Runs program time (ctl entry) before (ctl .returning) after):
    Runs program (time+2) (ctl pc) before (ctl next) after:=by
  intro frames target h
  rcases h with ⟨hp,hd,hf⟩
  let mid:=SemiprimeD1StackCalls.execute (.call (ctl entry) (ctl next)) target
  have hm:SemiprimeD1StackCalls.run program 1 target=some mid:=by
    change SemiprimeD1StackCalls.step program target=some mid
    simp only [SemiprimeD1StackCalls.step,hp,Option.map_some,hc,mid]
  obtain ⟨finish,hRun,hAt⟩:=hr ((ctl next)::frames) mid (by
    simp only [At,mid,SemiprimeD1StackCalls.execute,hd,hf,and_self])
  let last:=SemiprimeD1StackCalls.execute .ret finish
  have hl:SemiprimeD1StackCalls.run program 1 finish=some last:=by
    change SemiprimeD1StackCalls.step program finish=some last
    simp only [SemiprimeD1StackCalls.step,hAt.1,Option.map_some,program,last]
  refine ⟨last,?_,?_,?_,?_⟩
  · rw [show time+2=1+(time+1) by omega,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hRun,Option.bind_some]
    exact hl
  · simp only [last,SemiprimeD1StackCalls.execute,hAt.2.2]
  · simpa only [last,SemiprimeD1StackCalls.execute,hAt.2.2] using hAt.2.1
  · simp only [last,SemiprimeD1StackCalls.execute,hAt.2.2]
end RiemannGaussian.SemiprimeD1StackJetFoldPrimitives
