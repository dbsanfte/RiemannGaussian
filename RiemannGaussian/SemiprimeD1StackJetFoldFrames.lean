/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldPrimitives
/-! # Actual input-head saves and restores for both real right-fold procedures -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldFrames
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldState SemiprimeD1StackJetFoldPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Literal current input reader for either actual fold procedure. -/
def readerSlot (child:Bool):Slot:=if child then .group else .modes
/-- Literal current parsed head for either actual fold procedure. -/
def headSlot (child:Bool):Slot:=if child then .left else .group
/-- Literal procedure entry used by each actual input-tag pop. -/
def visitControl (child:Bool):Control:=if child then .productVisit else .sumVisit
/-- Literal zero/one constructor branch for the empty vector. -/
def emptyControl (child:Bool):Control:=if child then .unit else .zeroLeft
/-- Literal input-field parse location. -/
def readControl (child:Bool):Control:=if child then .productRead else .sumRead
/-- Literal input-field validation location. -/
def validControl (child:Bool):Control:=if child then .productValid else .sumValid
/-- Literal head-frame save location. -/
def saveControl (child:Bool):Control:=if child then .productSave else .sumSave
/-- Literal head-word drain location before actual recursive descent. -/
def clearControl (child:Bool):Control:=if child then .productClear else .sumClear
/-- Literal real recursive-call location. -/
def childControl (child:Bool):Control:=if child then .productChild else .sumChild
/-- Literal field-parser site selected by the current procedure. -/
def readSite (child:Bool):Parse:=if child then .child else .mode
/-- Literal saved-field parser site selected by the current procedure. -/
def restoreSite (child:Bool):Parse:=if child then .restoreChild else .restoreMode
/-- Literal saved-head restore location reached by the actual return. -/
def restoreControl (child:Bool):Control:=if child then .productRestore else .sumRestore
/-- Literal restored-field validation location. -/
def restoredControl (child:Bool):Control:=if child then .productRestored else .sumRestored
/-- Literal continuation after physically restoring and validating the actual head. -/
def restoredNext (child:Bool):Control:=if child then .multiply else .copySum
/-- Exact word boundary after the actual head frame is saved and the head buffer drained. -/
def saved (v:Values) (child:Bool) (word tail:List Bool):Values:=
  Function.update (Function.update (Function.update (Function.update v (readerSlot child) tail)
    (headSlot child) []) .valid []) .frames (frame word (v .frames))
/-- Every actual tag, field bit, validity marker, saved-frame bit and drained head bit is counted. -/
theorem enter (child:Bool) (v:Values) (word tail:List Bool)
    (hi:v (readerSlot child)=true::frame word tail) (ho:v (headSlot child)=[]) (hv:v .valid=[]):
    Runs program (15*word.length+15) (ctl (visitControl child)) (data v)
      (ctl (childControl child)) (data (saved v child word tail)):=by
  let a:=Function.update v (readerSlot child) (frame word tail)
  let b:=Function.update (Function.update (Function.update a (readerSlot child) tail) (headSlot child) word) .valid [true]
  let c:=Function.update b .valid []
  let d:=Function.update c .frames (frame word (v .frames))
  have h0:=pop_view (visitControl child) .abort (emptyControl child) (readControl child)
    (readerSlot child) v (true::frame word tail) (by cases child <;> rfl) hi
  change Runs program 1 _ _ (ctl (readControl child)) (data a) at h0
  have hread:readFrom (readSite child)=readerSlot child:=by cases child <;> rfl
  have hhead:readTo (readSite child)=headSlot child:=by cases child <;> rfl
  have hai:a (readFrom (readSite child))=frame word tail:=by rw [hread];exact Function.update_self _ _ _
  have hao:a (readTo (readSite child))=[]:=by cases child <;> exact ho
  have hav:a .valid=[]:=by cases child <;> exact hv
  have h1:=field_view (readSite child) (readControl child) (validControl child) a word tail
    (by cases child <;> rfl) hai hao hav
  rw [hread,hhead] at h1
  change Runs program (8*word.length+7) _ _ _ (data b) at h1
  have h2:=pop_view (validControl child) .abort .abort (saveControl child) .valid b [true]
    (by cases child <;> rfl) (Function.update_self _ _ _)
  change Runs program 1 _ _ (ctl (saveControl child)) (data c) at h2
  have h3:=save_view child (saveControl child) (clearControl child) c (by cases child <;> rfl)
  have hs:c (savedFrom child)=word:=by cases child <;> rfl
  have hf:c .frames=v .frames:=by cases child <;> rfl
  rw [hs,hf] at h3
  change Runs program (6*word.length+5) _ _ _ (data d) at h3
  have h4:=drain_view (clearControl child) (childControl child) (headSlot child) d (by cases child <;> rfl)
  have hd:d (headSlot child)=word:=by cases child <;> rfl
  rw [hd] at h4
  have he:Function.update d (headSlot child) []=saved v child word tail:=by
    funext s;cases s <;> cases child <;> rfl
  rw [he] at h4
  have h:=join h0 (join h1 (join h2 (join h3 h4)))
  convert h using 1;omega
/-- Exact boundary after restoring one physical saved head and consuming its true validity marker. -/
def restored (v:Values) (child:Bool) (word tail:List Bool):Values:=
  Function.update (Function.update (Function.update v .frames tail) (headSlot child) word) .valid []
/-- Every saved head is restored by the real parser, with every original payload bit preserved. -/
theorem restore (child:Bool) (v:Values) (word tail:List Bool)
    (hi:v .frames=frame word tail) (ho:v (headSlot child)=[]) (hv:v .valid=[]):
    Runs program (8*word.length+8) (ctl (restoreControl child)) (data v)
      (ctl (restoredNext child)) (data (restored v child word tail)):=by
  let b:=Function.update (Function.update (Function.update v .frames tail) (headSlot child) word) .valid [true]
  have hread:readFrom (restoreSite child)=.frames:=by cases child <;> rfl
  have hhead:readTo (restoreSite child)=headSlot child:=by cases child <;> rfl
  have h1:=field_view (restoreSite child) (restoreControl child) (restoredControl child) v word tail
    (by cases child <;> rfl) (by rw [hread];exact hi) (by rw [hhead];exact ho) hv
  rw [hread,hhead] at h1
  change Runs program (8*word.length+7) _ _ _ (data b) at h1
  have h2:=pop_view (restoredControl child) .abort .abort (restoredNext child) .valid b [true]
    (by cases child <;> rfl) (Function.update_self _ _ _)
  change Runs program 1 _ _ (ctl (restoredNext child)) (data (restored v child word tail)) at h2
  have h:=join h1 h2
  exact h
end RiemannGaussian.SemiprimeD1StackJetFoldFrames
