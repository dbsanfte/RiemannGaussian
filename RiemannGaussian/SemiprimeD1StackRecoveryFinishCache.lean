/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishMoves
import RiemannGaussian.SemiprimeD1StackRecoveryFinishOperators
/-! # Four actual copy/reduce/cache stages of the fixed recovery source
Each stage physically copies WIDTH, executes the existing canonical reducer,
and physically transfers/drains its output. The finite kind below describes
fixed existing source labels in proofs; it is not a runtime procedure argument.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishCache
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackRecoveryFinishMoves
open SemiprimeD1StackRecoveryFinishProjection SemiprimeD1StackRecoveryFinishOperators SemiprimeD1StackProcedureTrace
local notation "ctl"=>Label.local
/-- Four fixed existing reduction/cache sites, independent of all source words. -/
inductive Kind where | quotient | odd | two | one deriving DecidableEq,Repr
/-- Existing literal WIDTH-copy control site. -/
def widthSite:Kind → Control | .quotient=>.qWidth | .odd=>.aWidth | .two=>.twoWidth | .one=>.oneWidth
/-- Existing literal reducer-call control site. -/
def reduceSite:Kind → Control | .quotient=>.qReduce | .odd=>.aReduce | .two=>.twoReduce | .one=>.oneReduce
/-- Existing literal result-transfer control site. -/
def saveSite:Kind → Control | .quotient=>.saveQ | .odd=>.saveA | .two=>.saveTwo | .one=>.saveOne
/-- Existing actual continuation after the physical result cache has been acquired. -/
def nextSite:Kind → Control | .quotient=>.oddInput | .odd=>.negativeWord | .two=>.one | .one=>.copyTodo
/-- Existing literal consuming transfer site. -/
def transfer:Kind→MoveSite | .quotient=>.residue | .odd=>.inverseInput | .two=>.two | .one=>.one
/-- Exact actual cached destination role. -/
def target (kind:Kind):Slot:=moveTo (transfer kind)
/-- Exact canonical bits produced by the real WIDTH-sized reduction. -/
def word (v:Values):List Bool:=(SemiprimeD1JetScalarBits.reduce (v .width).length (v .reduceInput)).bits
/-- Exact actual reducer invocation clock after WIDTH was physically copied. -/
def reducerTime (v:Values):Nat:=
  SemiprimeD1StackReduceExecution.trimTime ((v .reduceInput).take (v .width).length).reverse+
    SemiprimeD1StackReduceExecution.prefixTime (v .reduceInput) (v .width)+1
/-- Complete actual copy/reduce/move stage clock, including every real call and return. -/
def time (v:Values):Nat:=(5*(v .width).length+4)+reducerTime v+(6*(word v).length+7)
/-- Exact clean cache boundary after consuming the actual reducer input. -/
def cached (v:Values) (kind:Kind):Values:=
  Function.update (Function.update v .reduceInput []) (target kind) (word v)
/-- The SAME literal source executes each whole existing reduction/cache stage. -/
theorem cache_run (kind:Kind) (v:Values) (hs:v (.aux .copyScratch)=[])
    (hw:v .reduceWidth=[]) (ho:v .output=[]) (ht:v (target kind)=[]):
    Runs program (time v) (ctl (widthSite kind)) (data v) (ctl (nextSite kind)) (data (cached v kind)):=by
  let v1:=Function.update v .reduceWidth (v .width)
  let v2:=reduced v1 (word v)
  have hc0:program (ctl (widthSite kind))=.call (.copy .width 0) (ctl (reduceSite kind)):=by cases kind <;> rfl
  have h0:=copy_view .width (ctl (widthSite kind)) (ctl (reduceSite kind)) v hc0 hs
  simp only [copyFrom,copyTo,hw,List.append_nil] at h0
  change Runs program (5*(v .width).length+4) _ _ _ (data v1) at h0
  have hc1:program (ctl (reduceSite kind))=.call (.reduce .take) (ctl (saveSite kind)):=by cases kind <;> rfl
  have ho1:v1 .output=[]:=by simp [v1,ho]
  have h1:=reduce_call (ctl (reduceSite kind)) (ctl (saveSite kind)) v1 hc1 ho1
  have hword:reduceWord v1=word v:=by simp [reduceWord,word,v1]
  have htime:reduceTime v1=reducerTime v:=by simp [reduceTime,reducerTime,v1]
  rw [hword,htime] at h1
  change Runs program (reducerTime v) _ _ _ (data v2) at h1
  have hc2:program (ctl (saveSite kind))=.call (.move (transfer kind) false) (ctl (nextSite kind)):=by cases kind <;> rfl
  have hs2:v2 (.aux .copyScratch)=[]:=by simp [v2,reduced,v1,hs]
  have h2:=move_call (transfer kind) (ctl (saveSite kind)) (ctl (nextSite kind)) v2 hc2 hs2
  have hf:moveFrom (transfer kind)=.output:=by cases kind <;> rfl
  have hov:v2 .output=word v:=by simp [v2,reduced]
  rw [hf,hov] at h2
  have he:moved v2 (transfer kind)=cached v kind:=by
    cases kind <;> dsimp only [target,transfer,moveTo] at ht <;> funext s <;> cases s with
    | aux a=>cases a <;> simp [moved,v2,reduced,v1,cached,target,transfer,moveFrom,moveTo,ht]
    | _=>simp [moved,v2,reduced,v1,cached,target,transfer,moveFrom,moveTo,hw,ho]
  rw [he] at h2
  exact join (join h0 h1) h2
end RiemannGaussian.SemiprimeD1StackRecoveryFinishCache
