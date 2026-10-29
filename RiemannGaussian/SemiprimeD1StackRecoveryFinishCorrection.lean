/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishMoves
import RiemannGaussian.SemiprimeD1StackRecoveryFinishOperators
/-! # Actual Newton correction-cache scalar sum
Both operands are physically copied, the real modular scalar adder is called,
the previous correction cache is drained, and the real output is moved/drained.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishCorrection
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackRecoveryFinishMoves
open SemiprimeD1StackRecoveryFinishProjection SemiprimeD1StackRecoveryFinishOperators SemiprimeD1StackProcedureTrace
local notation "ctl"=>Label.local
/-- Actual real scalar-adder operands/result are empty before their paid preparation. -/
structure Clean (v:Values):Prop where
  /-- Actual left operand is empty. -/
  left:v .addLeft=[]
  /-- Actual right operand is empty. -/
  right:v .addRight=[]
  /-- Actual output word is empty. -/
  output:v .addOutput=[]
/-- Exact real correction-cache word. -/
def word (v:Values):List Bool:=
  (SemiprimeD1JetScalarBits.add (v .width).length (v (.aux .two)) (v (.aux .opposite))).bits
/-- Actual whole-controller result clears all real adder work and replaces only the correction cache. -/
def result (v:Values):Values:=Function.update v (.aux .correction) (word v)
/-- Actual two preserving copies, real scalar adder, cache drain and output move, with all real returns. -/
def time (v:Values):Nat:=
  (5*(v (.aux .two)).length+4)+(5*(v (.aux .opposite)).length+4)+
    (AE.totalTime (v (.aux .two)) (v (.aux .opposite)) (v .width)+1)+
    ((v (.aux .correction)).length+3)+(6*(word v).length+7)
/-- The SAME fixed Newton source actually writes the exact canonical scalar correction and physically clears all work. -/
theorem source_run (v:Values) (hc:Clean v) (hs:v (.aux .copyScratch)=[]):
    Runs program (time v) (ctl .addLeft) (data v) (ctl .roundUpdate) (data (result v)):=by
  let v1:=Function.update v .addLeft (v (.aux .two))
  let v2:=Function.update v1 .addRight (v (.aux .opposite))
  let v3:=Function.update v .addOutput (word v)
  let v4:=Function.update v3 (.aux .correction) []
  have h0:=copy_view .addLeft (ctl .addLeft) (ctl .addRight) v rfl hs
  simp only [copyFrom,copyTo,hc.left,List.append_nil] at h0
  change Runs program (5*(v (.aux .two)).length+4) _ _ _ (data v1) at h0
  have hs1:v1 (.aux .copyScratch)=[]:=by simp [v1,hs]
  have h1:=copy_view .addRight (ctl .addRight) (ctl .add) v1 rfl hs1
  have ho1:v1 (.aux .opposite)=v (.aux .opposite):=rfl
  have hr1:v1 .addRight=[]:=by simp [v1,hc.right]
  simp only [copyFrom,copyTo,ho1,hr1,List.append_nil] at h1
  change Runs program (5*(v (.aux .opposite)).length+4) _ _ _ (data v2) at h1
  have h2:=add_call (ctl .add) (ctl .clearCorrection) v2 rfl (by simp [v2,v1,hc.output])
  have hword:addWord v2=word v:=by simp [addWord,AE.result,word,v2,v1]
  have htime:addTime v2=AE.totalTime (v (.aux .two)) (v (.aux .opposite)) (v .width)+1:=by
    simp [addTime,v2,v1]
  rw [hword,htime] at h2
  have he2:added v2 (word v)=v3:=by
    funext s
    cases s with
    | addLeft=>simp [added,v2,v1,v3,hc.left]
    | addRight=>simp [added,v2,v1,v3,hc.right]
    | _=>rfl
  rw [he2] at h2
  have h3:=drain_call (ctl .clearCorrection) (ctl .saveCorrection) (.aux .correction) v3 rfl
  have hv3:v3 (.aux .correction)=v (.aux .correction):=rfl
  rw [hv3] at h3
  have hs4:v4 (.aux .copyScratch)=[]:=by simp [v4,v3,hs]
  have h4:=move_call .correction (ctl .saveCorrection) (ctl .roundUpdate) v4 rfl hs4
  change Runs program (6*(v4 .addOutput).length+7) _ _ _ _ at h4
  have ho4:v4 .addOutput=word v:=by simp [v4,v3]
  rw [ho4] at h4
  have he4:moved v4 .correction=result v:=by
    funext s
    cases s with
    | aux a=>cases a <;> simp [moved,v4,v3,moveFrom,moveTo,result]
    | _=>simp [moved,v4,v3,moveFrom,moveTo,result,hc.output]
  rw [he4] at h4
  exact join (join (join (join h0 h1) h2) h3) h4
end RiemannGaussian.SemiprimeD1StackRecoveryFinishCorrection
