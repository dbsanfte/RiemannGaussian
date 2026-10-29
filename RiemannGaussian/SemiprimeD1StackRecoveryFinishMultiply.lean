/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishMoves
import RiemannGaussian.SemiprimeD1StackRecoveryFinishOperators
/-! # Full actual cached-product subprocedures of the fixed recovery source
Each literal site copies both actual operands, calls the real modular multiplier,
clears its actual destination after the product is acquired, transfers/drains the
real output, and returns through the actual finite hardware return stack.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishMultiply
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackRecoveryFinishMoves
open SemiprimeD1StackRecoveryFinishProjection SemiprimeD1StackRecoveryFinishOperators SemiprimeD1StackProcedureTrace
/-- Actual whole multiplier bank is clean before a cached-product invocation. -/
structure Clean (v:Values):Prop where
  /-- Actual first operand is empty before its paid copy. -/
  left:v .mulLeft=[]
  /-- Actual second operand is empty before its paid copy. -/
  right:v .mulRight=[]
  /-- Actual temporary reducer counter is empty. -/
  counter:v .reduceWidth=[]
  /-- Actual temporary product/reducer accumulator is empty. -/
  accumulator:v .reduceInput=[]
  /-- Actual product output is empty before the real source call. -/
  output:v .output=[]
/-- Exact actual destination of each fixed product procedure. -/
def target:MulSite→Slot
  | .product=>.aux .product | .opposite=>.aux .opposite | .update=>.aux .current
  | .signed=>.aux .signedResidue | .final=>.output
/-- Literal canonical word acquired by each real product procedure. -/
def word (v:Values) (site:MulSite):List Bool:=
  (SemiprimeD1JetScalarBits.mul (v .width).length (v (multiplyFromLeft site)) (v (multiplyFromRight site))).bits
/-- Exact all-live-word procedure result; every other source/cache word is preserved. -/
def result (v:Values) (site:MulSite):Values:=Function.update v (target site) (word v site)
/-- Actual loader and multiplier-call source clock, with both paid operand copies. -/
def loadTime (v:Values) (site:MulSite):Nat:=
  (5*(v (multiplyFromLeft site)).length+4)+(5*(v (multiplyFromRight site)).length+4)+
    (ME.totalTime (v (multiplyFromLeft site)) (v (multiplyFromRight site)) (v .width)+1)
/-- Real final return label, before the actual hardware return is popped. -/
def returnSite (site:MulSite):Label:=if site=.final then .mul site 3 else .mul site 5
/-- Own actual callee clock, including destination drain/output movement at nonfinal sites. -/
def bodyTime (v:Values) (site:MulSite):Nat:=
  loadTime v site+(if site=.final then 0 else (v (target site)).length+3+(6*(word v site).length+7))
/-- Complete actual nested invocation includes the actual call and actual final return. -/
def time (v:Values) (site:MulSite):Nat:=bodyTime v site+2
/-- An actual arbitrary finite return label is popped only after the real callee trace reaches it. -/
theorem call_return (pc entry finish next:Label) (before after:Stack→List Bool) (t:Nat)
    (hc:program pc=.call entry next) (hret:program finish=.ret)
    (hr:Runs program t entry before finish after):Runs program (t+2) pc before next after:=by
  intro frames start h
  rcases h with ⟨hp,hd,hf⟩
  let mid:=SemiprimeD1StackCalls.execute (.call entry next) start
  have hm:SemiprimeD1StackCalls.run program 1 start=some mid:=by
    change SemiprimeD1StackCalls.step program start=some mid
    simp only [SemiprimeD1StackCalls.step,hp,Option.map_some,hc,mid]
  obtain ⟨out,hrun,hat⟩:=hr (next::frames) mid (by
    simp only [At,mid,SemiprimeD1StackCalls.execute,hd,hf,and_self])
  let last:=SemiprimeD1StackCalls.execute .ret out
  have hl:SemiprimeD1StackCalls.run program 1 out=some last:=by
    change SemiprimeD1StackCalls.step program out=some last
    simp only [SemiprimeD1StackCalls.step,hat.1,Option.map_some,hret,last]
  refine ⟨last,?_,?_,?_,?_⟩
  · rw [show t+2=1+(t+1) by omega,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add,hrun,Option.bind_some]
    exact hl
  · simp only [last,SemiprimeD1StackCalls.execute,hat.2.2]
  · simpa only [last,SemiprimeD1StackCalls.execute,hat.2.2] using hat.2.1
  · simp only [last,SemiprimeD1StackCalls.execute,hat.2.2]
/-- Exact real two-copy loader and modular-product source, retaining every original operand cache until the result exists. -/
theorem loaded_run (site:MulSite) (v:Values) (hc:Clean v) (hs:v (.aux .copyScratch)=[]):
    Runs program (loadTime v site) (.mul site 0) (data v) (.mul site 3)
      (data (Function.update v .output (word v site))):=by
  let a:=v (multiplyFromLeft site)
  let b:=v (multiplyFromRight site)
  let v1:=Function.update v .mulLeft a
  let v2:=Function.update v1 .mulRight b
  have h0:=copy_view (.mulLeft site) (.mul site 0) (.mul site 1) v rfl hs
  simp only [copyFrom,copyTo,hc.left,List.append_nil] at h0
  change Runs program (5*a.length+4) _ _ _ (data v1) at h0
  have hs1:v1 (.aux .copyScratch)=[]:=by simp [v1,hs]
  have h1:=copy_view (.mulRight site) (.mul site 1) (.mul site 2) v1 rfl hs1
  have hb:v1 (multiplyFromRight site)=b:=by cases site <;> rfl
  have hright:v1 .mulRight=[]:=by simp [v1,hc.right]
  simp only [copyFrom,copyTo,hb,hright,List.append_nil] at h1
  change Runs program (5*b.length+4) _ _ _ (data v2) at h1
  have h2:=multiply_call (.mul site 2) (.mul site 3) v2 rfl
    (by simp [v2,v1,hc.counter]) (by simp [v2,v1,hc.accumulator]) (by simp [v2,v1,hc.output])
  have hword:multiplyWord v2=word v site:=by simp [multiplyWord,ME.result,word,v2,v1,a,b]
  have htime:multiplyTime v2=ME.totalTime a b (v .width)+1:=by simp [multiplyTime,v2,v1]
  rw [hword,htime] at h2
  have he:multiplied v2 (word v site)=Function.update v .output (word v site):=by
    funext s
    cases s with
    | mulLeft=>simp [multiplied,v2,v1,hc.left]
    | mulRight=>simp [multiplied,v2,v1,hc.right]
    | _=>rfl
  rw [he] at h2
  exact join (join h0 h1) h2
/-- Whole actual nonfinal callee includes real destination clearing and actual source-consuming output transfer. -/
theorem nonfinal_run (site:MulSite) (hn:site≠.final) (v:Values) (hc:Clean v) (hs:v (.aux .copyScratch)=[]):
    Runs program (bodyTime v site) (.mul site 0) (data v) (.mul site 5) (data (result v site)):=by
  let v3:=Function.update v .output (word v site)
  let v4:=Function.update v3 (target site) []
  have h0:=loaded_run site v hc hs
  have hc1:program (.mul site 3)=.call (.drain (address (target site))) (.mul site 4):=by
    cases site with
    | final=>exact (hn rfl).elim
    | _=>rfl
  have h1:=drain_call (.mul site 3) (.mul site 4) (target site) v3 hc1
  have hv3:v3 (target site)=v (target site):=by
    cases site with
    | final=>exact (hn rfl).elim
    | _=>rfl
  rw [hv3] at h1
  have hs4:v4 (.aux .copyScratch)=[]:=by cases site <;> simp [v4,v3,target,hs]
  have hc2:program (.mul site 4)=.call (.move (multiplyMove site) false) (.mul site 5):=by rfl
  have h2:=move_call (multiplyMove site) (.mul site 4) (.mul site 5) v4 hc2 hs4
  have hfrom:moveFrom (multiplyMove site)=.output:=by cases site <;> rfl
  have hout:v4 .output=word v site:=by
    cases site with
    | final=>exact (hn rfl).elim
    | _=>simp [v4,v3,target]
  rw [hfrom,hout] at h2
  have he:moved v4 (multiplyMove site)=result v site:=by
    cases site with
    | final=>exact (hn rfl).elim
    | _=>
      funext s
      cases s with
      | aux a=>cases a <;> simp [moved,v4,v3,target,multiplyMove,moveFrom,moveTo,result]
      | _=>simp [moved,v4,v3,target,multiplyMove,moveFrom,moveTo,result,hc.output]
  rw [he] at h2
  have h:=join (join h0 h1) h2
  simpa only [bodyTime,ite_eq_right hn,Nat.add_assoc] using h
/-- Full actual product subprocedure, through its literal final return label. -/
theorem body_run (site:MulSite) (v:Values) (hc:Clean v) (hs:v (.aux .copyScratch)=[]):
    Runs program (bodyTime v site) (.mul site 0) (data v) (returnSite site) (data (result v site)):=by
  by_cases h:site=.final
  · subst site
    simpa only [bodyTime,returnSite,ite_true,Nat.add_zero,result,target] using loaded_run .final v hc hs
  · simpa only [returnSite,ite_eq_right h] using nonfinal_run site h v hc hs
/-- One whole actual nested cached-product call, with its own physical copies/drains/real-return clock. -/
theorem source_call (site:MulSite) (pc next:Label) (v:Values) (hc:Clean v) (hs:v (.aux .copyScratch)=[])
    (hcode:program pc=.call (.mul site 0) next):
    Runs program (time v site) pc (data v) next (data (result v site)):=by
  apply call_return pc (.mul site 0) (returnSite site) next _ _ _ hcode
  · cases site <;> rfl
  · exact body_run site v hc hs
end RiemannGaussian.SemiprimeD1StackRecoveryFinishMultiply
