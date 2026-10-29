/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishMultiply
import RiemannGaussian.SemiprimeD1StackRecoveryFinishCorrection
/-! # Actual precision-marker Newton loop of the fixed recovery source
Each actual marker executes exactly the old three-product/one-sum word order.
Only the physical todo tape drives iteration. Loop values and clocks below are
proof descriptions of these actual executions, never supplied source operands.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishNewton
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackProcedureTrace
namespace MP
export SemiprimeD1StackRecoveryFinishMultiply (Clean target word result time source_call)
end MP
namespace CP
export SemiprimeD1StackRecoveryFinishCorrection (Clean word result time source_run)
end CP
local notation "ctl"=>Label.local
/-- Every real scalar operator and the real preserving-copy scratch are empty at an iteration boundary. -/
structure Clean (v:Values):Prop where
  /-- Entire real multiplier workspace. -/
  multiply:MP.Clean v
  /-- Entire real modular-adder workspace. -/
  add:CP.Clean v
  /-- Actual restoring-copy scratch. -/
  scratch:v (.aux .copyScratch)=[]
/-- Nonfinal real product result preserves all clean scalar-workspace predicates. -/
theorem clean_product (v:Values) (site:MulSite) (hn:site≠.final) (hc:Clean v):Clean (MP.result v site):=by
  cases site with
  | final=>exact (hn rfl).elim
  | _=>exact ⟨⟨hc.multiply.left,hc.multiply.right,hc.multiply.counter,hc.multiply.accumulator,hc.multiply.output⟩,
      ⟨hc.add.left,hc.add.right,hc.add.output⟩,hc.scratch⟩
/-- Real correction-cache replacement preserves every scalar workspace and copy scratch. -/
theorem clean_correction (v:Values) (hc:Clean v):Clean (CP.result v):=
  ⟨⟨hc.multiply.left,hc.multiply.right,hc.multiply.counter,hc.multiply.accumulator,hc.multiply.output⟩,
    ⟨hc.add.left,hc.add.right,hc.add.output⟩,hc.scratch⟩
/-- Popping the actual marker tape touches no arithmetic workspace or copy scratch. -/
theorem clean_todo (v:Values) (bits:List Bool) (hc:Clean v):Clean (Function.update v (.aux .todo) bits):=
  ⟨⟨hc.multiply.left,hc.multiply.right,hc.multiply.counter,hc.multiply.accumulator,hc.multiply.output⟩,
    ⟨hc.add.left,hc.add.right,hc.add.output⟩,hc.scratch⟩
/-- Actual first Newton product cache a*x. -/
def first (v:Values):Values:=MP.result v .product
/-- Actual second Newton product cache negative*(a*x). -/
def second (v:Values):Values:=MP.result (first v) .opposite
/-- Actual scalar correction cache two+opposite. -/
def correction (v:Values):Values:=CP.result (second v)
/-- Actual final product replaces the prior current cache only after it was physically copied and used. -/
def stepResult (v:Values):Values:=MP.result (correction v) .update
/-- Own complete actual Newton stage clock: three real cached-product invocations and one real sum/cache invocation. -/
def stepTime (v:Values):Nat:=MP.time v .product+MP.time (first v) .opposite+CP.time (second v)+MP.time (correction v) .update
/-- Exact actual full Newton stage, including every physical copy/drain/return. -/
theorem step_run (v:Values) (hc:Clean v):
    Runs program (stepTime v) (ctl .roundProduct) (data v) (ctl .loop) (data (stepResult v)):=by
  have h0:=MP.source_call .product (ctl .roundProduct) (ctl .roundOpposite) v hc.multiply hc.scratch rfl
  have hc1:=clean_product v .product (by decide) hc
  have h1:=MP.source_call .opposite (ctl .roundOpposite) (ctl .addLeft) (first v) hc1.multiply hc1.scratch rfl
  have hc2:=clean_product (first v) .opposite (by decide) hc1
  have h2:=CP.source_run (second v) hc2.add hc2.scratch
  have hc3:=clean_correction (second v) hc2
  have h3:=MP.source_call .update (ctl .roundUpdate) (ctl .loop) (correction v) hc3.multiply hc3.scratch rfl
  exact join (join (join h0 h1) h2) h3
/-- Every actual scalar/copy work role is clean again at the complete stage boundary. -/
theorem clean_step (v:Values) (hc:Clean v):Clean (stepResult v):=
  clean_product (correction v) .update (by decide)
    (clean_correction (second v) (clean_product (first v) .opposite (by decide) (clean_product v .product (by decide) hc)))
/-- Exact old Newton step word order, with no algebraic reassociation or padding identification. -/
theorem step_current (v:Values):stepResult v (.aux .current)=
    (SemiprimeD1OddInverseBits.step (v .width).length (v (.aux .inverseInput))
      (v (.aux .negative)) (v (.aux .two)) (v (.aux .current))).bits:=by
  simp [stepResult,correction,second,first,MP.result,MP.target,MP.word,CP.result,CP.word,multiplyFromLeft,multiplyFromRight,SemiprimeD1OddInverseBits.step]
/-- Actual stage changes only the current/product/opposite/correction caches. -/
def Stable (s:Slot):Prop:=s≠.aux .current ∧s≠.aux .product ∧s≠.aux .opposite ∧s≠.aux .correction
/-- Every actual source/metadata/operand/cache word outside the four stage outputs is retained literally. -/
theorem step_preserved (v:Values) (s:Slot) (hs:Stable s):stepResult v s=v s:=by
  simp only [stepResult,correction,second,first,MP.result,MP.target,CP.result,
    Function.update_of_ne hs.1,Function.update_of_ne hs.2.1,Function.update_of_ne hs.2.2.1,Function.update_of_ne hs.2.2.2]
/-- Actual marker pop followed by one complete physical Newton stage. -/
def advance (v:Values):Values:=stepResult (Function.update v (.aux .todo) (v (.aux .todo)).tail)
/-- Actual clean state is preserved through a marker pop and its whole physical stage. -/
theorem clean_advance (v:Values) (hc:Clean v):Clean (advance v):=clean_step _ (clean_todo _ _ hc)
/-- Proof-side exact sequence of states generated by actual marker pops; it is not executed as an instruction. -/
def states:Nat→Values→Values
  | 0,v=>v
  | n+1,v=>states n (advance v)
/-- Own actual loop clock sums the actual chosen stage traces and actual final marker EOF test. -/
def budget:Nat→Values→Nat
  | 0,_=>1
  | n+1,v=>1+stepTime (Function.update v (.aux .todo) (v (.aux .todo)).tail)+budget n (advance v)
/-- Complete SAME-program Newton loop reads actual precision markers, with no supplied iteration or inverse opcode. -/
theorem loop_run (n:Nat) (v:Values) (hc:Clean v) (ht:v (.aux .todo)=List.replicate n true):
    Runs program (budget n v) (ctl .loop) (data v) (ctl .signChoice) (data (states n v)):=by
  induction n generalizing v with
  | zero=>
    have h:=pop_view (ctl .loop) (ctl .signChoice) (ctl .abort) (ctl .roundProduct) (.aux .todo) v [] rfl ht
    have he:Function.update v (.aux .todo) []=v:=Function.update_eq_self_iff.mpr ht.symm
    simp only [List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose] at h
    rw [he] at h
    exact h
  | succ n ih=>
    have h0:=pop_view (ctl .loop) (ctl .signChoice) (ctl .abort) (ctl .roundProduct) (.aux .todo) v
      (List.replicate (n+1) true) rfl ht
    have htail:(v (.aux .todo)).tail=List.replicate n true:=by rw [ht];rfl
    change Runs program 1 (ctl .loop) (data v) (ctl .roundProduct)
      (data (Function.update v (.aux .todo) (List.replicate n true))) at h0
    rw [←htail] at h0
    have h1:=step_run (Function.update v (.aux .todo) (v (.aux .todo)).tail) (clean_todo v _ hc)
    have htodo:advance v (.aux .todo)=List.replicate n true:=by
      rw [advance,step_preserved _ (.aux .todo) (by simp [Stable]),Function.update_same]
      exact htail
    have h2:=ih (advance v) (clean_advance v hc) htodo
    exact join (join h0 h1) h2
end RiemannGaussian.SemiprimeD1StackRecoveryFinishNewton
