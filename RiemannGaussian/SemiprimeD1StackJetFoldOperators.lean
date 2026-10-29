/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldPrimitives
import RiemannGaussian.SemiprimeD1StackJetFoldProjection
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Real frozen multiplication, unit and addition calls of the same fold
Every component execution is the concrete immutable source trace, with actual
shared operand/cache words and actual physical return transitions.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldOperators
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldState SemiprimeD1StackJetFoldProjection
open SemiprimeD1StackJetFoldWords SemiprimeD1StackProcedureTrace
open SemiprimeD1JetAxes (Context)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
local notation "ctl" => Label.local
/-- Actual physical multiplier input inventory, used only to state its proved source allowance. -/
def mulBound (ctx:Context) (v:Values):Nat:=
  2000000*(SemiprimeD1StackJetMulBounds.inputSize ctx (cache v)+1)^6+1
/-- One actual whole dense multiplication, including every point calculation and the real caller return. -/
theorem multiply_call (ctx:Context) (hp:ctx.Positive) (v:Values) (a b:Jet)
    (ha:v .left=jetTape a) (hb:v .product=jetTape b)
    (hx:v .axes=vectorBits (ctx.axes.map unary)) (hw:(v .width).length=ctx.precision)
    (hr:v .rank=unary ctx.rank) (ho:v .result=[]):
    ∃time ≤ mulBound ctx v,Runs program time (ctl .multiply) (data v) (ctl .clearLeft)
      (data (Function.update v .result (jetTape (SemiprimeD1JetRingBits.mul ctx a b).words))):=by
  obtain ⟨time,ht,hrun⟩:=SemiprimeD1StackJetMulBounds.source_run_polynomial ctx hp (cache v) a b ha hb hx hw hr
  let source:=M.initial (v .left) (v .product) (v .axes) (v .width) (v .rank)
  let out:SemiprimeD1StackCalls.State M.Stack M.Label:=⟨none,none,none,
    SemiprimeD1StackJetMulExecution.data (cache v) [] [] (jetTape (SemiprimeD1JetRingBits.mul ctx a b).words),[]⟩
  have hin:SemiprimeD1StackMultiplierLink.DataRel main (data v) source.data (data v):=by
    constructor
    · intro k
      rw [data_main,ho]
      exact (congrFun (SemiprimeD1StackJetMulExecution.initial_data (cache v)) k).symm
    · intro k _;rfl
  refine ⟨time+1,by unfold mulBound;omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program main Label.multiply Sum.inl_injective
    M.program .start (fun _=>rfl) (ctl .multiply) (ctl .clearLeft) rfl time source out _ _
    rfl rfl rfl rfl hrun hin
  have h:=SemiprimeD1StackMultiplierLink.data_update main Sum.inl_injective (data v) source.data (data v) hin M.output
    (jetTape (SemiprimeD1JetRingBits.mul ctx a b).words)
  have he:Function.update source.data M.output (jetTape (SemiprimeD1JetRingBits.mul ctx a b).words)=out.data:=by
    change Function.update (M.initial (cache v).a (cache v).b (cache v).axes (cache v).width (cache v).rank).data
      M.output (jetTape (SemiprimeD1JetRingBits.mul ctx a b).words)=_
    rw [SemiprimeD1StackJetMulExecution.initial_data,SemiprimeD1StackJetMulExecution.data_output_update]
  rw [he] at h
  change SemiprimeD1StackMultiplierLink.DataRel main (data v) out.data
    (Function.update (data v) (address .result) (jetTape (SemiprimeD1JetRingBits.mul ctx a b).words)) at h
  rw [←data_update] at h
  exact h
/-- Updating the real unit output preserves all acquired cache and zero private roles. -/
theorem unit_output_update (width rank out:List Bool):
    Function.update (SemiprimeD1StackJetUnit.bank width rank [] [] []) U.output out=
      SemiprimeD1StackJetUnit.bank width rank [] [] out:=by
  funext k;fin_cases k <;> rfl
/-- One real unit call computes the native empty product from the physically acquired counters. -/
theorem unit_call (ctx:Context) (v:Values) (hw:(v .width).length=ctx.precision)
    (hr:(v .rank).length=ctx.rank) (hb:v .product=[]):
    Runs program (SemiprimeD1StackJetUnitExecution.totalTime (v .width) (v .rank)+1)
      (ctl .unit) (data v) (ctl .returning)
      (data (Function.update v .product (jetTape (SemiprimeD1JetAffineCoefficient.one ctx).words))):=by
  let source:=SemiprimeD1StackJetUnit.initial (v .width) (v .rank)
  let out:SemiprimeD1StackCalls.State U.Stack U.Label:=⟨none,none,none,
    SemiprimeD1StackJetUnit.bank (v .width) (v .rank) [] [] (jetTape (SemiprimeD1JetAffineCoefficient.one ctx).words),[]⟩
  have hin:SemiprimeD1StackMultiplierLink.DataRel unitStack (data v) source.data (data v):=by
    constructor
    · intro k;rw [data_unit,hb];rfl
    · intro k _;rfl
  apply SemiprimeD1StackProcedureCallsTrace.included_call program unitStack Label.unit unit_injective
    U.program .seed0 (fun _=>rfl) (ctl .unit) (ctl .returning) rfl _ source out _ _
    rfl rfl rfl rfl (SemiprimeD1StackJetUnitExecution.source_run ctx _ _ hw hr) hin
  have h:=SemiprimeD1StackMultiplierLink.data_update unitStack unit_injective (data v) source.data (data v) hin U.output
    (jetTape (SemiprimeD1JetAffineCoefficient.one ctx).words)
  have he:Function.update source.data U.output (jetTape (SemiprimeD1JetAffineCoefficient.one ctx).words)=out.data:=
    unit_output_update _ _ _
  rw [he] at h
  change SemiprimeD1StackMultiplierLink.DataRel unitStack (data v) out.data
    (Function.update (data v) (address .product) (jetTape (SemiprimeD1JetAffineCoefficient.one ctx).words)) at h
  rw [←data_update] at h
  exact h
/-- The actual adder consumes both physical operands and writes only its real output. -/
theorem add_store_updates (width rank a b out:List Bool):
    Function.update (Function.update (Function.update
      (A.store [] [] [] [] width [] a b rank [] [] [] [] [] []) (.inr .leftTape) []) (.inr .rightTape) []) (.inr .output) out=
      A.store [] [] [] [] width [] [] [] rank [] [] out [] [] []:=by
  funext k;fin_cases k <;> rfl
/-- Exact actual dense addition uses the literal right-fold product and saved tail-sum operands. -/
theorem add_call (ctx:Context) (v:Values) (a b:Jet)
    (ha:v .product=jetTape a) (hb:v .tailSum=jetTape b)
    (hw:(v .width).length=ctx.precision) (hr:(v .rank).length=ctx.rank) (ho:v .sum=[]):
    Runs program (SemiprimeD1StackJetAddExecution.totalTime (v .width) (v .rank) a b+1)
      (ctl .add) (data v) (ctl .returning)
      (data (Function.update (Function.update (Function.update v .product []) .tailSum []) .sum
        (jetTape (SemiprimeD1JetRingBits.add ctx a b).words))):=by
  let source:=SemiprimeD1StackJetAdd.state (some .start) none none [] [] [] [] (v .width) []
    (jetTape a) (jetTape b) (v .rank) [] [] [] [] [] []
  let out:=SemiprimeD1StackJetAdd.state none none none [] [] [] [] (v .width) [] [] [] (v .rank) [] []
    (jetTape (SemiprimeD1JetRingBits.add ctx a b).words) [] [] []
  have hin:SemiprimeD1StackMultiplierLink.DataRel addStack (data v) source.data (data v):=by
    constructor
    · intro k;rw [data_add,ha,hb,ho];rfl
    · intro k _;rfl
  have hrun:=SemiprimeD1StackJetAddExecution.source_run (v .width) (v .rank) a b
  rw [SemiprimeD1StackJetAddExecution.rows_eq_original ctx _ _ a b hw hr] at hrun
  apply SemiprimeD1StackProcedureCallsTrace.included_call program addStack Label.add add_injective
    A.program .start (fun _=>rfl) (ctl .add) (ctl .returning) rfl _ source out _ _ rfl rfl rfl rfl hrun hin
  have h0:=SemiprimeD1StackMultiplierLink.data_update addStack add_injective (data v) source.data (data v) hin (.inr .leftTape) []
  have h1:=SemiprimeD1StackMultiplierLink.data_update addStack add_injective (data v) _ _ h0 (.inr .rightTape) []
  have h2:=SemiprimeD1StackMultiplierLink.data_update addStack add_injective (data v) _ _ h1 (.inr .output)
    (jetTape (SemiprimeD1JetRingBits.add ctx a b).words)
  have he:Function.update (Function.update (Function.update source.data (.inr .leftTape) []) (.inr .rightTape) []) (.inr .output)
      (jetTape (SemiprimeD1JetRingBits.add ctx a b).words)=out.data:=add_store_updates _ _ _ _ _
  rw [he] at h2
  change SemiprimeD1StackMultiplierLink.DataRel addStack (data v) out.data
    (Function.update (Function.update (Function.update (data v) (address .product) []) (address .tailSum) []) (address .sum)
      (jetTape (SemiprimeD1JetRingBits.add ctx a b).words)) at h2
  rw [←data_update,←data_update,←data_update] at h2
  exact h2
end RiemannGaussian.SemiprimeD1StackJetFoldOperators
