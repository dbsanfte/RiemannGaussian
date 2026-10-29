/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanTreeExecution

/-! # Actual Boolean tree writer: linear output time and complete storage
This is the actual fixed machine's clock, not the old build/serialization report.
Only stream framing is claimed: acquiring entries and depth remains caller work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackBooleanTreeBounds
open SemiprimeD1StackBooleanTree SemiprimeD1StackBooleanTreeExecution
open SemiprimeD1BooleanTreeStream (bytes bytes_length leafBytes)
/-- Actual body visits both children, paying all real calls/returns/marker restores. -/
theorem bodyTime_plus7_le (depth raw : List Bool) : bodyTime depth raw+7≤15*2^depth.length := by
  induction depth generalizing raw with
  | nil=>
    cases h:raw.head?.getD false <;> simp [bodyTime,leafBytes,h]
  | cons b depth ih=>
    have hl:=ih raw
    have hr:=ih (raw.drop (2^depth.length))
    simp only [bodyTime,List.length_cons,pow_succ]
    omega
/-- Uniform actual source clock, before every entry stream and marker bit pattern. -/
def runBound (depth : List Bool) : ℕ := 40*2^depth.length
/-- All actual body/entry/codec/reversal/call/halt steps are paid. -/
theorem totalTime_le (raw depth : List Bool) : totalTime raw depth≤runBound depth := by
  have hb:=bodyTime_plus7_le depth raw
  have hl:=(bytes_length depth.length raw).2
  unfold totalTime runBound
  omega
/-- The whole actual framing time is LINEAR in the actual emitted old-codec
byte count, even for short/defaulted streams and arbitrary unused suffixes. -/
theorem time_le_output (raw depth : List Bool) : totalTime raw depth≤10*(bytes depth.length raw).length := by
  have h:=totalTime_le raw depth
  have hl:=(bytes_length depth.length raw).1
  unfold runBound at h
  omega
/-- The same source trace with its actual exponential-in-physical-depth bound. -/
def sourceTree (raw depth : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial raw depth)
      (some (done raw depth)) (runBound depth) := ⟨⟨_,source_run raw depth⟩,totalTime_le raw depth⟩
/-- Genuine fixed finite machine executes this complete literal writer. -/
def machineTree (raw depth : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial raw depth))
      (some (SemiprimeD1StackCalls.configuration (done raw depth))) (runBound depth) :=
  SemiprimeD1StackCalls.evalsCorrect Stack.input Stack.output Label.start program _ _ _ (sourceTree raw depth)
/-- Genuine SAME-machine output-linear clock, not a semantic-clock transfer. -/
def machineTreeLinear (raw depth : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial raw depth))
      (some (SemiprimeD1StackCalls.configuration (done raw depth))) (10*(bytes depth.length raw).length) :=
  SemiprimeD1StackCalls.evalsCorrect Stack.input Stack.output Label.start program _ _ _
    ⟨⟨_,source_run raw depth⟩,time_le_output raw depth⟩
/-- Literal old-codec tree bytes occupy the actual output stack. -/
theorem output_original (raw depth : List Bool) : (done raw depth).data .output=bytes depth.length raw := rfl
/-- Every consumed depth marker is physically restored with its exact input bit. -/
theorem retained_depth (raw depth : List Bool) : (done raw depth).data .depth=depth := rfl
/-- Only actual queried entry bits are consumed; all remaining input stays intact. -/
theorem retained_suffix (raw depth : List Bool) : (done raw depth).data .input=raw.drop (2^depth.length) := rfl
/-- No successful actual prefix extends beyond the complete literal halt. -/
theorem prefix_fuel_le (raw depth : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial raw depth)=some out) : fuel≤totalTime raw depth := by
  by_contra hn
  have he : fuel=totalTime raw depth+(1+(fuel-(totalTime raw depth+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
  have hz : C.run program 1 (done raw depth)=none := rfl
  rw [hz,Option.bind_none] at hr
  cases hr
/-- EVERY prefix includes all four data roles AND all actual recursive return
cells. Bound is linear in initial bytes plus emitted old-codec bytes. -/
theorem prefix_cells (raw depth : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial raw depth)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤
      5*(raw.length+depth.length+10*(bytes depth.length raw).length) := by
  let I:=raw.length+depth.length
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ out (by
    intro k;cases k <;> simp [initial,store,I]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length)≤4*(I+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(I+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=(prefix_fuel_le raw depth fuel out hr).trans (time_le_output raw depth)
  change _≤5*(I+10*(bytes depth.length raw).length)
  omega
/-- Same all-stack/real-return inventory for the compiled fixed finite machine. -/
theorem machine_prefix_cells (raw depth : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial raw depth)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      5*(raw.length+depth.length+10*(bytes depth.length raw).length) := by
  have he:=SemiprimeD1StackCalls.run_correct Stack.input Stack.output Label.start program fuel (initial raw depth)
  change (C.run program fuel (initial raw depth)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial raw depth))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial raw depth) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells raw depth fuel out hc
end RiemannGaussian.SemiprimeD1StackBooleanTreeBounds
