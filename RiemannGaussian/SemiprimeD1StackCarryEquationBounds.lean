/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCarryEquationExecution
/-! # Actual integer carry machine: linear time and all-prefix storage
No raw operand canonicality, positivity, intermediate result or clock is assumed.
Prepared framed-record/template acquisition is explicitly a separate caller stage.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackCarryEquationBounds
open SemiprimeD1StackCarryEquation SemiprimeD1StackCarryEquationExecution
open SemiprimeBitArithmetic (addBits)
/-- Actual original operand and retained template byte count. -/
def operandSize (cached coefficient previous target next : List Bool) : ℕ :=
  cached.length+coefficient.length+previous.length+target.length+next.length
/-- One fixed linear transition envelope before every raw original input. -/
def timeBound (cached coefficient previous target next : List Bool) : ℕ :=
  100*(operandSize cached coefficient previous target next+1)
/-- Both real ripple-add traces have linear bounds in ACTUAL operands. -/
theorem addTime_le (a b : List Bool) : addTime a b ≤ 5*(a.length+b.length)+7 := by
  have h:=(SemiprimeD1StackAdderExecution.sourceAdd a b false).2
  exact h
/-- All shift/add/compare temporary lengths follow actual raw source words. -/
theorem totalTime_le (cached coefficient previous target next : List Bool) :
    totalTime cached coefficient previous target next ≤ timeBound cached coefficient previous target next := by
  have hL:=addTime_le coefficient previous
  have hR:=addTime_le target (shifted cached next)
  have he:=SemiprimeD1StackWordEqualExecution.executionTime_le (addBits coefficient previous false).bits
    (addBits target (shifted cached next) false).bits
  have hl:=(SemiprimeBitArithmetic.addBits_counts coefficient previous false).2.2.2.2
  have hr:=(SemiprimeBitArithmetic.addBits_counts target (shifted cached next) false).2.2.2.2
  have hs : (shifted cached next).length=cached.length+next.length := by
    simp only [shifted,List.length_append,List.length_replicate]
  have hml : max coefficient.length previous.length ≤ coefficient.length+previous.length := max_le (by omega) (by omega)
  have hmr : max target.length (shifted cached next).length ≤ target.length+(shifted cached next).length := max_le (by omega) (by omega)
  unfold totalTime timeBound operandSize
  omega
/-- Exact prepared record length; every framed operand occurrence is counted. -/
theorem record_length (coefficient previous target next tail : List Bool) :
    (record coefficient previous target next tail).length=
      2*(coefficient.length+previous.length+target.length+next.length)+tail.length+4 := by
  simp only [record,SemiprimeSourceHistogramKeyBits.frame_length]
  omega
/-- Genuine source certificate for the complete actual INTEGER check. -/
def sourceCheck (cached coefficient previous target next tail : List Bool) :
    StateTransition.EvalsToInTime (C.step program)
      (initial (record coefficient previous target next tail) cached)
      (some (done cached coefficient previous target next tail))
      (timeBound cached coefficient previous target next) :=
  ⟨⟨_,source_run cached coefficient previous target next tail⟩,totalTime_le cached coefficient previous target next⟩
/-- Fixed finite-stack-machine certificate at the SAME actual transition count. -/
def machineCheck (cached coefficient previous target next tail : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (record coefficient previous target next tail) cached))
      (some (SemiprimeD1StackCalls.configuration (done cached coefficient previous target next tail)))
      (timeBound cached coefficient previous target next) :=
  SemiprimeD1StackCalls.evalsCorrect Stack.input Stack.output (Label.read 0) program _ _ _
    (sourceCheck cached coefficient previous target next tail)
/-- Exact original accepted Boolean; no modular congruence has been substituted. -/
theorem output_original (cached coefficient previous target next tail : List Bool) :
    (done cached coefficient previous target next tail).data .output=
      [(SemiprimeMacroEntryBitPrimitives.carryEquationBits cached coefficient previous target next).accepted] := rfl
/-- Thus the actual output true cell is EXACTLY the original INTEGER equation. -/
theorem output_integer (cached coefficient previous target next tail : List Bool) :
    (done cached coefficient previous target next tail).data .output=[true] ↔
      SemiprimeBitArithmetic.bitValue coefficient+SemiprimeBitArithmetic.bitValue previous=
        SemiprimeBitArithmetic.bitValue target+2^cached.length*SemiprimeBitArithmetic.bitValue next := by
  rw [output_original,List.cons.injEq]
  simp only [and_true]
  exact SemiprimeMacroEntryBitPrimitives.carryEquationBits_correct cached coefficient previous target next
/-- Unconsumed physical record suffix survives exactly. -/
theorem retained_suffix (cached coefficient previous target next tail : List Bool) :
    (done cached coefficient previous target next tail).data .input=tail := rfl
/-- Original physical offset/template is retained, including arbitrary bit contents. -/
theorem retained_template (cached coefficient previous target next tail : List Bool) :
    (done cached coefficient previous target next tail).data .cached=cached := rfl
/-- All parser/shift/operand/sum/comparator work is actually empty at halt. -/
theorem cleanup (cached coefficient previous target next tail : List Bool) (k : Stack)
    (hk : k≠.input ∧ k≠.cached ∧ k≠.output) :
    (done cached coefficient previous target next tail).data k=[] := by
  cases k <;> simp_all [done,finalData,store]
/-- A successful reached prefix cannot occur beyond the actual complete halt. -/
theorem prefix_fuel_le (cached coefficient previous target next tail : List Bool)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial (record coefficient previous target next tail) cached)=some out) :
    fuel ≤ totalTime cached coefficient previous target next := by
  by_contra hn
  have he : fuel=totalTime cached coefficient previous target next+
      (1+(fuel-(totalTime cached coefficient previous target next+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run cached coefficient previous target next tail,
    Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
  have hz : C.run program 1 (done cached coefficient previous target next tail)=none := rfl
  rw [hz,Option.bind_none] at hr
  cases hr
/-- EVERY reached source state, including all twelve data stacks and actual
return labels, has a fixed LINEAR bound in physical original input inventory. -/
theorem prefix_cells (cached coefficient previous target next tail : List Bool)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial (record coefficient previous target next tail) cached)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      2000*((record coefficient previous target next tail).length+cached.length+1) := by
  let inv:=(record coefficient previous target next tail).length+cached.length
  have hdata : ∀k,((initial (record coefficient previous target next tail) cached).data k).length ≤ inv := by
    intro k;cases k <;> simp only [initial,input,store,List.length_nil] <;> dsimp [inv] <;> omega
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel inv _ out hdata hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 12*(inv+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(inv+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=(prefix_fuel_le cached coefficient previous target next tail fuel out hr).trans
    (totalTime_le cached coefficient previous target next)
  have hi : operandSize cached coefficient previous target next ≤ inv := by
    dsimp [inv,operandSize];rw [record_length];omega
  unfold timeBound at ht
  change (∑k : Stack,(out.data k).length)+out.frames.length ≤ 2000*(inv+1)
  omega
/-- The same complete all-prefix data/return inventory for genuine FinTM2. -/
theorem machine_prefix_cells (cached coefficient previous target next tail : List Bool)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (record coefficient previous target next tail) cached)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      2000*((record coefficient previous target next tail).length+cached.length+1) := by
  have he:=SemiprimeD1StackCalls.run_correct Stack.input Stack.output (Label.read 0) program fuel
    (initial (record coefficient previous target next tail) cached)
  have hh:=he.trans hr
  cases hc : C.run program fuel (initial (record coefficient previous target next tail) cached) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells cached coefficient previous target next tail fuel out hc
end RiemannGaussian.SemiprimeD1StackCarryEquationBounds
