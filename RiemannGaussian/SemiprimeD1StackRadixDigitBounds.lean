/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRadixDigitExecution
import RiemannGaussian.SemiprimeD1OriginalNativeWidths

/-! # Actual radix-extraction machine and original public parameter bounds
The original integer is binary. Counter acquisition is a caller operation;
these statements bound every executed scan/copy/cleanup once counters exist.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRadixDigitBounds
open SemiprimeD1StackRadixDigit SemiprimeD1StackRadixDigitExecution SemiprimeBitArithmetic

/-- Actual target halt has only the digit output and no returned/work payload. -/
theorem finish_configuration (bits : List Bool) :
    SemiprimeD1StackCalls.configuration
      (⟨none,none,none,store [] [] [] [] [] bits,[]⟩:C.State Stack Label)=Turing.haltList machine bits := by
  have hs : (⟨none,none,none,store [] [] [] [] [] bits,[]⟩:C.State Stack Label)=
      SemiprimeD1StackCalls.final Stack.output bits := by
    congr 1
    funext k
    cases k <;> rfl
  rw [hs]
  exact SemiprimeD1StackCalls.final_correct Stack.input Stack.output Label.start program bits

/-- Actual finite machine digit extraction. Width/index are explicit physical
caller stacks, not hidden natural-number arguments or offset/power advice. -/
def machineDigit (word width index : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (⟨some .start,none,none,store word width index [] [] [],[]⟩:C.State Stack Label))
      (some (Turing.haltList machine (result word width index))) (timeBound word width index) := by
  have hh:=SemiprimeD1StackCalls.evalsCorrect Stack.input Stack.output Label.start program _ _ _
    (sourceDigit word width index)
  change StateTransition.EvalsToInTime machine.step
    (SemiprimeD1StackCalls.configuration
      (⟨some .start,none,none,store word width index [] [] [],[]⟩:C.State Stack Label))
    (some (SemiprimeD1StackCalls.configuration
      (⟨none,none,none,store [] [] [] [] [] (result word width index),[]⟩:C.State Stack Label)))
    (timeBound word width index) at hh
  exact Eq.mp (congrArg (fun finish : machine.Cfg=>
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (⟨some .start,none,none,store word width index [] [] [],[]⟩:C.State Stack Label))
      (some finish) (timeBound word width index)) (finish_configuration (result word width index))) hh

/-- Every successful prefix stops before the actual proved machine halt. -/
theorem prefix_fuel_le (word width index : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (⟨some .start,none,none,store word width index [] [] [],[]⟩:C.State Stack Label)=some out) :
    fuel ≤ timeBound word width index := by
  have hf : fuel ≤ totalTime word width index := by
    by_contra hn
    have he : fuel=totalTime word width index+(1+(fuel-(totalTime word width index+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1
      (⟨none,none,none,store [] [] [] [] [] (result word width index),[]⟩:C.State Stack Label)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans (totalTime_le word width index)

/-- All actual source prefixes count data plus physical finite-label return cells. -/
theorem prefix_cells (word width index : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (⟨some .start,none,none,store word width index [] [] [],[]⟩:C.State Stack Label)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      7*(word.length+width.length+index.length+timeBound word width index) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (word.length+width.length+index.length)
    _ out (by intro k;cases k <;> simp only [store,List.length_nil] <;> omega) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 6*(word.length+width.length+index.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(word.length+width.length+index.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by
        have hc : Fintype.card Stack=6 := by decide
        simp only [Finset.sum_const,Finset.card_univ,hc,smul_eq_mul]
  have ht:=prefix_fuel_le word width index fuel out hr
  omega

/-- Every reached target configuration, with no fuel premise, has the same total bound. -/
theorem machine_prefix_cells (word width index : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (⟨some .start,none,none,store word width index [] [] [],[]⟩:C.State Stack Label)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      7*(word.length+width.length+index.length+timeBound word width index) := by
  let start : C.State Stack Label:=⟨some .start,none,none,store word width index [] [] [],[]⟩
  have he:=SemiprimeD1StackCalls.run_correct Stack.input Stack.output Label.start program fuel start
  change (C.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  rw [hr] at he
  cases hc:C.run program fuel start with
  | none => rw [hc] at he;cases he
  | some out =>
    rw [hc] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    subst cfg
    exact prefix_cells word width index fuel out hc

/-- Original radix and digit counters obey the internally proved public dimension bounds. -/
theorem original_counter_bounds (ell : ℕ) (hell : 0<ell) (width index : List Bool)
    (hw : width.length=SemiprimeMacroParameters.radixBits ell)
    (hi : index.length ≤ SemiprimeMacroParameters.digitCount ell) :
    width.length ≤ 64*ell ∧ index.length ≤ 64*ell := by
  have hd:=SemiprimeD1OriginalNativeWidths.public_dimensions ell hell
  exact ⟨hw ▸ hd.2.2.2.1,hi.trans hd.2.2.2.2⟩

/-- Every original public target digit is acquired in a fixed quadratic bound
in original binary input LENGTH; no native power/quotient is executed. -/
theorem original_time (ell : ℕ) (hell : 0<ell) (word width index : List Bool)
    (hn : word.length=ell) (hw : width.length=SemiprimeMacroParameters.radixBits ell)
    (hi : index.length ≤ SemiprimeMacroParameters.digitCount ell) :
    timeBound word width index ≤ 30000*(ell+1)^2 := by
  have hc:=original_counter_bounds ell hell width index hw hi
  have hm : (7*width.length+6)*index.length ≤ (7*(64*ell)+6)*(64*ell) :=
    Nat.mul_le_mul (by omega) hc.2
  unfold timeBound
  rw [hn]
  nlinarith [sq_nonneg (ell : ℤ)]

/-- The same actual public digit implementation has quadratic total prefix space. -/
theorem original_space (ell : ℕ) (hell : 0<ell) (word width index : List Bool)
    (hn : word.length=ell) (hw : width.length=SemiprimeMacroParameters.radixBits ell)
    (hi : index.length ≤ SemiprimeMacroParameters.digitCount ell) :
    7*(word.length+width.length+index.length+timeBound word width index) ≤ 220000*(ell+1)^2 := by
  have hc:=original_counter_bounds ell hell width index hw hi
  have ht:=original_time ell hell word width index hn hw hi
  rw [hn]
  nlinarith [sq_nonneg (ell : ℤ)]

end RiemannGaussian.SemiprimeD1StackRadixDigitBounds
