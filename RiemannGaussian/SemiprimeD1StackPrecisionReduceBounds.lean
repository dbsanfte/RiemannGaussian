/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPrecisionReduceExecution

/-! # Whole executed precision-reducer prefix bounds
The scalar, precision and both field frames are original physical input. Every
intermediate copy, marker, parser flag and actual return frame is counted.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPrecisionReduceBounds
open SemiprimeD1StackPrecisionReduce SemiprimeD1StackPrecisionReduceExecution SemiprimeBitArithmetic

/-- Actual runtime budget includes both binary field widths and the counter VALUE. -/
def timeBound (word precision : List Bool) : ℕ :=
  13*word.length+14*precision.length+12*bitValue precision+32

/-- No successful actual prefix extends beyond the proved real halt. -/
theorem prefix_fuel_le (word precision : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel
      (⟨some .start,none,none,store (input word precision) [] [] [] [] [] [] [],[]⟩:C.State Stack Label)=some out) :
    fuel ≤ timeBound word precision := by
  have hf : fuel ≤ totalTime word precision := by
    by_contra hn
    have he : fuel=totalTime word precision+(1+(fuel-(totalTime word precision+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hh : C.run program 1
      (⟨none,none,none,store [] [] [] [] [] [] (result word precision) [],[]⟩:C.State Stack Label)=none := rfl
    rw [hh,Option.bind_none] at hr
    cases hr
  exact hf.trans (totalTime_le word precision)

/-- The real data and return stack storage bound holds on EVERY executed prefix. -/
theorem prefix_cells (word precision : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel
      (⟨some .start,none,none,store (input word precision) [] [] [] [] [] [] [],[]⟩:C.State Stack Label)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      9*((input word precision).length+timeBound word precision) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (input word precision).length
    _ out (by intro k;cases k <;> simp [store]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 8*((input word precision).length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,((input word precision).length+fuel) :=
        Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by
        have hc : Fintype.card Stack=8 := by decide
        simp only [Finset.sum_const,Finset.card_univ,hc,smul_eq_mul]
  have ht:=prefix_fuel_le word precision fuel out hr
  omega

/-- Same storage bound for the ACTUAL single-input finite machine, including
its real return stack; no runtime fuel or workspace promise is assumed. -/
theorem machine_prefix_cells (word precision : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (Turing.initList machine (input word precision)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      9*((input word precision).length+timeBound word precision) := by
  let start : C.State Stack Label:=
    ⟨some .start,none,none,store (input word precision) [] [] [] [] [] [] [],[]⟩
  have he:=SemiprimeD1StackCalls.run_correct Stack.input Stack.result Label.start program fuel start
  change (C.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  have hs : (SemiprimeD1StackCalls.configuration start : machine.Cfg)=
      Turing.initList machine (input word precision) := start_configuration _
  have hh : (C.run program fuel start).map SemiprimeD1StackCalls.configuration=some cfg :=
    he.trans ((congrArg (fun initial : machine.Cfg=>
      (fun q : Option machine.Cfg=>q.bind machine.step)^[fuel] (some initial)) hs).trans hr)
  cases hc:C.run program fuel start with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells word precision fuel out hc

/-- Framing is physically part of the original input length. -/
theorem input_length (word precision : List Bool) :
    (input word precision).length=2*word.length+2*precision.length+2 := by
  simp only [input,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  omega

/-- Bounded control VALUES give a fixed polynomial bridge for this actual
program. This never replaces a precision-value bound by its bit length. -/
theorem resource_time (word precision : List Bool) (B : ℕ)
    (hw : word.length ≤ B) (hp : precision.length ≤ B) (hv : bitValue precision ≤ B) :
    timeBound word precision ≤ 39*(B+1) := by
  unfold timeBound
  omega

/-- Actual whole-prefix storage is linear in the same bounded resources. -/
theorem resource_cells (word precision : List Bool) (B : ℕ)
    (hw : word.length ≤ B) (hp : precision.length ≤ B) (hv : bitValue precision ≤ B) :
    9*((input word precision).length+timeBound word precision) ≤ 400*(B+1) := by
  have ht:=resource_time word precision B hw hp hv
  rw [input_length]
  omega

end RiemannGaussian.SemiprimeD1StackPrecisionReduceBounds
