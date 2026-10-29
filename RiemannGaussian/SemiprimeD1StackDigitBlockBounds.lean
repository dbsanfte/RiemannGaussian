/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitBlockExecution

/-! # Whole streaming block prefix storage
High input and cached width remain live deliberately. Their cells and every
temporary/return cell are included in the actual executed prefix bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitBlockBounds
open SemiprimeD1StackDigitBlock SemiprimeD1StackDigitBlockExecution

/-- Successful source prefixes cannot continue beyond the genuine proved halt. -/
theorem prefix_fuel_le (word width : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel
      (⟨some .start,none,none,store word width [] [] [] [] [] [],[]⟩:C.State Stack Label)=some out) :
    fuel ≤ 8*width.length+5*word.length+11 := by
  have hf : fuel ≤ totalTime word width := by
    by_contra hn
    have he : fuel=totalTime word width+(1+(fuel-(totalTime word width+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1
      (⟨none,none,none,store (word.drop width.length) width [] [] [] [] [] (result word width),[]⟩:
        C.State Stack Label)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans (totalTime_le word width)

/-- Every visited source configuration counts the retained input/cache too. -/
theorem prefix_cells (word width : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel
      (⟨some .start,none,none,store word width [] [] [] [] [] [],[]⟩:C.State Stack Label)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      9*(6*word.length+9*width.length+11) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (word.length+width.length)
    _ out (by intro k;cases k <;> simp only [store,List.length_nil] <;> omega) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 8*(word.length+width.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(word.length+width.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by
        have hc : Fintype.card Stack=8 := by decide
        simp only [Finset.sum_const,Finset.card_univ,hc,smul_eq_mul]
  have ht:=prefix_fuel_le word width fuel out hr
  omega

/-- The same total storage bound holds on EVERY actual target-machine prefix. -/
theorem machine_prefix_cells (word width : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (⟨some .start,none,none,store word width [] [] [] [] [] [],[]⟩:C.State Stack Label)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      9*(6*word.length+9*width.length+11) := by
  let start : C.State Stack Label:=⟨some .start,none,none,store word width [] [] [] [] [] [],[]⟩
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
    exact prefix_cells word width fuel out hc

end RiemannGaussian.SemiprimeD1StackDigitBlockBounds
