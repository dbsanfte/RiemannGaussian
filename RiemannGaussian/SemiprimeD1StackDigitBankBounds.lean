/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDigitBankExecution
import RiemannGaussian.SemiprimeD1OriginalNativeWidths

/-! # Whole streaming digit-bank transition and storage bounds
All actual source and target prefixes include original N, cached width, unread
bits, reverse log, restored blocks, scratch and physical return frames.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDigitBankBounds
open SemiprimeD1StackDigitBank SemiprimeD1StackDigitBankExecution

/-- A successful prefix cannot pass the actual EOF-driven halt. -/
theorem prefix_fuel_le (word width : List Bool) (hw : width≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel
      (⟨some (SemiprimeD1StackDigitBank.control .start),none,none,store word [] width [] [] [],[]⟩:
        C.State Stack Label)=some out) : fuel ≤ timeBound word width := by
  obtain ⟨time,ht,hexe⟩:=source_run word width hw
  have hf : fuel ≤ time := by
    by_contra hn
    have he : fuel=time+(1+(fuel-(time+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hexe,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1
      (⟨none,none,none,store word [] width [] [] (result word width),[]⟩:C.State Stack Label)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht

/-- All actual source prefix cells are bounded without a supplied workspace cap. -/
theorem prefix_cells (word width : List Bool) (hw : width≠[]) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel
      (⟨some (SemiprimeD1StackDigitBank.control .start),none,none,store word [] width [] [] [],[]⟩:
        C.State Stack Label)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      12*(word.length+width.length+timeBound word width) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (word.length+width.length)
    _ out (by
      intro k
      rcases k with k|k
      · cases k <;> simp only [store,Sum.elim_inl,SemiprimeD1StackDigitBlock.store,List.length_nil] <;> omega
      · fin_cases k <;> simp [store]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 11*(word.length+width.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(word.length+width.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by
        have hc : Fintype.card Stack=11 := by decide
        simp only [Finset.sum_const,Finset.card_univ,hc,smul_eq_mul]
  have ht:=prefix_fuel_le word width hw fuel out hr
  omega

/-- Every actual compiled-machine prefix counts all data and return stacks. -/
theorem machine_prefix_cells (word width : List Bool) (hw : width≠[]) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (⟨some (SemiprimeD1StackDigitBank.control .start),none,none,store word [] width [] [] [],[]⟩:
          C.State Stack Label)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      12*(word.length+width.length+timeBound word width) := by
  let start : C.State Stack Label:=
    ⟨some (SemiprimeD1StackDigitBank.control .start),none,none,store word [] width [] [] [],[]⟩
  have he:=SemiprimeD1StackCalls.run_correct original output (SemiprimeD1StackDigitBank.control .start) program fuel start
  change (C.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  rw [hr] at he
  cases hc:C.run program fuel start with
  | none => rw [hc] at he;cases he
  | some out =>
    rw [hc] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    subst cfg
    exact prefix_cells word width hw fuel out hc

/-- The actual original radix marker cache is small in original input LENGTH. -/
theorem original_width (ell : ℕ) (hell : 0<ell) (width : List Bool)
    (hw : width.length=SemiprimeMacroParameters.radixBits ell) : width.length ≤ 64*ell :=
  hw ▸ (SemiprimeD1OriginalNativeWidths.public_dimensions ell hell).2.2.2.1

/-- Real whole-bank time is quadratic for the entire original public radix family. -/
theorem original_time (ell : ℕ) (hell : 0<ell) (word width : List Bool)
    (hn : word.length=ell) (hw : width.length=SemiprimeMacroParameters.radixBits ell) :
    timeBound word width ≤ 6500*(ell+1)^2 := by
  have hB:=original_width ell hell width hw
  unfold timeBound
  rw [hn]
  nlinarith [Nat.zero_le (ell^2)]

/-- The full original public digit-bank prefix footprint is likewise quadratic. -/
theorem original_space (ell : ℕ) (hell : 0<ell) (word width : List Bool)
    (hn : word.length=ell) (hw : width.length=SemiprimeMacroParameters.radixBits ell) :
    12*(word.length+width.length+timeBound word width) ≤ 80000*(ell+1)^2 := by
  have hB:=original_width ell hell width hw
  have ht:=original_time ell hell word width hn hw
  rw [hn]
  nlinarith [Nat.zero_le (ell^2)]

end RiemannGaussian.SemiprimeD1StackDigitBankBounds
