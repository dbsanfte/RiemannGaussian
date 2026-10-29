/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerEqualityKey
/-! # Actual transition and all-prefix cell bounds for endpoint sentinel-copy -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1StackOwnerEqualityKeyBounds
open SemiprimeD1StackOwnerEqualityKey
/-- The acquired-record stage has one actual input tape and no preloaded output. -/
theorem initial_eq (record:List Bool) :
    Turing.initList machine record=SemiprimeD1StackCalls.configuration (initial record) := by
  have hs:initial record=SemiprimeD1StackCalls.initial (0:Stack) (.inl 0:Label) record := by
    unfold initial SemiprimeD1StackCalls.initial
    congr 1
    funext k;fin_cases k <;> rfl
  rw [hs]
  exact (SemiprimeD1StackCalls.initial_correct (0:Stack) 1 (.inl 0:Label) program record).symm
/-- No successful prefix can execute past the actual final halt. -/
theorem prefix_fuel (record:List Bool) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial record)=some out) : fuel≤5*record.length+6 := by
  by_contra hn
  have h:fuel=(5*record.length+6)+(1+(fuel-(5*record.length+7))):=by omega
  rw [h,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hz:C.run program 1 (done record)=none:=rfl
  rw [hz,Option.bind_none] at hr
  cases hr
/-- All three Boolean data stacks and actual return frames at EVERY prefix. -/
theorem prefix_cells (record:List Bool) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial record)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤23*record.length+24 := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel record.length _ out (by
    intro k;fin_cases k <;> simp [initial,SemiprimeD1StackCopy.payload]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤3*(record.length+fuel):=by
    calc
      _≤∑_k:Stack,(record.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp
  have ht:=prefix_fuel record fuel out hr
  omega
/-- Actual fixed finite-machine execution certificate, not a retained clock. -/
noncomputable def keyInTime (record:List Bool) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine record)
      (some (SemiprimeD1StackCalls.configuration (done record))) (5*record.length+6) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect (0:Stack) 1 (.inl 0:Label) program
  exact ⟨⟨5*record.length+6,source_run record⟩,le_rfl⟩
end RiemannGaussian.SemiprimeD1StackOwnerEqualityKeyBounds
