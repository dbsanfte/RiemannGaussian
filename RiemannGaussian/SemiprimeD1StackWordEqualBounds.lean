/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordEqualExecution

/-! # Linear binary-value comparison and original public equality semantics
This physical bit comparison directly handles arbitrary high-zero padding;
it does not construct either numeric value or call two subtraction routines.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordEqualBounds
open SemiprimeD1StackWordEqual SemiprimeD1StackWordEqualExecution SemiprimeD1StackBytecode
open SemiprimeD1StackAdder (Stack store)
open SemiprimeBitArithmetic

/-- Actual source certificate; expected numeric equality appears only in its specification. -/
def sourceEqual (left right : List Bool) :
    StateTransition.EvalsToInTime (step code) (state (some .loop) none left right [])
      (some (state none none [] [] [decide (bitValue left=bitValue right)]))
      (2*(left.length+right.length)+8) :=
  ⟨⟨_,source_run left right none⟩,executionTime_le left right⟩
/-- Actual four-stack finite-machine equality with the SAME linear transition bound. -/
def machineEqual (left right : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackBytecode.configuration (state (some .loop) none left right []))
      (some (SemiprimeD1StackBytecode.configuration
        (state none none [] [] [decide (bitValue left=bitValue right)])))
      (2*(left.length+right.length)+8) :=
  SemiprimeD1StackBytecode.evalsCorrect Stack.left Stack.output Label.loop code _ _ _ (sourceEqual left right)

/-- Exact Boolean result of the frozen public equality checker, now acquired
by direct physical digit comparisons instead of two subtractor calls. -/
theorem original_answer (left right : List Bool) :
    decide (bitValue left=bitValue right)=(SemiprimeMacroEntryBitPrimitives.equalBits left right).accepted := by
  by_cases h : bitValue left=bitValue right
  · have ho:=(SemiprimeMacroEntryBitPrimitives.equalBits_correct left right).mpr h
    simp only [h,decide_true,ho]
  · have ho : (SemiprimeMacroEntryBitPrimitives.equalBits left right).accepted=false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact h ((SemiprimeMacroEntryBitPrimitives.equalBits_correct left right).mp ht)
    simp only [h,decide_false,ho]

/-- Every successful prefix is bounded by the actually proved halt. -/
theorem prefix_fuel_le (left right : List Bool) (fuel : ℕ) (out : State Stack Label)
    (hr : run code fuel (state (some .loop) none left right [])=some out) :
    fuel ≤ 2*(left.length+right.length)+8 := by
  have ht:=SemiprimeD1StackBytecodeBounds.fuel_le_halt code
    (state (some .loop) none left right [])
    (state none none [] [] [decide (bitValue left=bitValue right)]) out
    (executionTime left right) fuel (source_run left right none) rfl hr
  exact ht.trans (executionTime_le left right)

/-- Every real visited Boolean cell is counted, including both mismatch tails. -/
theorem prefix_cells (left right : List Bool) (fuel : ℕ) (out : State Stack Label)
    (hr : run code fuel (state (some .loop) none left right [])=some out) :
    SemiprimeD1StackBytecodeBounds.cells out ≤ 10*(left.length+right.length)+40 := by
  have ht:=prefix_fuel_le left right fuel out hr
  have hc:=SemiprimeD1StackBytecodeBounds.run_cells code fuel _ out hr
  have hi : SemiprimeD1StackBytecodeBounds.cells (state (some .loop) none left right [])=
      left.length+right.length := by
    have hu : (Finset.univ : Finset Stack)={.left,.right,.scratch,.output} := by decide
    simp [SemiprimeD1StackBytecodeBounds.cells,hu,state,store]
  have hk : Fintype.card Stack=4 := by decide
  rw [hi,hk] at hc
  omega

/-- The same linear storage cap holds at every actually reached compiled-machine prefix. -/
theorem machine_prefix_cells (left right : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackBytecode.configuration (state (some .loop) none left right [])))=some cfg) :
    (∑k : Stack,(cfg.stk k).length) ≤ 10*(left.length+right.length)+40 := by
  have he:=SemiprimeD1StackBytecode.run_correct Stack.left Stack.output Label.loop code fuel
    (state (some .loop) none left right [])
  change (run code fuel (state (some .loop) none left right [])).map SemiprimeD1StackBytecode.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackBytecode.configuration (state (some .loop) none left right []))) at he
  have hh:=he.trans hr
  cases hc:run code fuel (state (some .loop) none left right []) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackBytecode.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells left right fuel out hc

end RiemannGaussian.SemiprimeD1StackWordEqualBounds
