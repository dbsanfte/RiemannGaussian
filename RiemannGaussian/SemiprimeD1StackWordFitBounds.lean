/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordFitExecution
import RiemannGaussian.SemiprimeMacroEntryBitPrimitives

/-! # Actual literal-word fitting time, space and checker interface
Input and template are physical caller operands. The machine never executes a
decoded-value test, native fitting routine, supplied clock or prepared result.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordFitBounds
open SemiprimeD1StackWordFit SemiprimeD1StackWordFitExecution

/-- Complete executed time, including physical erasure of excess input. -/
theorem totalTime_le (word cached : List Bool) :
    totalTime word cached ≤ word.length+10*cached.length+8 := by
  have hd : (word.drop cached.length).length ≤ word.length := by
    simp only [List.length_drop]
    exact Nat.sub_le _ _
  unfold totalTime
  omega

/-- Source trace certificate for the actual input and cached width word. -/
def sourceFit (word cached : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial word cached)
      (some (done word cached)) (word.length+10*cached.length+8) :=
  ⟨⟨_,source_run word cached⟩,totalTime_le word cached⟩

/-- Actual finite-machine fitting, without changing the source transition count. -/
def machineFit (word cached : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial word cached))
      (some (SemiprimeD1StackCalls.configuration (done word cached)))
      (word.length+10*cached.length+8) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) operand output Label.start program
    _ _ _ (sourceFit word cached)

/-- The original public interpreter's literal case has EXACTLY these output bytes. -/
theorem literal_bytes (word cached : List Bool) :
    result word cached=(SemiprimeMacroEntryBitPrimitives.execute cached (.literal word)).bits := rfl

/-- The physical binary width template survives the complete trace. -/
theorem retained_template (word cached : List Bool) : (done word cached).data template=cached := rfl
/-- The actual output designation contains exactly the original fitting bytes. -/
theorem output_result (word cached : List Bool) : (done word cached).data output=result word cached := rfl

/-- Every value that fits the actual template width is preserved numerically. -/
theorem result_value (word cached : List Bool)
    (h : SemiprimeBitArithmetic.bitValue word < 2^cached.length) :
    SemiprimeBitArithmetic.bitValue (result word cached)=SemiprimeBitArithmetic.bitValue word :=
  SemiprimeBitDivision.fitBits_value h

/-- A successful prefix cannot continue beyond the actual proved halt. -/
theorem prefix_fuel_le (word cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial word cached)=some out) :
    fuel ≤ word.length+10*cached.length+8 := by
  have hf : fuel ≤ totalTime word cached := by
    by_contra hn
    have he : fuel=totalTime word cached+(1+(fuel-(totalTime word cached+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done word cached)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans (totalTime_le word cached)

/-- Every actual prefix counts all five Boolean data stacks and the real
finite-label return stack, including all template copies and padding. -/
theorem prefix_cells (word cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial word cached)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 100*(word.length+cached.length+1) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (word.length+cached.length) _ out (by
    intro k
    fin_cases k <;> simp [initial,store]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 5*(word.length+cached.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(word.length+cached.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have ht:=prefix_fuel_le word cached fuel out hr
  omega

/-- The same linear bound holds at every prefix of the compiled finite machine. -/
theorem machine_prefix_cells (word cached : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial word cached)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      100*(word.length+cached.length+1) := by
  have he:=SemiprimeD1StackCalls.run_correct operand output Label.start program fuel (initial word cached)
  change (C.run program fuel (initial word cached)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial word cached))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial word cached) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells word cached fuel out hc

end RiemannGaussian.SemiprimeD1StackWordFitBounds
