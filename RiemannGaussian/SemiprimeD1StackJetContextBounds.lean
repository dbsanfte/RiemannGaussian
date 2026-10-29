/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetContextCorrectness
/-! # Original-derived context-cache time and all-prefix cell bounds
Binary precision conversion pays for the precision VALUE. It is used for bounded
control metadata, and does not license unary conversion of the factoring input.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackJetContextBounds
open SemiprimeD1StackJetContext SemiprimeD1StackJetContextExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeBitArithmetic (bitValue)

/-- Every acquired original record cell is included in the bound before cleanup. -/
theorem budget_le (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool) :
    SemiprimeD1StackJetContextCorrectness.budget axes precision ≤
      5*(vectorBits (axes.map unary)).length+100*(axes.length+1)*(axes.prod+1)+
        (4*axes.prod+2)*axes.length+11*precision.length+7*bitValue precision+17 := by
  have hr:=SemiprimeD1StackJetRouteRecords.original_tape_length axes hp
  rw [←SemiprimeD1StackJetRouteRecords.acquired_tape] at hr
  unfold SemiprimeD1StackJetContextCorrectness.budget
  omega

/-- Original control dimensions and actual physical input inventory. -/
def resource (axes : List ℕ) (precision : List Bool) : ℕ :=
  (vectorBits (axes.map unary)).length+axes.length+axes.prod+precision.length+bitValue precision+1

/-- Actual context acquisition is a fixed quadratic in original control resources. -/
theorem budget_polynomial (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool) :
    SemiprimeD1StackJetContextCorrectness.budget axes precision ≤ 1000*(resource axes precision+1)^2 := by
  have h:=budget_le axes hp precision
  have ha : (vectorBits (axes.map unary)).length ≤ resource axes precision := by unfold resource; omega
  have hl : axes.length ≤ resource axes precision := by unfold resource; omega
  have hr : axes.prod ≤ resource axes precision := by unfold resource; omega
  have hb : precision.length ≤ resource axes precision := by unfold resource; omega
  have hv : bitValue precision ≤ resource axes precision := by unfold resource; omega
  have hc : 100*(axes.length+1)*(axes.prod+1) ≤ 100*(resource axes precision+1)^2 := by
    calc
      _ ≤ 100*(resource axes precision+1)*(resource axes precision+1) := by gcongr
      _ = _ := by ring
  have hd : (4*axes.prod+2)*axes.length ≤ (4*resource axes precision+2)*resource axes precision := by gcongr
  nlinarith [Nat.zero_le ((resource axes precision)^2)]

/-- Original input, no rank/count/Fits/operation-budget supplier. -/
theorem source_run_polynomial (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool) :
    ∃ m ≤ 1000*(resource axes precision+1)^2,
      SemiprimeD1StackCalls.run program m (initial (vectorBits (axes.map unary)) precision)=
        some (⟨none,none,none,SemiprimeD1StackJetContextCorrectness.finalData axes precision,[]⟩:
          SemiprimeD1StackCalls.State Stack Label) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackJetContextCorrectness.source_run axes hp precision
  exact ⟨m,hm.trans (budget_polynomial axes hp precision),hr⟩

/-- Genuine actual finite-stack original context-cache acquisition certificate. -/
noncomputable def machineAcquirePolynomial (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (vectorBits (axes.map unary)) precision))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,SemiprimeD1StackJetContextCorrectness.finalData axes precision,[]⟩:
          SemiprimeD1StackCalls.State Stack Label))) (1000*(resource axes precision+1)^2) := by
  let h:=source_run_polynomial axes hp precision
  let m:=Classical.choose h
  have hm:=Classical.choose_spec h
  apply SemiprimeD1StackCalls.evalsCorrect axesCache rankCache Label.start program
  exact ⟨⟨m,hm.2⟩,hm.1⟩

/-- No actual successful original prefix continues beyond the proved halt. -/
theorem prefix_fuel_le (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool)
    (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial (vectorBits (axes.map unary)) precision)=some out) :
    fuel ≤ 1000*(resource axes precision+1)^2 := by
  obtain ⟨m,hm,hstop⟩:=source_run_polynomial axes hp precision
  by_contra hn
  have he : fuel=m+(1+(fuel-(m+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,hstop,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hh : SemiprimeD1StackCalls.run program 1
      (⟨none,none,none,SemiprimeD1StackJetContextCorrectness.finalData axes precision,[]⟩:
        SemiprimeD1StackCalls.State Stack Label)=none := rfl
  rw [hh,Option.bind_none] at hr
  cases hr

/-- Every original physical input register is bounded without an input-height oracle. -/
theorem initial_length (axes : List ℕ) (precision : List Bool) (k : Stack) :
    ((initial (vectorBits (axes.map unary)) precision).data k).length ≤ resource axes precision := by
  rcases k with k|k
  · simp [initial,bank]
  · rcases k with k|k
    · simp [initial,bank]
    · fin_cases k <;> simp [initial,bank,cached,resource] <;> omega

/-- Every successful source prefix has polynomial data and real-return storage. -/
theorem prefix_cells (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool)
    (fuel : ℕ) (out : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial (vectorBits (axes.map unary)) precision)=some out) :
    (∑s:Stack,(out.data s).length)+out.frames.length ≤
      16*(resource axes precision+1000*(resource axes precision+1)^2+1) := by
  have hf:=prefix_fuel_le axes hp precision fuel out hr
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (resource axes precision) _ out
    (initial_length axes precision) hr
  have hframes:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hframes
  have hs : (∑s:Stack,(out.data s).length) ≤ 15*(resource axes precision+fuel) := by
    calc
      _ ≤ ∑_s:Stack,(resource axes precision+fuel) := Finset.sum_le_sum (fun s _=>hd s)
      _ = 15*(resource axes precision+fuel) := by
        have hc : Fintype.card Stack=15 := by decide
        simp [hc]
  omega

/-- The same original-resource cap bounds every actual compiled-machine prefix. -/
theorem machine_prefix_cells (axes : List ℕ) (hp : ∀q∈axes,0<q) (precision : List Bool)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (vectorBits (axes.map unary)) precision)))=some cfg) :
    (∑s:Stack,(cfg.stk (some s)).length)+(cfg.stk none).length ≤
      16*(resource axes precision+1000*(resource axes precision+1)^2+1) := by
  let start:=initial (vectorBits (axes.map unary)) precision
  have he:=SemiprimeD1StackCalls.run_correct axesCache rankCache Label.start program fuel start
  change (SemiprimeD1StackCalls.run program fuel start).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration start)) at he
  cases hc:SemiprimeD1StackCalls.run program fuel start with
  | none => rw [hc,hr] at he; cases he
  | some out =>
    rw [hc,hr] at he
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj he
    rw [←hcfg]
    exact prefix_cells axes hp precision fuel out hc

end RiemannGaussian.SemiprimeD1StackJetContextBounds
