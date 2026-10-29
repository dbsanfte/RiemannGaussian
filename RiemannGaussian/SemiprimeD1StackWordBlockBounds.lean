/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordBlockExecution

/-! # Exact word-block cost and all-prefix physical storage
One physical width copy, one actual read/pad per template cell and a real
reversal suffice. Every unread original assignment bit remains on its tape.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWordBlockBounds
open SemiprimeD1StackWordBlock SemiprimeD1StackWordBlockExecution

/-- Actual exact elapsed count; no unread assignment suffix is scanned. -/
theorem totalTime_eq (cached : List Bool) : totalTime cached=10*cached.length+7 := by
  unfold totalTime
  ring
/-- Complete actual source block extraction, with no supplied width or result. -/
def sourceBlock (word cached : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial word cached) (some (done word cached))
      (10*cached.length+7) :=
  ⟨⟨totalTime cached,source_run word cached⟩,(totalTime_eq cached).le⟩
/-- Genuine fixed finite-stack bit machine with the same exact transition count. -/
def machineBlock (word cached : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial word cached))
      (some (SemiprimeD1StackCalls.configuration (done word cached))) (10*cached.length+7) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) operand output
    RiemannGaussian.SemiprimeD1StackWordFit.Label.start program _ _ _ (sourceBlock word cached)
/-- Every actual block is exactly the original literal padded-prefix bytes. -/
theorem output_original (word cached : List Bool) :
    (done word cached).data output=(SemiprimeBitDivision.fitBits word cached).bits := rfl
/-- Full original assignment input gives the exact unchanged first physical word. -/
theorem output_take (word cached : List Bool) (hlen : cached.length ≤ word.length) :
    (done word cached).data output=word.take cached.length := result_take word cached hlen
/-- Every subsequent original assignment cell is retained byte for byte. -/
theorem retained_suffix (word cached : List Bool) :
    (done word cached).data operand=word.drop cached.length := rfl
/-- The physical binary width template survives the actual counter copy. -/
theorem retained_template (word cached : List Bool) : (done word cached).data template=cached := rfl

/-- No successful source prefix can exceed this actual completed halt. -/
theorem prefix_fuel_le (word cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial word cached)=some out) : fuel ≤ 10*cached.length+7 := by
  have hf : fuel ≤ totalTime cached := by
    by_contra h
    have hh : fuel=totalTime cached+(1+(fuel-(totalTime cached+1))) := by omega
    rw [hh,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done word cached)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans (totalTime_eq cached).le
/-- ALL five Boolean data stacks and real return tags at every physical prefix,
including retained source suffix and width cache, copied counter and scratch. -/
theorem prefix_cells (word cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial word cached)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 100*(word.length+cached.length+1) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (word.length+cached.length) _ out
    (by intro k;fin_cases k <;> simp [initial,store]) hr
  have ht:=prefix_fuel_le word cached fuel out hr
  have hframe:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hframe
  have hsum : (∑k : Stack,(out.data k).length) ≤ 5*(word.length+cached.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(word.length+cached.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega
/-- The same bound on every actual finite-machine prefix, with no ignored cells. -/
theorem machine_prefix_cells (word cached : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial word cached)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤ 100*(word.length+cached.length+1) := by
  have he:=SemiprimeD1StackCalls.run_correct (K:=Stack) (L:=Label) operand output
    RiemannGaussian.SemiprimeD1StackWordFit.Label.start program fuel (initial word cached)
  change (C.run program fuel (initial word cached)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial word cached))) at he
  have hh:=he.trans hr
  cases hrun:C.run program fuel (initial word cached) with
  | none => rw [hrun] at hh;cases hh
  | some out =>
    rw [hrun] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells word cached fuel out hrun

end RiemannGaussian.SemiprimeD1StackWordBlockBounds
