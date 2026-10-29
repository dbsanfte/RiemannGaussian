/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprPowerExecution

/-! # Actual power-syntax acquisition time and every-prefix storage
All repeated base bytes and both disposable counter copies are paid. The
source exponent is a physical marker word; acquiring it is caller work.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprPowerBounds
open SemiprimeD1StackExprPower SemiprimeD1StackExprPowerSpec SemiprimeD1StackExprPowerExecution

/-- Exact own instruction count, never transported from a native syntax report. -/
theorem totalTime_eq (baseCode cached : List Bool) :
    totalTime baseCode cached=cached.length*(5*baseCode.length+18)+16 := by
  unfold totalTime
  ring
/-- A uniform quadratic in actual encoded-base and physical exponent lengths. -/
theorem totalTime_le (baseCode cached : List Bool) :
    totalTime baseCode cached ≤ 40*(baseCode.length+cached.length+1)^2 := by
  rw [totalTime_eq]
  nlinarith [Nat.zero_le (baseCode.length^2),Nat.zero_le (cached.length^2)]

/-- Actual source syntax construction, not a supplied AST or encoded power. -/
def sourceBuild (baseCode cached tail : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial baseCode cached tail)
      (some (done baseCode cached tail)) (cached.length*(5*baseCode.length+18)+16) := by
  exact ⟨⟨totalTime baseCode cached,source_run baseCode cached tail⟩,(totalTime_eq baseCode cached).le⟩
/-- Genuine finite-machine power syntax acquisition with the same exact budget. -/
def machineBuild (baseCode cached tail : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial baseCode cached tail))
      (some (SemiprimeD1StackCalls.configuration (done baseCode cached tail)))
      (cached.length*(5*baseCode.length+18)+16) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) base output Label.start program
    _ _ _ (sourceBuild baseCode cached tail)

/-- Original source expression bytes, including every repeated subtree and the suffix. -/
theorem output_original (baseExpr : SemiprimeMacroEntryBitPrimitives.Expr) (cached tail : List Bool) :
    (done (SemiprimeD1StackExprCodec.encode baseExpr []) cached tail).data output=
      SemiprimeD1StackExprCodec.encode (SemiprimeMacroEntryBitPrimitives.powerExpr baseExpr cached.length) tail :=
  result_original baseExpr cached.length tail
/-- All physically copied base cells remain available for subsequent checker terms. -/
theorem retained_base (baseCode cached tail : List Bool) : (done baseCode cached tail).data base=baseCode := rfl
/-- The full original exponent-marker cache survives both actual consuming passes. -/
theorem retained_exponent (baseCode cached tail : List Bool) :
    (done baseCode cached tail).data exponent=cached := rfl

/-- Every successful source prefix ends by the actual completed construction halt. -/
theorem prefix_fuel_le (baseCode cached tail : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial baseCode cached tail)=some out) :
    fuel ≤ cached.length*(5*baseCode.length+18)+16 := by
  have hf : fuel ≤ totalTime baseCode cached := by
    by_contra hn
    have he : fuel=totalTime baseCode cached+(1+(fuel-(totalTime baseCode cached+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done baseCode cached tail)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans (totalTime_eq baseCode cached).le

/-- ALL five Boolean stacks and real return tags are counted at every prefix,
including the original encoded base, exponent cache, suffix and scratch copies. -/
theorem prefix_cells (baseCode cached tail : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial baseCode cached tail)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      500*(baseCode.length+cached.length+tail.length+1)^2 := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel
    (baseCode.length+cached.length+tail.length) _ out (by
      intro k
      fin_cases k <;> simp [initial,store] <;> omega) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 5*(baseCode.length+cached.length+tail.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(baseCode.length+cached.length+tail.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have ht: fuel ≤ 40*(baseCode.length+cached.length+1)^2 :=
    (prefix_fuel_le baseCode cached tail fuel out hr).trans
      (by rw [←totalTime_eq];exact totalTime_le baseCode cached)
  nlinarith [Nat.zero_le (baseCode.length^2),Nat.zero_le (cached.length^2),Nat.zero_le (tail.length^2)]

/-- Every actually reached target-machine prefix satisfies the SAME quadratic bound. -/
theorem machine_prefix_cells (baseCode cached tail : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial baseCode cached tail)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      500*(baseCode.length+cached.length+tail.length+1)^2 := by
  have he:=SemiprimeD1StackCalls.run_correct base output Label.start program fuel (initial baseCode cached tail)
  change (C.run program fuel (initial baseCode cached tail)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial baseCode cached tail))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial baseCode cached tail) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells baseCode cached tail fuel out hc

end RiemannGaussian.SemiprimeD1StackExprPowerBounds
