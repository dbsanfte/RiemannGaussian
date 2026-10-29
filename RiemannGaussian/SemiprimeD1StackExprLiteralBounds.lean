/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprLiteralExecution

/-! # Literal expression actual machine cost and public semantics
All parsed/fitted bits come from the physical syntax and cached template. The
suffix is retained and its storage counted; acquiring syntax/cache is caller work.
-/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprLiteralBounds
open SemiprimeD1StackExprLiteral SemiprimeD1StackExprLiteralExecution

/-- Every constructor read, actual parser/fitter call and cleanup is paid. -/
theorem totalTime_le (word cached : List Bool) :
    totalTime word cached ≤ 9*word.length+10*cached.length+20 := by
  have hf:=SemiprimeD1StackWordFitBounds.totalTime_le word cached
  unfold totalTime readyTime
  omega

/-- Exact source certificate for the literal encoded in the physical syntax. -/
def sourceLiteral (word tail cached : List Bool) :
    StateTransition.EvalsToInTime (C.step program)
      (initial (SemiprimeD1StackExprCodec.encode (.literal word) tail) cached)
      (some (done word tail cached)) (9*word.length+10*cached.length+20) :=
  ⟨⟨_,source_run word tail cached⟩,totalTime_le word cached⟩

/-- Genuine fixed finite-machine literal execution; no AST/value/width answer input. -/
def machineLiteral (word tail cached : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial (SemiprimeD1StackExprCodec.encode (.literal word) tail) cached))
      (some (SemiprimeD1StackCalls.configuration (done word tail cached)))
      (9*word.length+10*cached.length+20) :=
  SemiprimeD1StackCalls.evalsCorrect inputCode output (ctl .start) program
    _ _ _ (sourceLiteral word tail cached)

/-- Exact original public arithmetic interpreter literal bytes. -/
theorem literal_original (word tail cached : List Bool) :
    (done word tail cached).data output=
      (SemiprimeMacroEntryBitPrimitives.execute cached (.literal word)).bits := rfl
/-- The physically unconsumed expression suffix remains available for recursive parsing. -/
theorem retained_suffix (word tail cached : List Bool) :
    (done word tail cached).data inputCode=tail := rfl
/-- The binary modulus/template cache survives the actual complete literal trace. -/
theorem retained_template (word tail cached : List Bool) :
    (done word tail cached).data (.inl Fit.template)=cached := rfl
/-- The result has the SAME physical modulus width used by the original checker. -/
theorem output_length (word tail cached : List Bool) :
    ((done word tail cached).data output).length=cached.length :=
  SemiprimeD1StackWordFitExecution.result_length word cached

/-- Successful source prefixes cannot pass the real complete halt. -/
theorem prefix_fuel_le (word tail cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel
      (initial (SemiprimeD1StackExprCodec.encode (.literal word) tail) cached)=some out) :
    fuel ≤ 9*word.length+10*cached.length+20 := by
  have hf : fuel ≤ totalTime word cached := by
    by_contra hn
    have he : fuel=totalTime word cached+(1+(fuel-(totalTime word cached+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,source_run,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done word tail cached)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans (totalTime_le word cached)

/-- ALL seven Boolean data stacks, the complete retained suffix and every real
return tag are included at every actual prefix. No live-inventory premise. -/
theorem prefix_cells (word tail cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel
      (initial (SemiprimeD1StackExprCodec.encode (.literal word) tail) cached)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤ 200*(word.length+tail.length+cached.length+1) := by
  let code:=SemiprimeD1StackExprCodec.encode (.literal word) tail
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (code.length+cached.length) _ out (by
    intro k
    rcases k with k|k
    · fin_cases k <;> simp [initial,input,store,Fit.store,code]
    · rcases k with k|k <;> cases k <;> simp [initial,input,store,code]) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 7*(code.length+cached.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(code.length+cached.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by
        have hc : Fintype.card Stack=7 := by decide
        simp only [Finset.sum_const,Finset.card_univ,hc,smul_eq_mul]
  have hcode : code.length=2*word.length+3+tail.length := by
    exact SemiprimeD1StackExprCodec.encode_length (.literal word) tail
  have ht:=prefix_fuel_le word tail cached fuel out hr
  omega

/-- Every reached compiled-machine prefix has the SAME complete linear storage cap. -/
theorem machine_prefix_cells (word tail cached : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial (SemiprimeD1StackExprCodec.encode (.literal word) tail) cached)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      200*(word.length+tail.length+cached.length+1) := by
  have he:=SemiprimeD1StackCalls.run_correct inputCode output (ctl .start) program fuel
    (initial (SemiprimeD1StackExprCodec.encode (.literal word) tail) cached)
  change (C.run program fuel (initial (SemiprimeD1StackExprCodec.encode (.literal word) tail) cached)).map
      SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration
        (initial (SemiprimeD1StackExprCodec.encode (.literal word) tail) cached))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial (SemiprimeD1StackExprCodec.encode (.literal word) tail) cached) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells word tail cached fuel out hc

end RiemannGaussian.SemiprimeD1StackExprLiteralBounds
