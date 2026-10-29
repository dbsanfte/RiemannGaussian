/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprExecution
/-! # Whole actual expression time and every-prefix storage
Only original modulus positivity/literal validity are assumed. All syntax
occurrences, actual calls/copies and every data/return cell are counted.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackExprBounds
open SemiprimeD1StackExpr SemiprimeD1StackExprExecution
open SemiprimeMacroEntryBitPrimitives (Expr execute Valid)
open SemiprimeD1StackExprCodec (size encode)
/-- Fixed per-node physical transition allowance, in binary modulus LENGTH. -/
def nodeBudget (p : ℕ) : ℕ := 20000*(3*p+3)^3
/-- Every actual operator and its frame/copy/parser overhead fit this allowance. -/
theorem nodeBudget_operation (p : ℕ) : 10000*(3*p+3)^3+21*p+26 ≤ nodeBudget p := by
  have h : 3*p+3 ≤ (3*p+3)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ 3*p+3) (by decide : 1 ≤ 3)
  unfold nodeBudget
  omega
/-- The same allowance pays literal parsing, fitting and finite call overhead. -/
theorem nodeBudget_literal (p : ℕ) : 10*p+30 ≤ nodeBudget p := by
  have h : 3*p+3 ≤ (3*p+3)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ 3*p+3) (by decide : 1 ≤ 3)
  unfold nodeBudget
  omega

/-- The COMPLETE actual recursive body is linear in encoded syntax size times
one fixed modulus-width polynomial. No intermediate width/clock oracle occurs. -/
theorem bodyTime_le (cached : List Bool) (hm : 0<SemiprimeBitArithmetic.bitValue cached)
    (expr : Expr) (hv : Valid cached expr) :
    bodyTime cached expr ≤ nodeBudget cached.length*size expr := by
  induction expr with
  | literal word=>
    have h := SemiprimeD1StackExprLiteralBounds.totalTime_le word cached
    have hB := nodeBudget_literal cached.length
    have h9 : 9 ≤ nodeBudget cached.length := by omega
    have hw := Nat.mul_le_mul_right word.length h9
    simp only [SemiprimeD1StackExprLiteralExecution.totalTime] at h
    change 2+(SemiprimeD1StackExprLiteralExecution.readyTime word cached+1) ≤
      nodeBudget cached.length*(2*word.length+3)
    ring_nf at hw ⊢
    omega
  | add a b ia ib=>
    have hA := ia hv.1
    have hB := ib hv.2
    have hOp := SemiprimeD1StackExprMeaning.arithmetic_time_le .add cached a b hm hv.1 hv.2
    have hExtra := nodeBudget_operation cached.length
    simp only [bodyTime,size]
    ring_nf at ⊢
    omega
  | sub a b ia ib=>
    have hA := ia hv.1
    have hB := ib hv.2
    have hOp := SemiprimeD1StackExprMeaning.arithmetic_time_le .sub cached a b hm hv.1 hv.2
    have hExtra := nodeBudget_operation cached.length
    simp only [bodyTime,size]
    ring_nf at ⊢
    omega
  | mul a b ia ib=>
    have hA := ia hv.1
    have hB := ib hv.2
    have hOp := SemiprimeD1StackExprMeaning.arithmetic_time_le .mul cached a b hm hv.1 hv.2
    have hExtra := nodeBudget_operation cached.length
    simp only [bodyTime,size]
    ring_nf at ⊢
    omega

/-- Uniform actual full-entry transition polynomial, before all source expressions. -/
def timeBound (syntaxSize modulus : ℕ) : ℕ := nodeBudget modulus*syntaxSize+3
/-- The real top call/return/halt are included, with no old/new clock equality. -/
theorem totalTime_le (cached : List Bool) (expr : Expr)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hv : Valid cached expr) :
    totalTime cached expr ≤ timeBound (size expr) cached.length :=
  Nat.add_le_add_right (bodyTime_le cached hm expr hv) 3
/-- Explicit fixed-degree closure in original encoded syntax and binary cache size. -/
theorem timeBound_le_fourth (syntaxSize modulus : ℕ) :
    timeBound syntaxSize modulus ≤ 600000*(syntaxSize+modulus+1)^4 := by
  let u:=syntaxSize+modulus+1
  have hu : 1 ≤ u := by omega
  have hp : modulus+1 ≤ u := by dsimp [u];omega
  have hs : syntaxSize ≤ u := by dsimp [u];omega
  have h := Nat.mul_le_mul (Nat.pow_le_pow_left hp 3) hs
  have h' := Nat.mul_le_mul_left 540000 h
  have he : nodeBudget modulus=540000*(modulus+1)^3 := by unfold nodeBudget;ring
  have hpos : 0<u^4 := by positivity
  unfold timeBound
  rw [he]
  rw [show u^3*u=u^4 by ring] at h'
  ring_nf at h' ⊢
  omega

/-- Actual source time certificate determined by the literal completed trace. -/
def sourceEvaluate (cached : List Bool) (expr : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hv : Valid cached expr) :
    StateTransition.EvalsToInTime (C.step program) (initial (encode expr tail) cached)
      (some (done cached expr tail)) (timeBound (size expr) cached.length) :=
  ⟨⟨_,source_run cached expr tail hm hv⟩,totalTime_le cached expr hm hv⟩
/-- Genuine fixed FinTM2 evaluation of prepared PHYSICAL syntax/cache inputs. -/
def machineEvaluate (cached : List Bool) (expr : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hv : Valid cached expr) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (encode expr tail) cached))
      (some (SemiprimeD1StackCalls.configuration (done cached expr tail)))
      (timeBound (size expr) cached.length) :=
  SemiprimeD1StackCalls.evalsCorrect Stack.code Stack.result Label.start program _ _ _
    (sourceEvaluate cached expr tail hm hv)
/-- The output is literally the original whole execute result, not its decoded value alone. -/
theorem output_original (cached : List Bool) (expr : Expr) (tail : List Bool) :
    (done cached expr tail).data .result=(execute cached expr).bits := rfl
/-- Unconsumed original physical code suffix is retained exactly. -/
theorem retained_suffix (cached : List Bool) (expr : Expr) (tail : List Bool) :
    (done cached expr tail).data .code=tail := rfl
/-- Raw binary modulus survives every recursive child and complete arithmetic call. -/
theorem retained_modulus (cached : List Bool) (expr : Expr) (tail : List Bool) :
    (done cached expr tail).data .modulus=cached := rfl
/-- Every other physical data role is empty at the actual completed halt. -/
theorem cleanup (cached : List Bool) (expr : Expr) (tail : List Bool) (k : Stack)
    (hk : k≠.code ∧ k≠.modulus ∧ k≠.result) : (done cached expr tail).data k=[] := by
  cases k <;> simp_all [done,finalData,bank]

/-- Every reached prefix lies before the proved actual whole evaluator halt. -/
theorem prefix_fuel_le (cached : List Bool) (expr : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hv : Valid cached expr)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial (encode expr tail) cached)=some out) : fuel ≤ totalTime cached expr := by
  by_contra hn
  have he : fuel=totalTime cached expr+(1+(fuel-(totalTime cached expr+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run cached expr tail hm hv,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at hr
  have hz : C.run program 1 (done cached expr tail)=none := rfl
  rw [hz,Option.bind_none] at hr
  cases hr

/-- EVERY actual data cell and real return-label cell, including all saved-left
frames, private arithmetic/parser work and retained code/cache, is bounded. -/
theorem prefix_cells (cached : List Bool) (expr : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hv : Valid cached expr)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial (encode expr tail) cached)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      100000000*(size expr+tail.length+cached.length+1)^4 := by
  let inv:=size expr+tail.length+cached.length
  have hdata : ∀k,((initial (encode expr tail) cached).data k).length ≤ inv := by
    intro k
    cases k <;> simp only [initial,input,bank,List.length_nil]
    · rw [SemiprimeD1StackExprCodec.encode_length];omega
    · dsimp [inv];omega
    all_goals dsimp [inv];omega
  have hd := SemiprimeD1StackReturnLink.run_data_bound program fuel inv _ out hdata hr
  have hf := SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 75*(inv+fuel) := by
    calc
      _  ≤  ∑_k : Stack,(inv+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht := ((prefix_fuel_le cached expr tail hm hv fuel out hr).trans (totalTime_le cached expr hm hv)).trans
    (timeBound_le_fourth (size expr) cached.length)
  have hpow : (size expr+cached.length+1)^4 ≤ (inv+1)^4 := Nat.pow_le_pow_left (by dsimp [inv];omega) 4
  have ht' := ht.trans (Nat.mul_le_mul_left 600000 hpow)
  have hbase : inv ≤ (inv+1)^4 := by
    have hh:=Nat.pow_le_pow_right (by omega : 1 ≤ inv+1) (by decide : 1 ≤ 4)
    simp only [pow_one] at hh
    omega
  change (∑k : Stack,(out.data k).length)+out.frames.length ≤ 100000000*(inv+1)^4
  omega

/-- Same all-prefix inventory bound for the genuine finite target machine. -/
theorem machine_prefix_cells (cached : List Bool) (expr : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hv : Valid cached expr)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (encode expr tail) cached)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      100000000*(size expr+tail.length+cached.length+1)^4 := by
  have he := SemiprimeD1StackCalls.run_correct Stack.code Stack.result Label.start program fuel
    (initial (encode expr tail) cached)
  have hh:=he.trans hr
  cases hc : C.run program fuel (initial (encode expr tail) cached) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells cached expr tail hm hv fuel out hc
end RiemannGaussian.SemiprimeD1StackExprBounds
