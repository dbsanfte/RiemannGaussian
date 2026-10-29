/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprEqualityExecution
/-! # Actual scalar equality time and complete prefix inventory
Both original expression executions, result copies/drains and the real numeric
comparator are paid. Inputs are prepared physical syntax and binary modulus.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackExprEqualityBounds
open SemiprimeD1StackExprEquality SemiprimeD1StackExprEqualityExecution
open SemiprimeMacroEntryBitPrimitives (Expr execute Valid residueEqualityBits)
open SemiprimeD1StackExprCodec (size encode)
/-- One fixed polynomial before both original expressions and the modulus. -/
def timeBound (leftSize rightSize modulusSize : ℕ) : ℕ :=
  SemiprimeD1StackExprBounds.nodeBudget modulusSize*(leftSize+rightSize+1)
/-- Actual intermediate result widths are DERIVED from original validity. -/
theorem totalTime_le (cached : List Bool) (left right : Expr)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hl : Valid cached left) (hr : Valid cached right) :
    totalTime cached left right ≤ timeBound (size left) (size right) cached.length := by
  have hL := SemiprimeD1StackExprBounds.totalTime_le cached left hm hl
  have hR := SemiprimeD1StackExprBounds.totalTime_le cached right hm hr
  have hEq := SemiprimeD1StackWordEqualExecution.executionTime_le (execute cached left).bits (execute cached right).bits
  have hwL := (SemiprimeMacroEntryBitPrimitives.execute_bounds cached hm left hl).1
  have hwR := (SemiprimeMacroEntryBitPrimitives.execute_bounds cached hm right hr).1
  have hB := SemiprimeD1StackExprBounds.nodeBudget_literal cached.length
  rw [hwL,hwR] at hEq
  unfold totalTime timeBound
  rw [hwL]
  unfold SemiprimeD1StackExprBounds.timeBound at hL hR
  ring_nf at hL hR ⊢
  omega
/-- Explicit fixed fourth-degree transition bound, without a callback clock. -/
theorem timeBound_le_fourth (leftSize rightSize modulusSize : ℕ) :
    timeBound leftSize rightSize modulusSize ≤ 600000*(leftSize+rightSize+modulusSize+2)^4 := by
  let u:=leftSize+rightSize+modulusSize+2
  have hp : modulusSize+1 ≤ u := by dsimp [u];omega
  have hs : leftSize+rightSize+1 ≤ u := by dsimp [u];omega
  have h := Nat.mul_le_mul (Nat.pow_le_pow_left hp 3) hs
  have h' := Nat.mul_le_mul_left 540000 h
  have he : SemiprimeD1StackExprBounds.nodeBudget modulusSize=540000*(modulusSize+1)^3 := by
    unfold SemiprimeD1StackExprBounds.nodeBudget;ring
  unfold timeBound
  rw [he]
  rw [show u^3*u=u^4 by ring] at h'
  ring_nf at h' ⊢
  omega
/-- Actual source trace certificate, not a reinterpretation of an old clock. -/
def sourceEqual (cached : List Bool) (left right : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hl : Valid cached left) (hr : Valid cached right) :
    StateTransition.EvalsToInTime (C.step program) (initial (encode left (encode right tail)) cached)
      (some (done cached left right tail)) (timeBound (size left) (size right) cached.length) :=
  ⟨⟨_,source_run cached left right tail hm hl hr⟩,totalTime_le cached left right hm hl hr⟩
/-- Genuine fixed finite-stack machine with actual real-call/return semantics. -/
def machineEqual (cached : List Bool) (left right : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hl : Valid cached left) (hr : Valid cached right) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial (encode left (encode right tail)) cached))
      (some (SemiprimeD1StackCalls.configuration (done cached left right tail)))
      (timeBound (size left) (size right) cached.length) :=
  SemiprimeD1StackCalls.evalsCorrect inputCode output Label.start program _ _ _
    (sourceEqual cached left right tail hm hl hr)
/-- Literal accepted output is the original residue-equality answer. -/
theorem output_original (cached : List Bool) (left right : Expr) (tail : List Bool) :
    (done cached left right tail).data output=[(residueEqualityBits cached left right).accepted] := rfl
/-- Unconsumed syntax suffix remains byte for byte. -/
theorem retained_suffix (cached : List Bool) (left right : Expr) (tail : List Bool) :
    (done cached left right tail).data inputCode=tail := rfl
/-- Raw binary modulus survives BOTH actual complete evaluations. -/
theorem retained_modulus (cached : List Bool) (left right : Expr) (tail : List Bool) :
    (done cached left right tail).data modulus=cached := rfl
/-- All other physical data roles are actually empty at halt. -/
theorem cleanup (cached : List Bool) (left right : Expr) (tail : List Bool) (k : Stack)
    (hk : k≠inputCode ∧ k≠modulus ∧ k≠output) : (done cached left right tail).data k=[] := by
  rcases k with k|k
  · cases k <;> simp_all [done,finalData,store,E.input,SemiprimeD1StackExpr.bank,inputCode,modulus,output]
  · rcases k with k|k
    · cases k <;> simp_all [done,finalData,store,Q.store,inputCode,modulus,output]
    · cases k;rfl
/-- Every reached source state precedes the actual proved complete halt. -/
theorem prefix_fuel_le (cached : List Bool) (left right : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hl : Valid cached left) (hr : Valid cached right)
    (fuel : ℕ) (out : C.State Stack Label)
    (h : C.run program fuel (initial (encode left (encode right tail)) cached)=some out) :
    fuel ≤ totalTime cached left right := by
  by_contra hn
  have he : fuel=totalTime cached left right+(1+(fuel-(totalTime cached left right+1))) := by omega
  rw [he,SemiprimeD1StackReturnLink.run_add,source_run cached left right tail hm hl hr,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add] at h
  have hz : C.run program 1 (done cached left right tail)=none := rfl
  rw [hz,Option.bind_none] at h
  cases h
/-- All EIGHTY Boolean data stacks and the actual return-label stack, at EVERY
reached prefix, including repeated code, saved values and comparator work. -/
theorem prefix_cells (cached : List Bool) (left right : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hl : Valid cached left) (hr : Valid cached right)
    (fuel : ℕ) (out : C.State Stack Label)
    (h : C.run program fuel (initial (encode left (encode right tail)) cached)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      100000000*(size left+size right+tail.length+cached.length+2)^4 := by
  let inv:=size left+size right+tail.length+cached.length
  have hdata : ∀k,((initial (encode left (encode right tail)) cached).data k).length ≤ inv := by
    intro k
    rcases k with k|k
    · cases k <;> simp only [initial,input,store,E.input,SemiprimeD1StackExpr.bank,List.length_nil,Sum.elim_inl]
      · rw [SemiprimeD1StackExprCodec.encode_length,SemiprimeD1StackExprCodec.encode_length];omega
      all_goals dsimp [inv];omega
    · rcases k with k|k
      · cases k <;> change 0 ≤ inv <;> omega
      · cases k;change 0 ≤ inv;omega
  have hd := SemiprimeD1StackReturnLink.run_data_bound program fuel inv _ out hdata h
  have hf := SemiprimeD1StackCalls.run_frame_bound program fuel _ out h
  change out.frames.length ≤ 0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length) ≤ 80*(inv+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(inv+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht := ((prefix_fuel_le cached left right tail hm hl hr fuel out h).trans
    (totalTime_le cached left right hm hl hr)).trans (timeBound_le_fourth (size left) (size right) cached.length)
  have hpow : (size left+size right+cached.length+2)^4 ≤ (inv+2)^4 :=
    Nat.pow_le_pow_left (by dsimp [inv];omega) 4
  have ht' := ht.trans (Nat.mul_le_mul_left 600000 hpow)
  have hbase : inv ≤ (inv+2)^4 := by
    have hh:=Nat.pow_le_pow_right (by omega : 1 ≤ inv+2) (by decide : 1 ≤ 4)
    simp only [pow_one] at hh
    omega
  change (∑k : Stack,(out.data k).length)+out.frames.length ≤ 100000000*(inv+2)^4
  omega
/-- The identical all-prefix bound for the genuine finite target machine. -/
theorem machine_prefix_cells (cached : List Bool) (left right : Expr) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached) (hl : Valid cached left) (hr : Valid cached right)
    (fuel : ℕ) (cfg : machine.Cfg)
    (h : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial (encode left (encode right tail)) cached)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      100000000*(size left+size right+tail.length+cached.length+2)^4 := by
  have he := SemiprimeD1StackCalls.run_correct inputCode output Label.start program fuel
    (initial (encode left (encode right tail)) cached)
  have hh:=he.trans h
  cases hc : C.run program fuel (initial (encode left (encode right tail)) cached) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells cached left right tail hm hl hr fuel out hc
end RiemannGaussian.SemiprimeD1StackExprEqualityBounds
