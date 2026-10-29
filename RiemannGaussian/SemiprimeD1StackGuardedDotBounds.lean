/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackGuardedDotExecution
/-! # Closed guarded dot time and complete all-prefix inventory
Canonicality and whole-source validity are derived only after the actual true
verdict. The rejected path pays the guard and preserves every original input.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackGuardedDotBounds
open SemiprimeD1StackGuardedDotEvaluate SemiprimeD1StackGuardedDotExecution
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeMacroEntryBitPrimitives (Expr Valid)
/-- Fixed-degree actual transition bound, before all prepared physical inputs. -/
def runBound (c : D.Cache) (cached : List Bool) : ℕ :=
  30000000000*(SemiprimeD1StackDotEvaluateBounds.inputSize c cached+1)^8
/-- Uniform actual guard plus CONDITIONAL real DotEvaluate bound. There is no
canonical-vector/Valid-whole/count-result/source-size/clock advice premise. -/
theorem timeBound_le (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr) :
    timeBound c cached baseExpr words stride frequency n ≤ runBound c cached := by
  let S:=SemiprimeD1StackDotEvaluateBounds.inputSize c cached
  have hi : (vectorBits words).length+cached.length+1 ≤ S+1 := by
    dsimp [S,SemiprimeD1StackDotEvaluateBounds.inputSize,SemiprimeD1StackExprDotBounds.inputSize]
    rw [hc]
    omega
  have hG:=SemiprimeD1StackVectorCanonicalBounds.timeBound_le words cached
  have h2 : ((vectorBits words).length+cached.length+1)^2 ≤ (S+1)^2 := Nat.pow_le_pow_left hi 2
  have h28 : (S+1)^2 ≤ (S+1)^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hguard : SemiprimeD1StackVectorCanonicalExecution.timeBound words cached ≤ 200*(S+1)^8 :=
    hG.trans (Nat.mul_le_mul_left 200 (h2.trans h28))
  have hpos : 0<(S+1)^8 := by positivity
  cases ha : answer cached words with
  | false=>
    simp only [timeBound,ha,Bool.false_eq_true,ite_false,runBound]
    change _ ≤ 30000000000*(S+1)^8
    omega
  | true=>
    have hDot:=SemiprimeD1StackDotEvaluateBounds.timeBound_le c cached baseExpr hbase words stride frequency n hs hf hn hc
      (by omega) (expression_valid cached baseExpr words stride frequency n hm hb ha)
    change SemiprimeD1StackDotEvaluateExecution.timeBound c cached baseExpr words stride frequency n ≤ 10000000000*(S+1)^8 at hDot
    simp only [timeBound,ha,ite_true,runBound]
    change _ ≤ 30000000000*(S+1)^8
    omega
/-- Actual completed source trace with the uniform physical-input polynomial. -/
theorem source_run_bounded (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr) :
    ∃t ≤ runBound c cached,C.run program t (initial c cached tail)=some (done c cached baseExpr words stride frequency n tail) := by
  obtain ⟨t,ht,hr⟩:=source_run c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hb
  exact ⟨t,ht.trans (timeBound_le c cached baseExpr hbase words stride frequency n hs hf hn hc hm hb),hr⟩
/-- Proof-side choice of a PROVED actual trace, never an executing time oracle. -/
noncomputable def sourceEvaluate (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr) :
    StateTransition.EvalsToInTime (C.step program) (initial c cached tail)
      (some (done c cached baseExpr words stride frequency n tail)) (runBound c cached) := by
  let h:=source_run_bounded c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine fixed FinTM2 caller from physical source/vector/metadata/modulus caches. -/
noncomputable def machineEvaluate (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial c cached tail))
      (some (SemiprimeD1StackCalls.configuration (done c cached baseExpr words stride frequency n tail))) (runBound c cached) :=
  SemiprimeD1StackCalls.evalsCorrect (.inl (.inl .base)) output Label.start program _ _ _
    (sourceEvaluate c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hb)
/-- Any actual successful prefix lies before the proved actual completed halt. -/
theorem prefix_fuel_le (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial c cached tail)=some out) : fuel ≤ runBound c cached := by
  obtain ⟨t,ht,hh⟩:=source_run_bounded c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hb
  have hfuel : fuel ≤ t := by
    by_contra hn'
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done c cached baseExpr words stride frequency n tail)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hfuel.trans ht
/-- Every successful source prefix includes ALL107 Boolean data stacks and actual
return-label cells, with duplicate private cache/modulus aliases counted as well. -/
theorem prefix_cells (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial c cached tail)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      108*(SemiprimeD1StackDotEvaluateBounds.inputSize c cached+tail.length+runBound c cached) := by
  let inv:=SemiprimeD1StackDotEvaluateBounds.inputSize c cached+tail.length
  have hdata : ∀k,((initial c cached tail).data k).length ≤ inv := by
    intro k
    rcases k with k|k
    · rcases k with k|k
      · cases k <;> simp [initial,store,D.initial,SemiprimeD1StackDotEvaluate.store,
          SemiprimeD1StackExprDot.bank,SemiprimeD1StackDotEvaluateBounds.inputSize,
          SemiprimeD1StackExprDotBounds.inputSize,inv] <;> omega
      · cases k <;> simp [initial,store,D.initial,SemiprimeD1StackDotEvaluate.store,
          SemiprimeD1StackExpr.input,SemiprimeD1StackExpr.bank,SemiprimeD1StackDotEvaluateBounds.inputSize,inv];omega
    · cases k <;> change 0 ≤ inv <;> omega
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel inv _ out hdata hr
  have hfuel:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hfuel
  have hsum : (∑k : Stack,(out.data k).length) ≤ 107*(inv+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(inv+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hb fuel out hr
  change (∑k : Stack,(out.data k).length)+out.frames.length ≤ 108*(inv+runBound c cached)
  omega
/-- Fixed-degree original-input inventory form, including retained arbitrary suffix. -/
theorem prefix_cells_polynomial (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial c cached tail)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      4000000000000*(SemiprimeD1StackDotEvaluateBounds.inputSize c cached+tail.length+1)^8 := by
  have h:=prefix_cells c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hb fuel out hr
  let inv:=SemiprimeD1StackDotEvaluateBounds.inputSize c cached+tail.length
  have hp : (SemiprimeD1StackDotEvaluateBounds.inputSize c cached+1)^8 ≤ (inv+1)^8 := Nat.pow_le_pow_left (by dsimp [inv];omega) 8
  have hi : inv ≤ (inv+1)^8 := by
    have hh:=Nat.pow_le_pow_right (by omega : 1 ≤ inv+1) (by decide : 1 ≤ 8)
    simp only [pow_one] at hh
    omega
  unfold runBound at h
  change (∑k : Stack,(out.data k).length)+out.frames.length ≤ 4000000000000*(inv+1)^8
  have hh:=Nat.mul_le_mul_left 30000000000 hp
  change (∑k : Stack,(out.data k).length)+out.frames.length ≤ 108*(inv+30000000000*(SemiprimeD1StackDotEvaluateBounds.inputSize c cached+1)^8) at h
  omega
/-- Same complete fixed-degree all-prefix inventory on the genuine target machine. -/
theorem machine_prefix_cells (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial c cached tail)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      4000000000000*(SemiprimeD1StackDotEvaluateBounds.inputSize c cached+tail.length+1)^8 := by
  have he:=SemiprimeD1StackCalls.run_correct (.inl (.inl .base)) output Label.start program fuel (initial c cached tail)
  have hh:=he.trans hr
  cases hc' : C.run program fuel (initial c cached tail) with
  | none=>rw [hc'] at hh;cases hh
  | some out=>
    rw [hc'] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells_polynomial c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hb fuel out hc'
end RiemannGaussian.SemiprimeD1StackGuardedDotBounds
