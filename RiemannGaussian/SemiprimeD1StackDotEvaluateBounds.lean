/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackDotEvaluateExecution

/-! # Whole source-and-evaluation bit-machine resource bound
Syntax size is DERIVED from the actual construction trace, not assumed. This
pays both original programs on their shared physical stack and includes all
ninety-seven Boolean stacks and real return tags at every successful prefix.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackDotEvaluateBounds
open SemiprimeD1StackDotEvaluate SemiprimeD1StackDotEvaluateExecution
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeMacroEntryBitPrimitives (Expr Valid)

/-- The whole prepared input inventory retains original binary modulus length. -/
def inputSize (c : D.Cache) (cached : List Bool) : ℕ :=
  SemiprimeD1StackExprDotBounds.inputSize c+cached.length+1

/-- Source syntax size follows from its actual complete instruction trace.
Every repeated subtree and source occurrence is physically present and paid. -/
theorem syntax_size_le (c : D.Cache) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) :
    SemiprimeD1StackExprCodec.size (expression baseExpr words stride frequency n) ≤
      SemiprimeD1StackExprDotBounds.inputSize c+
        SemiprimeD1StackExprDotExecution.timeBound c words stride frequency n := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackExprDotExecution.source_run c words stride frequency n hs hf hn hc []
  have hd:=SemiprimeD1StackReturnLink.run_data_bound D.program m
    (SemiprimeD1StackExprDotBounds.inputSize c) _ _ (by
      intro k;cases k <;> simp [D.initial,D.bank,SemiprimeD1StackExprDotBounds.inputSize] <;> omega) hr
  have hcode:=SemiprimeD1StackExprDotBounds.output_original c baseExpr hbase words stride frequency n []
  have hout:=hd SemiprimeD1StackExprDot.Stack.output
  rw [hcode,SemiprimeD1StackExprCodec.encode_length] at hout
  simp only [List.length_nil,Nat.add_zero] at hout
  simp only [expression]
  omega

/-- The complete SAME program has a fixed degree-eight actual bit time bound.
No source-size, result-size, index, power or clock oracle is required. -/
theorem timeBound_le (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached)
    (hv : Valid cached (expression baseExpr words stride frequency n)) :
    timeBound c cached baseExpr words stride frequency n ≤ 10000000000*(inputSize c cached+1)^8 := by
  let S:=inputSize c cached
  have hD : SemiprimeD1StackExprDotBounds.inputSize c ≤ S := by dsimp [S,inputSize];omega
  have hM : cached.length ≤ S := by dsimp [S,inputSize];omega
  have hgrow : S+1 ≤ (S+1)^5 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ S+1) (by decide : 1 ≤ 5)
  have hDtime:=SemiprimeD1StackExprDotBounds.timeBound_le c words stride frequency n hs hf hn hc
  have hDpow : 10000*(SemiprimeD1StackExprDotBounds.inputSize c+1)^5 ≤ 10000*(S+1)^5 := by gcongr
  have hsize:=syntax_size_le c baseExpr hbase words stride frequency n hs hf hn hc
  have hsize' : SemiprimeD1StackExprCodec.size (expression baseExpr words stride frequency n) ≤ 10001*(S+1)^5 := by omega
  have hEtime:=SemiprimeD1StackExprBounds.totalTime_le cached (expression baseExpr words stride frequency n) hm hv
  have hnode : SemiprimeD1StackExprBounds.nodeBudget cached.length=540000*(cached.length+1)^3 := by
    unfold SemiprimeD1StackExprBounds.nodeBudget
    ring
  unfold SemiprimeD1StackExprBounds.timeBound at hEtime
  rw [hnode] at hEtime
  have hnode' : 540000*(cached.length+1)^3 ≤ 540000*(S+1)^3 := by gcongr
  have hprod:=Nat.mul_le_mul hnode' hsize'
  rw [show 540000*(S+1)^3*(10001*(S+1)^5)=5400540000*(S+1)^8 by ring] at hprod
  have h58 : (S+1)^5 ≤ (S+1)^8 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpos : 0<(S+1)^8 := by positivity
  change timeBound c cached baseExpr words stride frequency n ≤ 10000000000*(S+1)^8
  unfold timeBound
  omega

/-- Whole actual source certificate; witness selection is only proof-side. -/
noncomputable def sourceEvaluate (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached)
    (hv : Valid cached (expression baseExpr words stride frequency n)) :
    StateTransition.EvalsToInTime (C.step program) (initial c cached tail)
      (some (done c cached baseExpr words stride frequency n tail)) (10000000000*(inputSize c cached+1)^8) := by
  let h:=source_run c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hv
  let m:=Classical.choose h
  have hh:=Classical.choose_spec h
  exact ⟨⟨m,hh.2⟩,hh.1.trans (timeBound_le c cached baseExpr hbase words stride frequency n hs hf hn hc hm hv)⟩

/-- Genuine fixed finite-machine execution from physical original dot arguments. -/
noncomputable def machineEvaluate (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached)
    (hv : Valid cached (expression baseExpr words stride frequency n)) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial c cached tail))
      (some (SemiprimeD1StackCalls.configuration (done c cached baseExpr words stride frequency n tail)))
      (10000000000*(inputSize c cached+1)^8) :=
  SemiprimeD1StackCalls.evalsCorrect (K:=Stack) (L:=Label) (.inl .base) output Label.start program _ _ _
    (sourceEvaluate c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hv)

/-- The shared source-code stack is consumed only through the original prefix. -/
theorem retained_suffix (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (words : List (List Bool)) (stride frequency n : ℕ) (tail : List Bool) :
    (done c cached baseExpr words stride frequency n tail).data code=tail := rfl
/-- Raw original binary modulus survives all source and arithmetic work. -/
theorem retained_modulus (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (words : List (List Bool)) (stride frequency n : ℕ) (tail : List Bool) :
    (done c cached baseExpr words stride frequency n tail).data modulus=cached := rfl

/-- Every successful source prefix lies before the actual whole-program halt. -/
theorem prefix_fuel_le (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached)
    (hv : Valid cached (expression baseExpr words stride frequency n))
    (fuel : ℕ) (out : C.State Stack Label) (hr : C.run program fuel (initial c cached tail)=some out) :
    fuel ≤ 10000000000*(inputSize c cached+1)^8 := by
  obtain ⟨m,hbound,he⟩:=source_run c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hv
  have hfm : fuel ≤ m := by
    by_contra h
    have hh : fuel=m+(1+(fuel-(m+1))) := by omega
    rw [hh,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done c cached baseExpr words stride frequency n tail)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hfm.trans (hbound.trans (timeBound_le c cached baseExpr hbase words stride frequency n hs hf hn hc hm hv))

/-- Every actual prefix counts ALL97 Boolean data stacks and real return tags. -/
theorem prefix_cells (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached)
    (hv : Valid cached (expression baseExpr words stride frequency n))
    (fuel : ℕ) (out : C.State Stack Label) (hr : C.run program fuel (initial c cached tail)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      98*(inputSize c cached+tail.length+10000000000*(inputSize c cached+1)^8) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (inputSize c cached+tail.length) _ out
    (by
      intro k
      rcases k with k|k
      · cases k <;> simp [initial,store,D.bank,inputSize,SemiprimeD1StackExprDotBounds.inputSize] <;> omega
      · cases k <;> simp [initial,store,E.input,E.bank,inputSize];omega) hr
  have ht:=prefix_fuel_le c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hv fuel out hr
  have hfuel:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hfuel
  have hsum : (∑k : Stack,(out.data k).length) ≤ 97*(inputSize c cached+tail.length+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(inputSize c cached+tail.length+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  omega

/-- The identical bound on EVERY reached prefix of the actual finite machine. -/
theorem machine_prefix_cells (c : D.Cache) (cached : List Bool) (baseExpr : Expr)
    (hbase : c.base=SemiprimeD1StackExprCodec.encode baseExpr []) (words : List (List Bool))
    (stride frequency n : ℕ) (hs : c.stride=unary stride) (hf : c.frequency=unary frequency)
    (hn : c.count=unary n) (hc : c.words=vectorBits words) (tail : List Bool)
    (hm : 0<SemiprimeBitArithmetic.bitValue cached)
    (hv : Valid cached (expression baseExpr words stride frequency n))
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial c cached tail)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      98*(inputSize c cached+tail.length+10000000000*(inputSize c cached+1)^8) := by
  have he:=SemiprimeD1StackCalls.run_correct (K:=Stack) (L:=Label) (.inl .base) output Label.start program fuel (initial c cached tail)
  change (C.run program fuel (initial c cached tail)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial c cached tail))) at he
  have hh:=he.trans hr
  cases hrun:C.run program fuel (initial c cached tail) with
  | none => rw [hrun] at hh;cases hh
  | some out =>
    rw [hrun] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells c cached baseExpr hbase words stride frequency n hs hf hn hc tail hm hv fuel out hrun

end RiemannGaussian.SemiprimeD1StackDotEvaluateBounds
