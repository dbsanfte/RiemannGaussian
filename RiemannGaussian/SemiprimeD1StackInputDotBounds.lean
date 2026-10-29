/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputDotExecution
/-! # Actual RAW assignment-to-dot time and complete prefix storage
Output-vector length is derived from the actual streaming word producer. No
native grouping/getter, vector, count/arity result or execution-clock is advised.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackInputDotBounds
open SemiprimeD1StackInputDotEvaluate SemiprimeD1StackInputDotExecution
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeMacroEntryBitPrimitives (Expr Valid)
/-- Original physical inputs only; NO vector/source-size answer occurs. -/
def inputSize (raw : List Bool) (args : Args) (cached : List Bool) : ℕ :=
  raw.length+args.base.length+args.stride.length+args.frequency.length+args.count.length+cached.length+1
/-- Every physically produced field/tag/padding byte is counted exactly. -/
theorem vector_length (raw : List Bool) (args : Args) (cached : List Bool) :
    (vectorBits (words raw args cached)).length=args.count.length*(2*cached.length+2)+1 := by
  have h:=SemiprimeD1StackWordVectorSpec.entries_length cached args.count.length raw
  rw [←SemiprimeD1StackDigitBankSpec.entries_vectorBits]
  change (SemiprimeD1StackDigitBankSpec.entries
    (SemiprimeD1StackWordVectorSpec.blocks cached args.count.length raw)++[false]).length=_
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega
/-- Pure scalar arithmetic, isolated from concrete producer terms during elaboration. -/
theorem consumer_scalar (b s f n m S : ℕ) (hs : b+s+f+n+m ≤ S) :
    b+(n*(2*m+2)+1)+s+f+n+1+m+1+1 ≤ 6*(S+1)^2 := by
  have hn : n ≤ S+1 := by omega
  have hm : m+1 ≤ S+1 := by omega
  have hp:=Nat.mul_le_mul hn hm
  ring_nf at hp ⊢
  omega
/-- Derive the ACTUAL consumer cache inventory from the producer, without a
supplied encoded vector or catalogue/count bound. -/
theorem consumer_inventory (raw : List Bool) (args : Args) (cached : List Bool) :
    SemiprimeD1StackDotEvaluateBounds.inputSize (cache raw args cached) cached+1 ≤
      6*(inputSize raw args cached+1)^2 := by
  change args.base.length+(vectorBits (words raw args cached)).length+args.stride.length+args.frequency.length+
      args.count.length+1+cached.length+1+1 ≤ 6*(inputSize raw args cached+1)^2
  rw [vector_length]
  exact consumer_scalar _ _ _ _ _ _ (by unfold inputSize;omega)
/-- The actual producer's complete setup/copy/block/log/reverse work is paid. -/
theorem acquisition_time (raw : List Bool) (args : Args) (cached : List Bool) :
    SemiprimeD1StackWordVectorExecution.timeBound raw cached args.count ≤ 500*(inputSize raw args cached+1)^2 := by
  let S:=inputSize raw args cached
  have hc : args.count.length+1 ≤ S+1 := by dsimp [S,inputSize];omega
  have hm : cached.length+1 ≤ S+1 := by dsimp [S,inputSize];omega
  have hp:=Nat.mul_le_mul hc hm
  rw [←pow_two] at hp
  have hr : raw.length+1 ≤ S+1 := by dsimp [S,inputSize];omega
  have hlin : S+1 ≤ (S+1)^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ S+1) (by decide : 1 ≤ 2)
  unfold SemiprimeD1StackWordVectorExecution.timeBound
  change _ ≤ 500*(S+1)^2
  omega
/-- Fixed degree-sixteen physical-input envelope, before the entire input family. -/
def runBound (raw : List Bool) (args : Args) (cached : List Bool) : ℕ :=
  1000000000000000000*(inputSize raw args cached+1)^16
/-- Closed fixed polynomial from ACTUAL producer + ACTUAL guarded numerical dot.
Only original base validity/M>1 and actual physical stream formats remain. -/
theorem timeBound_le (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (hbase : args.base=SemiprimeD1StackExprCodec.encode baseExpr [])
    (stride frequency n : ℕ) (hs : args.stride=unary stride) (hf : args.frequency=unary frequency)
    (hn : args.count=unary n) (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr) :
    timeBound raw args cached baseExpr stride frequency n ≤ runBound raw args cached := by
  let S:=inputSize raw args cached
  have hW:=acquisition_time raw args cached
  have hG:=SemiprimeD1StackGuardedDotBounds.timeBound_le (cache raw args cached) cached baseExpr hbase
    (words raw args cached) stride frequency n hs hf hn rfl hm hb
  have hi:=consumer_inventory raw args cached
  have hp:=Nat.mul_le_mul_left 30000000000 (Nat.pow_le_pow_left hi 8)
  have he : 30000000000*(6*(S+1)^2)^8=50388480000000000*(S+1)^16 := by
    rw [mul_pow,←pow_mul,←Nat.mul_assoc]
    norm_num
  change 30000000000*(SemiprimeD1StackDotEvaluateBounds.inputSize (cache raw args cached) cached+1)^8 ≤
    30000000000*(6*(S+1)^2)^8 at hp
  rw [he] at hp
  have hg:=hG.trans hp
  have h216 : (S+1)^2 ≤ (S+1)^16 := Nat.pow_le_pow_right (by omega) (by decide)
  have hpos : 0<(S+1)^16 := Nat.pow_pos (by omega)
  change SemiprimeD1StackWordVectorExecution.timeBound raw cached args.count ≤ 500*(S+1)^2 at hW
  unfold timeBound runBound
  change _ ≤ 1000000000000000000*(S+1)^16
  omega
/-- Exact actual closed RAW-input source trace with original-input polynomial. -/
theorem source_run_bounded (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (hbase : args.base=SemiprimeD1StackExprCodec.encode baseExpr [])
    (stride frequency n : ℕ) (hs : args.stride=unary stride) (hf : args.frequency=unary frequency)
    (hn : args.count=unary n) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr) :
    ∃t ≤ runBound raw args cached,C.run program t (initial raw args cached tail)=
      some (done raw args cached baseExpr stride frequency n tail) := by
  obtain ⟨t,ht,hr⟩:=source_run raw args cached baseExpr hbase stride frequency n hs hf hn tail hm hb
  exact ⟨t,ht.trans (timeBound_le raw args cached baseExpr hbase stride frequency n hs hf hn hm hb),hr⟩
/-- Proof-side choice of an ACTUAL completed finite-code trace, not a clock opcode. -/
noncomputable def sourceEvaluate (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (hbase : args.base=SemiprimeD1StackExprCodec.encode baseExpr [])
    (stride frequency n : ℕ) (hs : args.stride=unary stride) (hf : args.frequency=unary frequency)
    (hn : args.count=unary n) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr) :
    StateTransition.EvalsToInTime (C.step program) (initial raw args cached tail)
      (some (done raw args cached baseExpr stride frequency n tail)) (runBound raw args cached) := by
  let h:=source_run_bounded raw args cached baseExpr hbase stride frequency n hs hf hn tail hm hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine fixed finite bit machine from RAW assignment and physical parameters. -/
noncomputable def machineEvaluate (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (hbase : args.base=SemiprimeD1StackExprCodec.encode baseExpr [])
    (stride frequency n : ℕ) (hs : args.stride=unary stride) (hf : args.frequency=unary frequency)
    (hn : args.count=unary n) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial raw args cached tail))
      (some (SemiprimeD1StackCalls.configuration (done raw args cached baseExpr stride frequency n tail))) (runBound raw args cached) :=
  SemiprimeD1StackCalls.evalsCorrect rawRole output Label.start program _ _ _
    (sourceEvaluate raw args cached baseExpr hbase stride frequency n hs hf hn tail hm hb)
/-- Successful prefixes precede the bounded actual complete halt. -/
theorem prefix_fuel_le (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (hbase : args.base=SemiprimeD1StackExprCodec.encode baseExpr [])
    (stride frequency n : ℕ) (hs : args.stride=unary stride) (hf : args.frequency=unary frequency)
    (hn : args.count=unary n) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial raw args cached tail)=some out) : fuel ≤ runBound raw args cached := by
  obtain ⟨t,ht,hh⟩:=source_run_bounded raw args cached baseExpr hbase stride frequency n hs hf hn tail hm hb
  have hfuel : fuel ≤ t := by
    by_contra hn'
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done raw args cached baseExpr stride frequency n tail)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hfuel.trans ht
/-- Physical initial-cache inventory, before any input-specific source term is
introduced. This pays every private guard/evaluator role as well. -/
theorem guarded_initial_bound (c : SemiprimeD1StackExprDot.Cache) (cached tail : List Bool)
    (k : G.Stack) : ((G.initial c cached tail).data k).length ≤
      SemiprimeD1StackExprDotBounds.inputSize c+cached.length+tail.length := by
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> simp [G.initial,SemiprimeD1StackGuardedDotEvaluate.store,
        SemiprimeD1StackDotEvaluate.initial,SemiprimeD1StackDotEvaluate.store,SemiprimeD1StackExprDot.bank,
        SemiprimeD1StackExprDotBounds.inputSize] <;> omega
    · cases k <;> simp [G.initial,SemiprimeD1StackGuardedDotEvaluate.store,
        SemiprimeD1StackDotEvaluate.initial,SemiprimeD1StackDotEvaluate.store,
        SemiprimeD1StackExpr.input,SemiprimeD1StackExpr.bank,SemiprimeD1StackExprDotBounds.inputSize];omega
  · cases k <;> exact Nat.zero_le _
/-- EVERY actual source prefix counts ALL117 Boolean data roles and the real
return-label cells, including both retained raw assignment and unread suffix. -/
theorem prefix_cells (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (hbase : args.base=SemiprimeD1StackExprCodec.encode baseExpr [])
    (stride frequency n : ℕ) (hs : args.stride=unary stride) (hf : args.frequency=unary frequency)
    (hn : args.count=unary n) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial raw args cached tail)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      118*(inputSize raw args cached+tail.length+runBound raw args cached) := by
  let inv:=inputSize raw args cached+tail.length
  have hI : SemiprimeD1StackExprDotBounds.inputSize (withVector args [])+cached.length+tail.length ≤ inv := by
    dsimp [inv,inputSize,SemiprimeD1StackExprDotBounds.inputSize,withVector]
    omega
  have hdata : ∀k,((initial raw args cached tail).data k).length ≤ inv := by
    intro k
    rcases k with k|k
    · exact (guarded_initial_bound (withVector args []) cached tail k).trans hI
    · rcases k with k|k
      · fin_cases k <;> change 0 ≤ inv <;> omega
      · fin_cases k <;> first | (change 0 ≤ inv;omega) | (change raw.length ≤ inv;dsimp [inv,inputSize];omega)
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel inv _ out hdata hr
  have hfuel:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length ≤ 0+fuel at hfuel
  have hsum : (∑k : Stack,(out.data k).length) ≤ 117*(inv+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(inv+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le raw args cached baseExpr hbase stride frequency n hs hf hn tail hm hb fuel out hr
  change (∑k : Stack,(out.data k).length)+out.frames.length ≤ 118*(inv+runBound raw args cached)
  omega
/-- Fixed physical-input polynomial form, including retained arbitrary code suffix. -/
theorem prefix_cells_polynomial (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (hbase : args.base=SemiprimeD1StackExprCodec.encode baseExpr [])
    (stride frequency n : ℕ) (hs : args.stride=unary stride) (hf : args.frequency=unary frequency)
    (hn : args.count=unary n) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr)
    (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial raw args cached tail)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length ≤
      1000000000000000000000*(inputSize raw args cached+tail.length+1)^16 := by
  have h:=prefix_cells raw args cached baseExpr hbase stride frequency n hs hf hn tail hm hb fuel out hr
  let inv:=inputSize raw args cached+tail.length
  have hp : (inputSize raw args cached+1)^16 ≤ (inv+1)^16 := Nat.pow_le_pow_left (by dsimp [inv];omega) 16
  have hi : inv ≤ (inv+1)^16 := by
    have hh:=Nat.pow_le_pow_right (by omega : 1 ≤ inv+1) (by decide : 1 ≤ 16)
    simp only [pow_one] at hh
    omega
  have hh:=Nat.mul_le_mul_left 1000000000000000000 hp
  unfold runBound at h
  change (∑k : Stack,(out.data k).length)+out.frames.length ≤
    118*(inv+1000000000000000000*(inputSize raw args cached+1)^16) at h
  change (∑k : Stack,(out.data k).length)+out.frames.length ≤ 1000000000000000000000*(inv+1)^16
  omega
/-- The identical all-prefix bound on the genuine fixed target machine. -/
theorem machine_prefix_cells (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (hbase : args.base=SemiprimeD1StackExprCodec.encode baseExpr [])
    (stride frequency n : ℕ) (hs : args.stride=unary stride) (hf : args.frequency=unary frequency)
    (hn : args.count=unary n) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial raw args cached tail)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length ≤
      1000000000000000000000*(inputSize raw args cached+tail.length+1)^16 := by
  have he:=SemiprimeD1StackCalls.run_correct rawRole output Label.start program fuel (initial raw args cached tail)
  have hh:=he.trans hr
  cases hc : C.run program fuel (initial raw args cached tail) with
  | none=>rw [hc] at hh;cases hh
  | some out=>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells_polynomial raw args cached baseExpr hbase stride frequency n hs hf hn tail hm hb fuel out hc
end RiemannGaussian.SemiprimeD1StackInputDotBounds
