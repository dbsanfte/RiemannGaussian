/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleOriginal
/-! # Closed physical public-scale cost from original physical inputs
No source-size, modulus/word width, intermediate Fits or component clock advice
is an input. Every bound derives the actual acquired caches and literal traces.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicScaleBounds
open SemiprimeD1StackPublicScale SemiprimeD1StackPublicScaleState SemiprimeD1StackPublicScaleInputs
open SemiprimeD1StackPublicScaleAcquire SemiprimeD1StackPublicScaleDot SemiprimeD1StackPublicScaleTail
open SemiprimeD1StackPublicScaleExecution SemiprimeD1StackPublicScaleOriginal SemiprimeBitArithmetic
/-- Intrinsic acquired modulus-word length from actual binary N. -/
theorem cached_length (bits : List Bool) : (cached bits).length≤64*bits.length+2 :=
  (SemiprimeD1StackRootSourceBounds.acquired_lengths bits).1
/-- Every acquired original root-source byte is counted, including all repeated
base copies in inverse powers; no source-size answer is supplied. -/
theorem base_length (bits : List Bool) (inverse : Bool) :
    (baseCode bits inverse).length≤11*(cached bits).length+14 := by
  cases inverse
  · change 9≤11*(cached bits).length+14;omega
  · change (SemiprimeD1StackRootSourceExecution.rootCode (SemiprimeD1BinaryPublicAcquisitionComponents.result bits)).length≤_
    unfold SemiprimeD1StackRootSourceExecution.rootCode
    rw [SemiprimeD1StackExprPowerSpec.result_length]
    have hn : (SemiprimeD1StackRootSourceExecution.rootMarkers
        (SemiprimeD1BinaryPublicAcquisitionComponents.result bits)).length≤(cached bits).length := by
      change ((SemiprimeD1BinaryPublicAcquisitionComponents.result bits R.modulusKey).tail.tail).length≤
        (SemiprimeD1BinaryPublicAcquisitionComponents.result bits R.modulusKey).length
      simp only [List.length_tail];omega
    have h9 : (SemiprimeD1StackRootSources.literalCode 0).length=9 := by decide
    rw [h9]
    simp only [List.length_nil]
    omega
/-- Only ORIGINAL physical input tapes are counted here. -/
def inputSize (bits raw stride frequency : List Bool) : ℕ :=
  bits.length+raw.length+stride.length+frequency.length+2
/-- Acquired padding/base/modulus inventory is polynomial before the entire
input family; no T-term list or native grouped-word cache is present. -/
theorem dot_inventory (bits raw stride frequency : List Bool) (inverse : Bool) :
    SemiprimeD1StackInputDotBounds.inputSize (paddedRaw bits raw) (args bits stride frequency inverse) (cached bits)+1≤
      1000*inputSize bits raw stride frequency := by
  have hb:=base_length bits inverse
  have hm:=cached_length bits
  unfold SemiprimeD1StackInputDotBounds.inputSize args inputSize
  simp only [paddedRaw,List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  omega
/-- Canonical actual result bytes have the acquired width, while rejection
returns empty; no output-width or successful-guard premise is supplied. -/
theorem result_length (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    (readData bits raw stride frequency inverse j k (equalStack .left)).length≤(cached bits).length := by
  rw [read_left,result_value]
  cases he : SemiprimeD1StackPublicScaleMeaning.guard (cached bits) (inputWord bits raw) with
  | false=>simp only [Bool.false_eq_true,ite_false,List.length_nil];exact Nat.zero_le _
  | true=>
    simp only [ite_true]
    obtain ⟨hm,hb⟩:=original_valid bits hc hN inverse
    rw [←expression_original bits hc hN inverse] at hb
    have hi:=(SemiprimeD1StackPublicScaleMeaning.guard_true (cached bits) (inputWord bits raw) (by omega)).mp he
    have hv:=SemiprimeMacroEntryBitPrimitives.dotExpr_valid (cached bits) hm (expression bits inverse) hb j k 2
      (SemiprimeD1StackPublicScaleMeaning.inputAt (cached bits) (inputWord bits raw)) (by
        intro q hq
        interval_cases q <;> simp [SemiprimeD1StackPublicScaleMeaning.inputAt,
          SemiprimeD1StackPublicScaleMeaning.zeroWord_value,hi];omega)
    exact (SemiprimeMacroEntryBitPrimitives.execute_bounds (cached bits) (by omega) _ hv).1.le
/-- Full actual tail bound includes status read, skipped/success branch, output
word acquisition, copied template and actual numeric-comparison cleanup. -/
theorem tail_le (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    tailBudget bits raw stride frequency inverse j k≤14*(cached bits).length+19 := by
  have hl:=result_length bits raw stride frequency inverse j k hc hN
  have hr : (readData bits raw stride frequency inverse j k (equalStack .right)).length=(cached bits).length := by
    rw [read_right];exact SemiprimeD1StackWordBlockExecution.result_length _ _
  have he:=SemiprimeD1StackWordEqualExecution.executionTime_le
    (readData bits raw stride frequency inverse j k (equalStack .left))
    (readData bits raw stride frequency inverse j k (equalStack .right))
  rw [hr] at he
  unfold tailBudget SemiprimeD1StackWordBlockExecution.totalTime
  omega
/-- Actual preparation allowance, written in the actual acquired cache lengths. -/
theorem prep_eq (bits raw : List Bool) (inverse : Bool) :
    prepBudget (roots bits) raw inverse=5*(baseCode bits inverse).length+12*(cached bits).length+5*raw.length+20 := by
  unfold prepBudget
  change 1+(5*(baseCode bits inverse).length+4)+(5*(cached bits).length+4)+(5*raw.length+4)+
    (5*(cached bits).length+4)+(2*(cached bits).length+1)+2=_
  omega
/-- A fixed degree-sixteen original-physical-input transition envelope. -/
def runBound (bits raw stride frequency : List Bool) : ℕ := 10^70*(inputSize bits raw stride frequency)^16
/-- Whole OWN executed trace bound; old/new clocks are never equated. -/
theorem timeBound_le (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ)
    (hj : stride=SemiprimeD1StackUnaryDivmod.unary j) (hk : frequency=SemiprimeD1StackUnaryDivmod.unary k)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    timeBound bits raw stride frequency inverse j k≤runBound bits raw stride frequency := by
  let S:=inputSize bits raw stride frequency
  obtain ⟨hm,hb⟩:=original_valid bits hc hN inverse
  rw [←expression_original bits hc hN inverse] at hb
  have hd:=SemiprimeD1StackInputDotBounds.timeBound_le (paddedRaw bits raw) (args bits stride frequency inverse)
    (cached bits) (expression bits inverse) (source_code bits inverse) j k 2 hj hk rfl hm hb
  have hi:=Nat.pow_le_pow_left (dot_inventory bits raw stride frequency inverse) 16
  rw [mul_pow] at hi
  change (SemiprimeD1StackInputDotBounds.inputSize (paddedRaw bits raw) (args bits stride frequency inverse) (cached bits)+1)^16≤
    1000^16*S^16 at hi
  norm_num at hi
  unfold SemiprimeD1StackInputDotBounds.runBound at hd
  have htail:=tail_le bits raw stride frequency inverse j k hc hN
  have hM:=cached_length bits
  have hB:=base_length bits inverse
  have hx : bits.length≤S := by dsimp [S,inputSize];omega
  have hS : 1≤S := by dsimp [S,inputSize];omega
  have hp : (bits.length+1)^2≤S^16 :=
    (Nat.pow_le_pow_left (by dsimp [S,inputSize];omega) 2).trans (Nat.pow_le_pow_right hS (by decide : 2≤16))
  have hlin : S≤S^16 := by simpa only [pow_one] using Nat.pow_le_pow_right hS (by decide : 1≤16)
  have hprep : prepBudget (roots bits) raw inverse≤10000*S := by
    rw [prep_eq]
    dsimp [S,inputSize]
    omega
  unfold timeBound runBound
  change SemiprimeD1StackRootSourceBounds.timeBound bits+1+prepBudget (roots bits) raw inverse+
    (SemiprimeD1StackInputDotExecution.timeBound (paddedRaw bits raw) (args bits stride frequency inverse)
      (cached bits) (expression bits inverse) j k 2+1)+tailBudget bits raw stride frequency inverse j k+1≤10^70*S^16
  unfold SemiprimeD1StackRootSourceBounds.timeBound
  norm_num only
  omega
/-- Actual whole source trace bounded solely by original physical input inventory. -/
theorem source_run_bounded (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ)
    (hj : stride=SemiprimeD1StackUnaryDivmod.unary j) (hk : frequency=SemiprimeD1StackUnaryDivmod.unary k)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    ∃t≤runBound bits raw stride frequency,C.run program t (initial bits raw stride frequency inverse)=
      some (done bits raw stride frequency inverse j k) := by
  obtain ⟨t,ht,hr⟩:=source_run bits raw stride frequency inverse j k hj hk hc hN
  exact ⟨t,ht.trans (timeBound_le bits raw stride frequency inverse j k hj hk hc hN),hr⟩
/-- Original physical N input location, fixed before input lengths. -/
def inputRole : Stack := .inl (.inl (SemiprimeD1BinaryPublicAcquisition.digitStack
  (SemiprimeD1BinaryPublicAcquisition.Digits.metaStack .input)))
/-- Proof certificate of the actual completed finite-code source trace. -/
noncomputable def sourceCheck (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ)
    (hj : stride=SemiprimeD1StackUnaryDivmod.unary j) (hk : frequency=SemiprimeD1StackUnaryDivmod.unary k)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    StateTransition.EvalsToInTime (C.step program) (initial bits raw stride frequency inverse)
      (some (done bits raw stride frequency inverse j k)) (runBound bits raw stride frequency) := by
  let h:=source_run_bounded bits raw stride frequency inverse j k hj hk hc hN
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- Genuine FinTM2 whole original-input scale execution; no backend/evaluator,
word/vector/guard/verdict/clock supplier remains at this machine endpoint. -/
noncomputable def machineCheck (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ)
    (hj : stride=SemiprimeD1StackUnaryDivmod.unary j) (hk : frequency=SemiprimeD1StackUnaryDivmod.unary k)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits raw stride frequency inverse))
      (some (SemiprimeD1StackCalls.configuration (done bits raw stride frequency inverse j k)))
      (runBound bits raw stride frequency) :=
  SemiprimeD1StackCalls.evalsCorrect inputRole (auxRole .output) Label.start program _ _ _
    (sourceCheck bits raw stride frequency inverse j k hj hk hc hN)
/-- Every successful actual prefix precedes the proved completed halt. -/
theorem prefix_fuel_le (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ)
    (hj : stride=SemiprimeD1StackUnaryDivmod.unary j) (hk : frequency=SemiprimeD1StackUnaryDivmod.unary k)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits raw stride frequency inverse)=some out) :
    fuel≤runBound bits raw stride frequency := by
  obtain ⟨t,ht,hh⟩:=source_run_bounded bits raw stride frequency inverse j k hj hk hc hN
  have hf : fuel≤t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done bits raw stride frequency inverse j k)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- Initial original root cache has only the original binary input populated. -/
theorem root_initial_bound (bits : List Bool) (k : R.Stack) : (R.input bits k).length≤bits.length := by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · cases k <;> simp only [R.input,SemiprimeD1StackRootSources.store,SemiprimeD1StackRootSources.P.input,
          SemiprimeD1BinaryPublicAcquisition.store,SemiprimeD1BinaryPublicAcquisition.Digits.input,
          SemiprimeD1BinaryDigitAcquisition.store,SemiprimeD1StackTransform.input,Sum.elim_inl,List.length_nil] <;> omega
      · rcases k with k|k <;> exact Nat.zero_le _
    · rcases k with k|k <;> exact Nat.zero_le _
  · cases k <;> exact Nat.zero_le _
/-- ALL original physical data roles have an input-derived initial bound. -/
theorem initial_bound (bits raw stride frequency : List Bool) (inverse : Bool) (q : Stack) :
    ((initial bits raw stride frequency inverse).data q).length≤ inputSize bits raw stride frequency := by
  let S:=inputSize bits raw stride frequency
  have hs : bits.length+raw.length+stride.length+frequency.length+2=S := rfl
  change _≤S
  rcases q with q|q
  · exact (root_initial_bound bits q).trans (by omega)
  · rcases q with q|q
    · rcases q with q|q
      · have h:=SemiprimeD1StackInputDotBounds.guarded_initial_bound
          (SemiprimeD1StackInputDotEvaluate.withVector ⟨[],stride,frequency,[]⟩ []) [] [] q
        change _≤S
        change ((SemiprimeD1StackInputDotEvaluate.G.initial
          (SemiprimeD1StackInputDotEvaluate.withVector ⟨[],stride,frequency,[]⟩ []) [] []).data q).length≤S
        exact h.trans (by simp only [SemiprimeD1StackExprDotBounds.inputSize,SemiprimeD1StackInputDotEvaluate.withVector,
          List.length_nil,Nat.zero_add,Nat.add_zero];omega)
      · rcases q with q|q <;> fin_cases q <;> exact Nat.zero_le _
    · cases q <;> simp only [initial,store,aux,Sum.elim_inr,List.length_cons,List.length_nil] <;> omega
/-- Fixed polynomial total data+real-return storage bound at every machine prefix. -/
def spaceBound (bits raw stride frequency : List Bool) : ℕ := 10^74*(inputSize bits raw stride frequency)^16
/-- Every source prefix counts ALL160 Boolean data stacks and actual returns. -/
theorem prefix_cells (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ)
    (hj : stride=SemiprimeD1StackUnaryDivmod.unary j) (hk : frequency=SemiprimeD1StackUnaryDivmod.unary k)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits raw stride frequency inverse)=some out) :
    (∑q : Stack,(out.data q).length)+out.frames.length≤ spaceBound bits raw stride frequency := by
  let S:=inputSize bits raw stride frequency
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel S _ out (initial_bound bits raw stride frequency inverse) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hsum : (∑q : Stack,(out.data q).length)≤160*(S+fuel) := by
    calc
      _≤∑_q : Stack,(S+fuel) := Finset.sum_le_sum (fun q _=>hd q)
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits raw stride frequency inverse j k hj hk hc hN fuel out hr
  have hS : 1≤S := by dsimp [S,inputSize];omega
  have hp : S≤S^16 := by simpa only [pow_one] using Nat.pow_le_pow_right hS (by decide : 1≤16)
  change fuel≤10^70*S^16 at ht
  change _≤10^74*S^16
  norm_num only at ht ⊢
  omega
/-- Same ALL160-data+real-return inventory at EVERY genuine FinTM2 prefix. -/
theorem machine_prefix_cells (bits raw stride frequency : List Bool) (inverse : Bool) (j k : ℕ)
    (hj : stride=SemiprimeD1StackUnaryDivmod.unary j) (hk : frequency=SemiprimeD1StackUnaryDivmod.unary k)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun c=>c.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits raw stride frequency inverse)))=some cfg) :
    (∑q : Stack,(cfg.stk (some q)).length)+(cfg.stk none).length≤ spaceBound bits raw stride frequency := by
  have he:=SemiprimeD1StackCalls.run_correct inputRole (auxRole .output) Label.start program fuel
    (initial bits raw stride frequency inverse)
  have hh:=he.trans hr
  cases ho : C.run program fuel (initial bits raw stride frequency inverse) with
  | none=>rw [ho] at hh;cases hh
  | some out=>
    rw [ho] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells bits raw stride frequency inverse j k hj hk hc hN fuel out ho
end RiemannGaussian.SemiprimeD1StackPublicScaleBounds
