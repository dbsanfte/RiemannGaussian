/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFactorScopeFibreExecution
/-! # Actual complete/prepared factor-fibre clocks and all137 physical roles -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFactorScopeFibreBounds
open SemiprimeD1StackFactorScopeFibre SemiprimeD1StackFactorScopeFibreExecution
/-- Exact acquired pair bytes are bounded by the paid original scoped-port stream. -/
theorem pair_bytes (bits : List Bool) (hb : bits≠[]) :
    (pairTape bits).length≤10^114*(bits.length+1)^30+1 := by
  have hr:=SemiprimeD1StackFactorScopePairBounds.raw_length (P.rows bits)
  have hs:=SemiprimeD1StackFactorScopePairBounds.stream_length bits hb
  have he:=congrArg List.length (SemiprimeD1FactorScopePairEncoding.raw_records (P.rows bits) [])
  change _=(pairTape bits).length at he
  simp only [List.length_append,List.length_cons,List.length_nil] at he
  omega
/-- Prepared allowance charges the actual pair copy and every generic-filter instruction. -/
def preparedBound (bits key : List Bool) : Nat :=5*(pairTape bits).length+
  SemiprimeD1StackOwnerFibreBounds.runBound key ((P.rows bits).map SemiprimeD1FactorScopePairEncoding.pair)+6
/-- Same fixed program's prepared trace including its literal final halt. -/
theorem prepared_time_le (bits key : List Bool) : preparedTime bits key+1≤preparedBound bits key := by
  have h:=SemiprimeD1StackOwnerFibreBounds.time_le key ((P.rows bits).map SemiprimeD1FactorScopePairEncoding.pair)
  unfold preparedTime preparedBound
  omega
/-- Whole input-width/query-width polynomial, with neither scope count nor elapsed clock supplied. -/
def runBound (bits key : List Bool) : Nat :=10^122*(key.length+1)*(bits.length+1)^30
/-- All actual source/copy/scan/emission clocks are retained in one explicit bound. -/
theorem timeBound_le (bits key : List Bool) (hb : bits≠[]) : timeBound bits key≤runBound bits key := by
  let K:=key.length+1
  let W:=(bits.length+1)^30
  have hK:1≤K:=by dsimp [K];omega
  have hW:1≤W:=Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos _))
  have hL:(pairTape bits).length≤10^114*W+1:=pair_bytes bits hb
  have hF:=SemiprimeD1StackOwnerFibreBounds.time_le key ((P.rows bits).map SemiprimeD1FactorScopePairEncoding.pair)
  change SemiprimeD1StackOwnerFibreExecution.totalTime key _≤100*K*((pairTape bits).length+1) at hF
  have hm:=Nat.mul_le_mul_left (100*K) (Nat.add_le_add_right hL 1)
  have hKW:K≤K*W:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left K hW
  have hWK:W≤K*W:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right W hK
  unfold timeBound preparedTime SemiprimeD1StackFactorScopePairBounds.runBound runBound
  change 10^118*W+(5*(pairTape bits).length+SemiprimeD1StackOwnerFibreExecution.totalTime key _+5)+2≤10^122*K*W
  nlinarith
/-- Complete binary N plus actually acquired physical key, on the same137-role machine. -/
noncomputable def machineFibre (bits key : List Bool) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits key))
      (some (SemiprimeD1StackCalls.configuration (done bits key))) (runBound bits key) := by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output Label.main program
  let h:=source_run bits key hb
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1.trans (timeBound_le bits key hb)⟩
/-- Prepared actual-machine certificate: source already acquired, never silently initialized. -/
def preparedMachineFibre (bits key : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (⟨some .copy,none,none,afterSource bits key,[]⟩ : C.State Stack Label))
      (some (SemiprimeD1StackCalls.configuration (done bits key))) (preparedBound bits key) := by
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output Label.main program
  exact ⟨⟨preparedTime bits key+1,prepared_run bits key⟩,prepared_time_le bits key⟩
/-- Physical initial role widths include both genuine binary input words. -/
theorem initial_length (bits key : List Bool) (k : Stack) :
    ((initial bits key).data k).length≤bits.length+key.length := by
  have hf (j : F.Stack) : ((F.initial key []).data j).length≤key.length:=by
    rcases j with j|j <;> cases j <;>
      simp [SemiprimeD1StackOwnerFibre.initial,SemiprimeD1StackOwnerFibre.data,SemiprimeD1StackAdder.store]
  cases k with
  | inl k=>
    change (P.input bits k).length≤_
    rw [SemiprimeD1StackFactorScopePairExecution.input_eq]
    dsimp only
    split <;> simp
  | inr k=>cases k with
    | inl k=>have h:=hf k;change ((F.initial key []).data k).length≤_;omega
    | inr k=>exact Nat.zero_le _
/-- Actual successful prefixes cannot continue beyond the proved whole-source halt. -/
theorem prefix_fuel_le (bits key : List Bool) (hb : bits≠[]) (fuel : Nat) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits key)=some out) : fuel≤runBound bits key := by
  obtain ⟨t,ht,he⟩:=source_run bits key hb
  have hf:fuel≤t:=by
    by_contra hn
    have h:fuel=t+(1+(fuel-(t+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done bits key)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans (ht.trans (timeBound_le bits key hb))
/-- Every source/cache/copy/filter/shadow role and every actual nested return cell. -/
theorem prefix_cells (bits key : List Bool) (hb : bits≠[]) (fuel : Nat) (out : C.State Stack Label)
    (hr : C.run program fuel (initial bits key)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤138*(bits.length+key.length+runBound bits key) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel (bits.length+key.length) _ out
    (initial_length bits key) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤137*(bits.length+key.length+fuel):=by
    calc
      _≤∑_k:Stack,(bits.length+key.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits key hb fuel out hr
  omega
/-- Identical complete physical inventory for the actual compiled finite machine. -/
theorem machine_prefix_cells (bits key : List Bool) (hb : bits≠[]) (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits key)))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤138*(bits.length+key.length+runBound bits key) := by
  have he:=SemiprimeD1StackCalls.run_correct originalInput output Label.main program fuel (initial bits key)
  have hh:=he.trans hr
  cases hs:C.run program fuel (initial bits key) with
  | none=>rw [hs] at hh;cases hh
  | some out=>
    rw [hs] at hh
    have hc:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits key hb fuel out hs
/-- Actual bounded-ordinal factor query widths follow from the original catalogue,
not from a caller-supplied count or a binary/unary identification. -/
theorem factor_count_le (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits) :
    SemiprimePublicAcquiredExecution.factorCount (SemiprimeBitArithmetic.bitValue bits)≤
      2000000000000000*(bits.length+1)^5 := by
  have hb:bits≠[]:=by intro h;rw [h] at hN;exact Nat.lt_irrefl _ hN
  have hv:=SemiprimeD1StackPortCataloguePolynomial.vertices_le_tape (SemiprimeD1StackPortCatalogueExecution.vertices bits)
  have hs:=SemiprimeD1StackPortCatalogueBounds.size_le bits hb
  have he:(SemiprimeD1StackPortCatalogueExecution.vertices bits).length=
      SemiprimePublicAcquiredExecution.factorCount (SemiprimeBitArithmetic.bitValue bits) := by
    unfold SemiprimeD1StackPortCatalogueExecution.vertices SemiprimePublicAcquiredExecution.factorCount
      SemiprimePublicAcquiredExecution.vertexEnumeration
    rw [SemiprimeD1StackVertexCatalogueTags.digitCount_raw bits hb,
      SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc]
  unfold SemiprimeD1StackPortCataloguePolynomial.size at hs
  rw [he] at hv
  omega
/-- Whole actual N+original-factor-key source is polynomial in original binary width. -/
theorem original_timeBound (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<SemiprimeBitArithmetic.bitValue bits)
    (f : Fin (SemiprimePublicAcquiredExecution.factorCount (SemiprimeBitArithmetic.bitValue bits))) :
    runBound bits (SemiprimeD1FactorScopePairOriginal.key f.val)≤10^140*(bits.length+1)^35 := by
  have hf:=factor_count_le bits hc hN
  have hp:1≤(bits.length+1)^5:=Nat.succ_le_of_lt (Nat.pow_pos (Nat.succ_pos _))
  have hk:(SemiprimeD1FactorScopePairOriginal.key f.val).length+1≤
      2000000000000001*(bits.length+1)^5:=by
    simp only [SemiprimeD1FactorScopePairOriginal.key,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
    have hi:=f.isLt
    omega
  unfold runBound
  calc
    _ ≤ 10^122*(2000000000000001*(bits.length+1)^5)*(bits.length+1)^30 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk)
    _ = (10^122*2000000000000001)*((bits.length+1)^5*(bits.length+1)^30) :=by ring
    _ ≤ 10^140*((bits.length+1)^5*(bits.length+1)^30) :=Nat.mul_le_mul_right _ (by norm_num)
    _ = _ :=by rw [←pow_add]
end RiemannGaussian.SemiprimeD1StackFactorScopeFibreBounds
