/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductCheckExecution

/-! # Whole product-checker bit-time and complete physical inventory
These bounds count the SAME actual raw-input checker, including acquisition,
guarding, every parser call, arithmetic, comparison, cleanup and real returns.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackProductCheckBounds
open SemiprimeD1StackProductCheck SemiprimeD1StackProductCheckAcquisition
open SemiprimeD1StackProductCheckParse SemiprimeD1StackProductCheckExecution

/-- All three physically acquired words have exactly the actual cache width. -/
theorem word_lengths (raw cached : List Bool) :
    (first raw cached).length=cached.length ∧ (second raw cached).length=cached.length ∧
      (third raw cached).length=cached.length :=
  ⟨SemiprimeD1StackWordBlockExecution.result_length raw cached,
    SemiprimeD1StackWordBlockExecution.result_length _ cached,
    SemiprimeD1StackWordBlockExecution.result_length _ cached⟩
/-- The guarded family is exactly the actual three parser payloads. -/
theorem words_three (raw cached : List Bool) :
    SemiprimeD1StackProductCheckGuard.words raw cached=[first raw cached,second raw cached,third raw cached] := rfl
/-- Literal framing overhead is paid in the acquired vector size. -/
theorem vector_length (raw cached : List Bool) :
    (SemiprimeD1TensorTapeCodec.vectorBits (SemiprimeD1StackProductCheckGuard.words raw cached)).length=
      6*cached.length+7 := by
  obtain ⟨h0,h1,h2⟩:=word_lengths raw cached
  rw [words_three]
  simp only [SemiprimeD1TensorTapeCodec.vectorBits,List.length_cons,List.length_nil,
    SemiprimeSourceHistogramKeyBits.frame_length,h0,h1,h2]
  omega
/-- One fixed cubic before all binary word values bounds every actual branch. -/
def runBound (raw cached : List Bool) : ℕ := 1000000*(raw.length+cached.length+3)^3

/-- Complete actual source budget is polynomial in PHYSICAL input lengths,
including arbitrary zero modulus words and incomplete raw assignments. -/
theorem timeBound_le (raw cached : List Bool) : timeBound raw cached≤runBound raw cached := by
  let u:=raw.length+cached.length+3
  have hu : 1≤u := by dsimp [u];omega
  have h1p : u≤u^3 := by simpa only [pow_one] using Nat.pow_le_pow_right hu (by decide : 1≤3)
  have h2p : u^2≤u^3 := Nat.pow_le_pow_right hu (by decide : 2≤3)
  obtain ⟨h0,h1,h2⟩:=word_lengths raw cached
  have hw : SemiprimeD1StackWordVectorExecution.timeBound raw cached countWord≤500*u := by
    unfold SemiprimeD1StackWordVectorExecution.timeBound
    change 100*(raw.length+(3+1)*(cached.length+1)+1)≤500*u
    dsimp [u];omega
  have hg:=SemiprimeD1StackVectorCanonicalBounds.timeBound_le
    (SemiprimeD1StackProductCheckGuard.words raw cached) cached
  rw [vector_length] at hg
  have hgb : 200*(6*cached.length+7+cached.length+1)^2≤12800*u^2 := by
    calc
      _ ≤ 200*(8*u)^2 := Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (by dsimp [u];omega) 2)
      _ = _ := by ring
  have hguard:=hg.trans hgb
  have hm:=(SemiprimeD1StackResidueMulBounds.totalTime_le (first raw cached) (second raw cached) cached).trans
    (SemiprimeD1StackResidueMulBounds.timeBound_le_cube _ _ _)
  rw [h0,h1] at hm
  have hmb : 10000*(cached.length+cached.length+cached.length+3)^3≤270000*u^3 := by
    calc
      _ ≤ 10000*(3*u)^3 := Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left (by dsimp [u];omega) 3)
      _ = _ := by ring
  have hmul:=hm.trans hmb
  have he:=SemiprimeD1StackWordEqualExecution.executionTime_le
    (SemiprimeD1StackProductCheckCompute.residue raw cached) (third raw cached)
  have hr : (SemiprimeD1StackProductCheckCompute.residue raw cached).length=cached.length :=
    SemiprimeD1StackResidueMulBounds.residue_width _ _ cached
  rw [hr,h2] at he
  have hp : parseTime raw cached≤30*u := by
    simp only [parseTime,h0,h1,h2]
    dsimp [u];omega
  have hv : (SemiprimeD1StackWordVectorExecution.result raw cached countWord).length=6*cached.length+7 :=
    vector_length raw cached
  change _≤1000000*u^3
  unfold timeBound SemiprimeD1StackProductCheckReject.rejectBudget SemiprimeD1StackProductCheckCompute.computeBudget
  rw [hv]
  have huM : cached.length≤u := by dsimp [u];omega
  omega

/-- Actual completed checker trace with a fixed physical-input cubic clock. -/
theorem source_run_bounded (raw cached : List Bool) :
    ∃t≤runBound raw cached,C.run program t (initial raw cached)=some (done raw cached) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackProductCheckExecution.source_run raw cached
  exact ⟨t,ht.trans (timeBound_le raw cached),hr⟩
/-- A proof-side trace choice, never an executing elapsed-count operand. -/
noncomputable def sourceCheck (raw cached : List Bool) :
    StateTransition.EvalsToInTime (C.step program) (initial raw cached) (some (done raw cached)) (runBound raw cached) := by
  let h:=source_run_bounded raw cached
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- The genuine fixed FinTM2 has the SAME whole input/output/clock theorem. -/
noncomputable def machineCheck (raw cached : List Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial raw cached))
      (some (SemiprimeD1StackCalls.configuration (done raw cached))) (runBound raw cached) :=
  SemiprimeD1StackCalls.evalsCorrect rawInput output Label.start program _ _ _ (sourceCheck raw cached)

/-- Every successful prefix lies before the actual complete halt. -/
theorem prefix_fuel_le (raw cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial raw cached)=some out) : fuel≤runBound raw cached := by
  obtain ⟨t,ht,hh⟩:=source_run_bounded raw cached
  have hf : fuel≤t := by
    by_contra hn
    have he : fuel=t+(1+(fuel-(t+1))) := by omega
    rw [he,SemiprimeD1StackReturnLink.run_add,hh,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz : C.run program 1 (done raw cached)=none := rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- All48 Boolean stack roles AND every real return label are counted at EVERY
actual prefix, including the retained original input/cache/unread suffix. -/
theorem prefix_cells (raw cached : List Bool) (fuel : ℕ) (out : C.State Stack Label)
    (hr : C.run program fuel (initial raw cached)=some out) :
    (∑k : Stack,(out.data k).length)+out.frames.length≤
      49*(raw.length+cached.length+runBound raw cached) := by
  let I:=raw.length+cached.length
  have hi : ∀k,((initial raw cached).data k).length≤I := by
    intro k
    change (input raw cached k).length≤I
    unfold input
    split
    · dsimp [I];omega
    · split
      · dsimp [I];omega
      · exact Nat.zero_le _
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel I _ out hi hr
  have ht:=prefix_fuel_le raw cached fuel out hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs : (∑k : Stack,(out.data k).length)≤48*(I+fuel) := by
    calc
      _ ≤ ∑_k : Stack,(I+fuel) := Finset.sum_le_sum (fun k _=>hd k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  change _≤49*(I+runBound raw cached)
  omega
/-- Same complete inventory on the actual finite machine configuration. -/
theorem machine_prefix_cells (raw cached : List Bool) (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial raw cached)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      49*(raw.length+cached.length+runBound raw cached) := by
  have he:=SemiprimeD1StackCalls.run_correct rawInput output Label.start program fuel (initial raw cached)
  change (C.run program fuel (initial raw cached)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial raw cached))) at he
  have hh:=he.trans hr
  cases hc:C.run program fuel (initial raw cached) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg : SemiprimeD1StackCalls.configuration out=cfg := Option.some.inj hh
    subst cfg
    exact prefix_cells raw cached fuel out hc

end RiemannGaussian.SemiprimeD1StackProductCheckBounds
