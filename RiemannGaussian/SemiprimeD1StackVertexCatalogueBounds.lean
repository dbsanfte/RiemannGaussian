/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexCatalogueExecution

/-! # Actual complete vertex-catalogue resource bounds
All cache sizes below come from the executed original-input acquisition.
Ports, edge identifiers and checkers are separate subsequent stages.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 4096
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexCatalogueBounds
open SemiprimeD1StackVertexCatalogue SemiprimeD1StackVertexCatalogueExecution
open SemiprimeD1StackVertexCatalogueCaches SemiprimeD1StackVertexCatalogueTags
open SemiprimeMacroParameters

/-- Actual retained digit bytes are bounded by the proved executed source storage. -/
theorem cache_bytes (bits:List Bool) (hb:bits≠[]) :
    (SemiprimeD1TensorTapeCodec.vectorBits (SemiprimeD1StackDigitCountBounds.originalWords bits)).length≤
      24000000*(bits.length+1)^2 := by
  obtain ⟨time,_,hr⟩:=SemiprimeD1BinaryPublicAcquisitionExecution.source_run bits hb
  have hs:=SemiprimeD1BinaryPublicAcquisitionBounds.prefix_cells bits hb time _ hr
  have hk:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset SemiprimeD1BinaryPublicAcquisition.Stack))=>
    Nat.zero_le ((SemiprimeD1BinaryPublicAcquisitionComponents.result bits k).length))
    (Finset.mem_univ SemiprimeD1StackDigitCountBounds.bankRole)
  change (SemiprimeD1BinaryPublicAcquisitionComponents.result bits SemiprimeD1StackDigitCountBounds.bankRole).length≤_
  exact hk.trans (by simpa using hs)

/-- Pure arithmetic substitution, isolated from executable configurations. -/
theorem numeric_budget (n R d bytes:ℕ) (hR:R≤64*n+1) (hd:d≤R)
    (hb:bytes≤24000000*(n+1)^2) :
    1+(800000*(n+1)^2+1)+(11*bytes+5+1)+(5*R+5*d+16)+18+
      18*(24*(64*n+3)+43*(64*n+21)^5+22)+1≤10000000000000*(n+1)^5 := by
  have hp:(64*n+21)^5≤4437053125*(n+1)^5 := by
    calc
      _≤(85*(n+1))^5:=Nat.pow_le_pow_left (by omega) 5
      _= _:=by rw [mul_pow];norm_num
  have h2:(n+1)^2≤(n+1)^5:=Nat.pow_le_pow_right (by omega) (by omega)
  have hn:n≤(n+1)^5:=by
    have h1:n+1≤(n+1)^5:=by simpa using (Nat.pow_le_pow_right (by omega : 1≤n+1) (by omega : 1≤5))
    omega
  have hpos:1≤(n+1)^5:=by
    have h:(0:ℕ)<(n+1)^5:=by positivity
    omega
  omega

/-- Fixed polynomial bound for the WHOLE actually executed original-input producer. -/
theorem budget_le (bits:List Bool) (hb:bits≠[]) : budget bits≤10000000000000*(bits.length+1)^5 := by
  have hr:transformLength bits.length≤64*bits.length+1:=
    (SemiprimeD1StackTransformArithmetic.prefix_powers bits.length (transformExponent bits.length) (le_refl _)).1
  have hd:digitCountValue bits≤transformLength bits.length:=by
    rw [digitCount_raw bits hb]
    exact ((digitCount_bounds (List.length_pos_iff.mpr hb)).2).trans (Nat.div_le_self _ _)
  have hc:=SemiprimeD1StackDigitCountExecution.totalTime_le (SemiprimeD1StackDigitCountBounds.originalWords bits)
  have hn:=numeric_budget bits.length (transformLength bits.length) (digitCountValue bits) _ hr hd (cache_bytes bits hb)
  unfold budget SemiprimeD1BinaryPublicAcquisitionExecution.timeBound SemiprimeD1StackVertexCatalogueModes.blockBudget
  simp only [show 64*bits.length+3+18=64*bits.length+21 by omega]
  omega

/-- Real complete producer trace with no resource-answer premise. -/
theorem source_run_polynomial (bits:List Bool) (hb:bits≠[]) :
    ∃m≤10000000000000*(bits.length+1)^5,C.run program m (initial bits)=some (done bits) := by
  obtain ⟨m,hm,hr⟩:=source_run bits hb
  exact ⟨m,hm.trans (budget_le bits hb),hr⟩

/-- Successful actual source prefixes cannot run beyond the proved final halt. -/
theorem prefix_fuel_le (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) : fuel≤10000000000000*(bits.length+1)^5 := by
  obtain ⟨time,ht,he⟩:=source_run_polynomial bits hb
  have hf:fuel≤time:=by
    by_contra hn
    have h:fuel=time+(1+(fuel-(time+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht

/-- All fifty-three actual Boolean stacks and actual return frames at EVERY executed prefix. -/
theorem prefix_cells (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤1000000000000000*(bits.length+1)^5 := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out (by
    intro k
    rcases k with k|k
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> simp only [initial,input,Root.input,SemiprimeD1BinaryPublicAcquisition.store,
            SemiprimeD1BinaryDigitAcquisition.input,SemiprimeD1BinaryDigitAcquisition.store,
            SemiprimeD1StackTransform.input,Sum.elim_inl,List.length_nil] <;> omega
        · rcases k with k|k <;> exact Nat.zero_le _
      · rcases k with k|k <;> exact Nat.zero_le _
    · exact Nat.zero_le _) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤53*(bits.length+fuel):=by
    calc
      _≤∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hb fuel out hr
  have hn:bits.length≤(bits.length+1)^5:=by
    have hh:bits.length+1≤(bits.length+1)^5:=by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1≤bits.length+1 by omega) (show 1≤5 by omega)
    omega
  omega

/-- Compiled finite-machine storage starts from binary N alone. -/
theorem machine_prefix_cells (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤1000000000000000*(bits.length+1)^5 := by
  have he:=SemiprimeD1StackCalls.run_correct originalInput (kernelStack (Kernel.aux 2)) (.inl .main)
    program fuel (initial bits)
  change (C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial bits))) at he
  have hh:(C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=some cfg:=
    he.trans ((congrArg (fun start:machine.Cfg=>
      (fun q:Option machine.Cfg=>q.bind machine.step)^[fuel] (some start)) (initial_eq bits).symm).trans hr)
  cases hc:C.run program fuel (initial bits) with
  | none => rw [hc] at hh;cases hh
  | some out =>
    rw [hc] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hb fuel out hc

/-- Actual complete finite-machine certificate, not a retained-report cost assumption. -/
noncomputable def catalogueInTime (bits:List Bool) (hb:bits≠[]) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (10000000000000*(bits.length+1)^5) := by
  rw [initial_eq bits]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput (kernelStack (Kernel.aux 2)) (.inl .main) program
  let cert:=source_run_polynomial bits hb
  let m:=Classical.choose cert
  have hs:=Classical.choose_spec cert
  exact ⟨⟨m,hs.2⟩,hs.1⟩
end RiemannGaussian.SemiprimeD1StackVertexCatalogueBounds

