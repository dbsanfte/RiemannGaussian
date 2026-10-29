/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCataloguePolynomial
/-! # Actual original-N clock and all-prefix memory of the complete physical port source -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueBounds
open SemiprimeD1StackPortCatalogue SemiprimeD1StackPortCatalogueExecution
open SemiprimeD1StackPortCataloguePolynomial
open SemiprimeMacroParameters
/-- Original source dimensions and acquired byte tape yield the actual scalar cap. -/
theorem size_le (bits:List Bool) (hb:bits≠[]) : size (vertices bits)≤2000000000000000*(bits.length+1)^5 := by
  have hT:=SemiprimeD1StackEdgeCatalogueBounds.tape_bytes bits hb
  have hR:transformLength bits.length≤64*bits.length+1:=
    (SemiprimeD1StackTransformArithmetic.prefix_powers bits.length (transformExponent bits.length) (le_refl _)).1
  have hP:firstAxis bits.length≤transformLength bits.length:=
    Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
  have hQ:secondAxis bits.length≤transformLength bits.length:=by
    rw [secondAxis_eq_power]
    exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have hD:SemiprimeD1StackVertexCatalogueCaches.digitCountValue bits≤transformLength bits.length:=by
    rw [SemiprimeD1StackVertexCatalogueTags.digitCount_raw bits hb]
    exact ((digitCount_bounds (List.length_pos_iff.mpr hb)).2).trans (Nat.div_le_self _ 4)
  have hpow:bits.length+1≤(bits.length+1)^5:=Nat.le_pow (by omega)
  unfold size vertices
  rw [axes_product]
  change (SemiprimeD1EdgeCatalogueEncoding.tape (SemiprimeD1StackEdgeCatalogueExecution.records bits) []).length+
    (transformLength bits.length+1)+firstAxis bits.length+secondAxis bits.length+
    SemiprimeD1StackVertexCatalogueCaches.digitCountValue bits+1≤_
  omega
/-- The WHOLE actual source has a fixed original-input polynomial transition bound. -/
theorem budget_le (bits:List Bool) (hb:bits≠[]) : budget bits≤10^100*(bits.length+1)^30 := by
  have hT:=SemiprimeD1StackEdgeCatalogueBounds.tape_bytes bits hb
  have hs:=size_le bits hb
  have hres:=original_resources (vertices bits)
  have hp:1≤(bits.length+1)^30:=by
    have h:(0:ℕ)<(bits.length+1)^30:=by positivity
    omega
  have h5:(bits.length+1)^5≤(bits.length+1)^30:=Nat.pow_le_pow_right (by omega) (by omega)
  have hs6:(size (vertices bits))^6≤2000000000000000^6*(bits.length+1)^30:=by
    simpa only [mul_pow,←pow_mul] using Nat.pow_le_pow_left hs 6
  unfold budget
  omega
/-- No graph, arity, tally, port list, resource or truth answer is a runtime input. -/
theorem source_run_polynomial (bits:List Bool) (hb:bits≠[]) :
    ∃ time ≤ 10^100*(bits.length+1)^30,C.run program time (initial bits)=some (done bits) := by
  obtain ⟨m,hm,hr⟩:=source_run bits hb
  exact ⟨m,hm.trans (budget_le bits hb),hr⟩
/-- Successful executed prefixes cannot pass the actual proved final halt. -/
theorem prefix_fuel_le (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) : fuel≤10^100*(bits.length+1)^30 := by
  obtain ⟨time,ht,he⟩:=source_run_polynomial bits hb
  have hf:fuel≤time:=by
    by_contra hn
    have h:fuel=time+(1+(fuel-(time+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- ALL seventy-eight Boolean stacks and real return frames at EVERY actual source prefix. -/
theorem prefix_cells (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤10^103*(bits.length+1)^30 := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out (by
    intro k
    rcases k with (k|k)|k
    · change (SemiprimeD1StackVertexCatalogue.input bits k).length≤bits.length
      rw [SemiprimeD1StackEdgeCatalogueExecution.cat_input]
      split <;> simp
    · exact Nat.zero_le _
    · exact Nat.zero_le _) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤78*(bits.length+fuel):=by
    calc
      _≤∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hb fuel out hr
  have hn:bits.length≤(bits.length+1)^30:=by
    have h:bits.length+1≤(bits.length+1)^30:=by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1≤bits.length+1 by omega) (show 1≤30 by omega)
    omega
  omega
/-- ALL actual compiled-machine prefixes start from initList of binary N alone. -/
theorem machine_prefix_cells (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤10^103*(bits.length+1)^30 := by
  have he:=SemiprimeD1StackCalls.run_correct (originalInput) (aux .output) (.local .main)
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
/-- Actual finite-machine full-acquisition certificate, rather than a reported-cost assumption. -/
noncomputable def portCatalogueInTime (bits:List Bool) (hb:bits≠[]) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (10^100*(bits.length+1)^30) := by
  rw [initial_eq bits]
  apply SemiprimeD1StackCalls.evalsCorrect (originalInput) (aux .output) (.local .main) program
  let cert:=source_run_polynomial bits hb
  let m:=Classical.choose cert
  have hs:=Classical.choose_spec cert
  exact ⟨⟨m,hs.2⟩,hs.1⟩
end RiemannGaussian.SemiprimeD1StackPortCatalogueBounds
