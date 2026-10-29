/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogueBounds
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueResources
open SemiprimeD1StackOwnerCatalogue SemiprimeD1StackOwnerCatalogueBounds
open SemiprimeBitArithmetic (bitValue)
/-- All 149 physical Boolean roles, including retained source/ID banks and actual work. -/
theorem stack_card : Fintype.card Stack=149 := by decide
/-- Initial data consists only of original binary N, before any tape/dimension/ID acquisition. -/
theorem initial_length (bits:List Bool) (k:Stack) : (input bits k).length≤bits.length := by
  rcases k with k|k
  · exact SemiprimeD1StackOwnerCatalogueOriginalBounds.source_input_length bits k
  · exact Nat.zero_le _
/-- Actual successful source prefixes cannot pass this SAME N-only source's proved halt. -/
theorem prefix_fuel (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label) (hr:C.run program fuel (initial bits)=some out) :
    fuel≤polynomial bits.length := by
  obtain ⟨time,ht,he⟩:=source_run_polynomial bits hc hN
  have hf:fuel≤time:=by
    by_contra hn
    have hh:fuel=time+(1+(fuel-(time+1))):=by omega
    rw [hh,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,
      SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (SemiprimeD1StackOwnerCatalogueExecution.done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- EVERY actual source prefix counts all 149 Boolean words and all real return frames. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label) (hr:C.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤150*(bits.length+polynomial bits.length) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ _ (initial_length bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤149*(bits.length+fuel):=by
    calc
      _≤∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel bits hc hN fuel out hr
  omega
/-- The actual source's initial tape equals the ordinary single-input finite-machine convention. -/
theorem input_single (bits:List Bool) : input bits=fun k=>if k=originalInput then bits else [] := by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · change SemiprimeD1StackVertexCatalogue.input bits k=_
        rw [SemiprimeD1StackEdgeCatalogueExecution.cat_input]
        simp only [originalInput,source,S.originalInput,S.edgeStack,SemiprimeD1StackEdgeCatalogue.catStack,
          Sum.inl.injEq]
      · rfl
    · rcases k with k|k <;> rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k <;> rfl
/-- The genuine compiled machine starts from binary N alone. -/
theorem initial_eq (bits:List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have he:initial bits=SemiprimeD1StackCalls.initial originalInput (.local .main) bits:=by
    unfold initial SemiprimeD1StackCalls.initial
    rw [input_single]
  rw [he]
  exact (SemiprimeD1StackCalls.initial_correct originalInput (aux .output) (.local .main) program bits).symm
/-- SAME actual polynomial source clock as a genuine finite-machine execution certificate. -/
noncomputable def catalogueInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (SemiprimeD1StackOwnerCatalogueExecution.done bits)))
      (polynomial bits.length) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput (aux .output) (.local .main) program
  let cert:=source_run_polynomial bits hc hN
  exact ⟨⟨Classical.choose cert,(Classical.choose_spec cert).2⟩,(Classical.choose_spec cert).1⟩
/-- EVERY genuine compiled-machine prefix retains the SAME all-role and return-cell bound. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤150*(bits.length+polynomial bits.length) := by
  have he:=SemiprimeD1StackCalls.run_correct originalInput (aux .output) (.local .main) program fuel (initial bits)
  change (C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=
    (fun q=>q.bind machine.step)^[fuel] (some (SemiprimeD1StackCalls.configuration (initial bits))) at he
  have hh:(C.run program fuel (initial bits)).map SemiprimeD1StackCalls.configuration=some cfg:=
    he.trans ((congrArg (fun start:machine.Cfg=>
      (fun q:Option machine.Cfg=>q.bind machine.step)^[fuel] (some start)) (initial_eq bits).symm).trans hr)
  cases hout:C.run program fuel (initial bits) with
  | none=>rw [hout] at hh;cases hh
  | some out=>
    rw [hout] at hh
    have hcfg:SemiprimeD1StackCalls.configuration out=cfg:=Option.some.inj hh
    subst cfg
    exact prefix_cells bits hc hN fuel out hout
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueResources
