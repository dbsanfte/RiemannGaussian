/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackEdgeCatalogueExecution

/-! # Original-input transition and all-prefix storage bounds for full half edges
The input tape bound is derived from the executed original catalogue, not
supplied as a graph/descriptor/count/resource answer.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackEdgeCatalogueBounds
open SemiprimeD1StackEdgeCatalogue SemiprimeD1StackEdgeCatalogueExecution
open SemiprimeD1StackEdgeCatalogueView

/-- Actual acquired source-tape bytes are bounded at its proved executed halt. -/
theorem tape_bytes (bits:List Bool) (hb:bits≠[]) :
    (SemiprimeD1EdgeCatalogueEncoding.tape (records bits) []).length≤1000000000000000*(bits.length+1)^5 := by
  obtain ⟨time,_,hr⟩:=SemiprimeD1StackVertexCatalogueBounds.source_run_polynomial bits hb
  have hs:=SemiprimeD1StackVertexCatalogueBounds.prefix_cells bits hb time _ hr
  have hk:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset Cat.Stack))=>
    Nat.zero_le ((SemiprimeD1StackVertexCatalogueExecution.result bits k).length)) (Finset.mem_univ sourceReader)
  have hd:afterCat bits reader=SemiprimeD1EdgeCatalogueEncoding.tape (records bits) []:=by
    rw [afterCat_clean]
    exact store_reader _ _ _ _
  change SemiprimeD1StackVertexCatalogueExecution.result bits sourceReader=_ at hd
  rw [←hd]
  change (∑k:Cat.Stack,(SemiprimeD1StackVertexCatalogueExecution.result bits k).length)+0≤
    1000000000000000*(bits.length+1)^5 at hs
  exact hk.trans (by simpa only [Nat.add_zero] using hs)
/-- Whole-source bound is a fixed polynomial in original binary input width. -/
theorem budget_le (bits:List Bool) (hb:bits≠[]) : budget bits≤1000000000000000000*(bits.length+1)^5 := by
  have hd:=tape_bytes bits hb
  have hp:1≤(bits.length+1)^5:=by
    have h:(0:ℕ)<(bits.length+1)^5:=by positivity
    omega
  unfold budget
  omega
/-- The WHOLE actual edge producer, without source/count/resource advice. -/
theorem source_run_polynomial (bits:List Bool) (hb:bits≠[]) :
    ∃m≤1000000000000000000*(bits.length+1)^5,C.run program m (initial bits)=some (done bits) := by
  obtain ⟨m,hm,hr⟩:=source_run bits hb
  exact ⟨m,hm.trans (budget_le bits hb),hr⟩
/-- Successful executed prefixes cannot pass the actual proved final halt. -/
theorem prefix_fuel_le (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) : fuel≤1000000000000000000*(bits.length+1)^5 := by
  obtain ⟨time,ht,he⟩:=source_run_polynomial bits hb
  have hf:fuel≤time:=by
    by_contra hn
    have h:fuel=time+(1+(fuel-(time+1))):=by omega
    rw [h,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (done bits)=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- ALL sixty-seven Boolean stacks and real return frames at EVERY actual source prefix. -/
theorem prefix_cells (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (out:C.State Stack Label)
    (hr:C.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤100000000000000000000*(bits.length+1)^5 := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ out (by
    intro k
    rcases k with k|k
    · change (SemiprimeD1StackVertexCatalogue.input bits k).length≤bits.length
      rw [cat_input]
      split <;> simp
    · exact Nat.zero_le _) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ out hr
  change out.frames.length≤0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤67*(bits.length+fuel):=by
    calc
      _≤∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _= _:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel_le bits hb fuel out hr
  have hn:bits.length≤(bits.length+1)^5:=by
    have h:bits.length+1≤(bits.length+1)^5:=by
      simpa only [pow_one] using Nat.pow_le_pow_right (show 1≤bits.length+1 by omega) (show 1≤5 by omega)
    omega
  omega
/-- ALL actual compiled-machine prefixes start from initList of binary N alone. -/
theorem machine_prefix_cells (bits:List Bool) (hb:bits≠[]) (fuel:ℕ) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤100000000000000000000*(bits.length+1)^5 := by
  have he:=SemiprimeD1StackCalls.run_correct (catStack Cat.originalInput) (aux .output) (.inl .main)
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
noncomputable def edgeCatalogueInTime (bits:List Bool) (hb:bits≠[]) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (done bits))) (1000000000000000000*(bits.length+1)^5) := by
  rw [initial_eq bits]
  apply SemiprimeD1StackCalls.evalsCorrect (catStack Cat.originalInput) (aux .output) (.inl .main) program
  let cert:=source_run_polynomial bits hb
  let m:=Classical.choose cert
  have hs:=Classical.choose_spec cert
  exact ⟨⟨m,hs.2⟩,hs.1⟩
/-- The same original metadata/digit cache survives the entire edge acquisition. -/
theorem retained_root (bits:List Bool) (k:SemiprimeD1BinaryPublicAcquisition.Stack) :
    result bits (catStack (SemiprimeD1StackVertexCatalogue.rootStack k))=
      SemiprimeD1BinaryPublicAcquisitionComponents.result bits k := by
  change SemiprimeD1StackVertexCatalogueExecution.result bits (SemiprimeD1StackVertexCatalogue.rootStack k)=_
  exact SemiprimeD1StackVertexCatalogueExecution.retained_root bits k
end RiemannGaussian.SemiprimeD1StackEdgeCatalogueBounds
