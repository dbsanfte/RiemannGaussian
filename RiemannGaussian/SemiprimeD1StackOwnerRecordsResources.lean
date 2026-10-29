/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerRecordsBounds
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerRecordsResources
open SemiprimeD1StackOwnerRecords SemiprimeD1StackOwnerRecordsBounds
open SemiprimeBitArithmetic (bitValue)
/-- Every initially present physical word is bounded by original binary N's actual bit length. -/
theorem initial_length (bits:List Bool) (k:Stack) : ((initial bits).data k).length≤ bits.length := by
  rcases k with k|k
  · exact SemiprimeD1StackOwnerFibreCatalogueResources.initial_length bits k
  · rcases k with k|k
    · exact Nat.zero_le _
    · cases k <;> exact Nat.zero_le _
/-- No actual successful prefix passes the SAME routing source's actual proved final halt. -/
theorem prefix_fuel (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label) (hr:C.run program fuel (initial bits)=some out) :
    fuel≤ polynomial bits.length := by
  obtain ⟨time,ht,he⟩:=source_run_polynomial bits hc hN
  have hf:fuel≤ time:=by
    by_contra hn
    have hh:fuel=time+(1+(fuel-(time+1))):=by omega
    rw [hh,SemiprimeD1StackReturnLink.run_add,he,Option.bind_some,SemiprimeD1StackReturnLink.run_add] at hr
    have hz:C.run program 1 (SemiprimeD1StackOwnerRecordsExecution.done bits hN [] [])=none:=rfl
    rw [hz,Option.bind_none] at hr
    cases hr
  exact hf.trans ht
/-- EVERY original-N source prefix counts ALL344 physical Boolean roles and ALL actual return cells. -/
theorem prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (out:C.State Stack Label) (hr:C.run program fuel (initial bits)=some out) :
    (∑k:Stack,(out.data k).length)+out.frames.length≤ 345*(bits.length+polynomial bits.length) := by
  have hd:=SemiprimeD1StackReturnLink.run_data_bound program fuel bits.length _ _ (initial_length bits) hr
  have hf:=SemiprimeD1StackCalls.run_frame_bound program fuel _ _ hr
  change out.frames.length≤ 0+fuel at hf
  have hs:(∑k:Stack,(out.data k).length)≤ 344*(bits.length+fuel):=by
    calc
      _≤ ∑_k:Stack,(bits.length+fuel):=Finset.sum_le_sum (fun k _=>hd k)
      _=_:=by simp only [Finset.sum_const,Finset.card_univ,stack_card,smul_eq_mul]
  have ht:=prefix_fuel bits hc hN fuel out hr
  omega
/-- Literal standard initialization contains original binary N alone. -/
theorem input_single (bits:List Bool) :
    data (S.input bits) (fun _=>[]) (rowAux [] [])=fun k=>if k=originalInput then bits else []:=by
  funext k;rcases k with k|k
  · simp only [data,Sum.elim_inl,SemiprimeD1StackOwnerFibreCatalogueResources.input_single,
      originalInput,source,Sum.inl.injEq]
  · rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Genuine compiled-machine initial configuration agrees with the actual N-only source. -/
theorem initial_eq (bits:List Bool) : Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have he:initial bits=SemiprimeD1StackCalls.initial originalInput (.local .empty) bits:=by
    unfold initial SemiprimeD1StackCalls.initial
    rw [input_single]
  rw [he]
  exact (SemiprimeD1StackCalls.initial_correct originalInput output (.local .empty) program bits).symm
/-- Genuine SAME-source finite-machine complete original owner-record certificate. -/
noncomputable def ownerRecordsInTime (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits) :
    StateTransition.EvalsToInTime machine.step (Turing.initList machine bits)
      (some (SemiprimeD1StackCalls.configuration (SemiprimeD1StackOwnerRecordsExecution.done bits hN [] [])))
      (polynomial bits.length) := by
  rw [initial_eq]
  apply SemiprimeD1StackCalls.evalsCorrect originalInput output (.local .empty) program
  let cert:=source_run_polynomial bits hc hN
  exact ⟨⟨Classical.choose cert,(Classical.choose_spec cert).2⟩,(Classical.choose_spec cert).1⟩
/-- EVERY actual compiled-machine prefix has the SAME complete physical344-role/return inventory. -/
theorem machine_prefix_cells (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fuel:Nat) (cfg:machine.Cfg)
    (hr:(fun q=>q.bind machine.step)^[fuel] (some (Turing.initList machine bits))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤ 345*(bits.length+polynomial bits.length) := by
  have he:=SemiprimeD1StackCalls.run_correct originalInput output (.local .empty) program fuel (initial bits)
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
/-- Entire actual305-role source state remains available, including acquired E/M caches. -/
theorem retained_source (bits:List Bool) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool))
    (tail:List Bool) (k:S.Stack) :
    (SemiprimeD1StackOwnerRecordsExecution.done bits hN fixed tail).data (source k)=
      (SemiprimeD1StackOwnerFibreCatalogueExecution.done bits hN).data k:=rfl
/-- All source and return alphabets are fixed finite BEFORE N and caller prefix. -/
theorem all_alphabets_finite :∀k,Finite (machine.Γ k):=
  SemiprimeD1StackCalls.all_alphabets_finite originalInput output (.local .empty) program
theorem control_finite :Finite machine.σ:=
  SemiprimeD1StackCalls.control_finite originalInput output (.local .empty) program
theorem compile_depth (pc:Label) :SemiprimeD1StackBytecode.statementDepth (machine.m pc)≤4:=
  SemiprimeD1StackCalls.compile_depth (.local .empty:Label) (program pc)
end RiemannGaussian.SemiprimeD1StackOwnerRecordsResources
