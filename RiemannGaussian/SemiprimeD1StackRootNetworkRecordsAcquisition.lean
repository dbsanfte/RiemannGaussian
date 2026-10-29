/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRecordsPrimitives

/-! # Same-program paid original-input acquisition of both root record banks
The two included source traces are concrete. Original N and the actual caller
prefix are physically copied into their respective empty source inputs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootNetworkRecordsAcquisition
open SemiprimeD1StackRootNetworkRecords SemiprimeD1StackRootNetworkRecordsPrimitives
open SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (bitValue)
local notation "ctl" => (Sum.inl : Control→Label)
/-- Actual encoded prefix/tail from the caller, not a supplied table or answer. -/
def prescription (bits:List Bool)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool))
    (tail:List Bool) : List Bool :=SemiprimeD1OwnerPrefixBits.records
      (SemiprimeD1StackOwnerRecordsOriginal.prefixRows (bitValue bits) fixed) tail
/-- The empty original prescription is exactly the marker written by the main entry. -/
theorem prescription_empty (bits:List Bool) : prescription bits [] []=[false] :=rfl
/-- The concrete original factor input has only the physically copied N word. -/
theorem factor_input (bits:List Bool) :
    (F.initial bits).data=Function.update (fun _=>[]) F.originalInput bits := by
  funext k
  change F.input bits k=_
  rw [SemiprimeD1StackFullFactorCatalogueFinish.input_eq]
  by_cases hk:k=F.originalInput
  · subst k;simp
  · simp [Function.update,hk]
/-- The actual owner input before the prefix copy contains only the copied N word. -/
theorem owner_empty_input (bits:List Bool) :
    (O.initialPrefix bits []).data=Function.update (fun _=>[]) O.originalInput bits := by
  change SemiprimeD1StackOwnerRecords.data (SemiprimeD1StackOwnerRecords.S.input bits)
    (fun _=>[]) (SemiprimeD1StackOwnerRecords.rowAux [] [])=_
  rw [SemiprimeD1StackOwnerRecordsResources.input_single]
  funext k
  by_cases hk:k=O.originalInput
  · subst k;simp
  · simp [Function.update,hk]
/-- One real prefix write transforms the actual empty-prefix owner input exactly. -/
theorem owner_prefix_input (bits pre:List Bool) :
    Function.update (O.initialPrefix bits []).data (SemiprimeD1StackOwnerRecords.aux .prefixBytes) pre=
      (O.initialPrefix bits pre).data := by
  have ha:Function.update (SemiprimeD1StackOwnerRecords.rowAux [] [])
      SemiprimeD1StackOwnerRecords.Aux.prefixBytes pre=SemiprimeD1StackOwnerRecords.rowAux [] pre:=by
    funext k;cases k <;> simp [SemiprimeD1StackOwnerRecords.rowAux,Function.update]
  unfold SemiprimeD1StackOwnerRecords.initialPrefix SemiprimeD1StackOwnerRecords.data SemiprimeD1StackOwnerRecords.aux
  rw [Sum.update_elim_inr,Sum.update_elim_inr,ha]
/-- The first actual copy gives the owner source its original binary input. -/
theorem owner_number_call (bits pre:List Bool) :
    Runs program (5*bits.length+4) (ctl .main) (work (fun _=>[]) (fun _=>[]) bits pre [] [] [])
      (ctl .copyPrefix) (work (fun _=>[]) (O.initialPrefix bits []).data bits pre [] [] []) := by
  have h:=copy_call .ownerNumber .main .copyPrefix rfl
    (work (fun _=>[]) (fun _=>[]) bits pre [] [] []) bits [] rfl rfl rfl
  simpa only [List.append_nil,copyTarget,work,update_owner,←owner_empty_input] using h
/-- The real second copy supplies the unchanged physical caller prefix/tail. -/
theorem prefix_call (bits pre:List Bool) :
    Runs program (5*pre.length+4) (ctl .copyPrefix)
      (work (fun _=>[]) (O.initialPrefix bits []).data bits pre [] [] [])
      (ctl .owners) (work (fun _=>[]) (O.initialPrefix bits pre).data bits pre [] [] []) := by
  have h:=copy_call .prefix .copyPrefix .owners rfl
    (work (fun _=>[]) (O.initialPrefix bits []).data bits pre [] [] []) pre [] rfl rfl rfl
  simpa only [List.append_nil,copyTarget,work,update_owner,owner_prefix_input] using h
/-- Actual complete owner source call preserves every factor/caller cell and every outer frame. -/
theorem owners_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool))
    (tail:List Bool) (f:F.Stack→List Bool) (a:Aux→List Bool) :
    ∃t ≤ O.budget bits hN fixed tail,Runs program (t+1) (ctl .owners)
      (data f (O.initialPrefix bits (prescription bits fixed tail)).data a)
      (ctl .copyFactorNumber) (data f (O.done bits hN fixed tail).data a) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackOwnerRecordsExecution.source_run_prefix bits hc hN fixed tail
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program ownerStack ownerLabel owner_injective
    O.program (.local .main) (fun _=>rfl) (ctl .owners) (ctl .copyFactorNumber) rfl t
    (O.initialPrefix bits (prescription bits fixed tail)) (O.done bits hN fixed tail) _ _
    rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;cases k with
      | inl k=>rfl
      | inr k=>cases k with
        | inl k=>exact (hk k rfl).elim
        | inr k=>rfl
/-- The factor source receives its own physically acquired copy of the same retained binary N. -/
theorem factor_number_call (bits pre:List Bool) (o:O.Stack→List Bool) :
    Runs program (5*bits.length+4) (ctl .copyFactorNumber) (work (fun _=>[]) o bits pre [] [] [])
      (ctl .factors) (work (F.initial bits).data o bits pre [] [] []) := by
  have h:=copy_call .factorNumber .copyFactorNumber .factors rfl
    (work (fun _=>[]) o bits pre [] [] []) bits [] rfl rfl rfl
  simpa only [List.append_nil,copyTarget,work,update_factor,←factor_input] using h
/-- The complete actual eighteen-family factor acquisition is called once, with all old cells retained. -/
theorem factors_call (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (o:O.Stack→List Bool) (a:Aux→List Bool) :
    ∃t ≤ F.timeBound bits,Runs program (t+1) (ctl .factors) (data (F.initial bits).data o a)
      (ctl .copyFactorOutput) (data (F.done bits).data o a) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackFullFactorCatalogueExecution.source_run bits hc hN
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program factorStack factorLabel Sum.inl_injective
    F.program (.local .main) (fun _=>rfl) (ctl .factors) (ctl .copyFactorOutput) rfl t
    (F.initial bits) (F.done bits) _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;cases k with
      | inl k=>exact (hk k rfl).elim
      | inr k=>rfl
/-- One actual acquisition trace composes all three copies and both genuine source calls. -/
theorem acquire_trace (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (fixed:List (Fin (SemiprimePublicAcquiredExecution.wireCount (bitValue bits))×Bool)) (tail:List Bool) :
    ∃t ≤ O.budget bits hN fixed tail+F.timeBound bits+10*bits.length+
        5*(prescription bits fixed tail).length+14,
      Runs program t (ctl .main) (initialPrefix bits (prescription bits fixed tail)).data
        (ctl .copyFactorOutput) (work (F.done bits).data (O.done bits hN fixed tail).data bits
          (prescription bits fixed tail) [] [] []) := by
  let pre:=prescription bits fixed tail
  have h0:=owner_number_call bits pre
  have h1:=prefix_call bits pre
  obtain ⟨o,ho,h2⟩:=owners_call bits hc hN fixed tail (fun _=>[]) (words bits pre [] [] [] [])
  have h3:=factor_number_call bits pre (O.done bits hN fixed tail).data
  obtain ⟨f,hf,h4⟩:=factors_call bits hc hN (O.done bits hN fixed tail).data (words bits pre [] [] [] [])
  have h:=join (join (join (join h0 h1) h2) h3) h4
  exact ⟨_,by dsimp only [pre];omega,h⟩
end RiemannGaussian.SemiprimeD1StackRootNetworkRecordsAcquisition
