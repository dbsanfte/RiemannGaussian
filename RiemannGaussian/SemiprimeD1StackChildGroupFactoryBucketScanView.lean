/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketScan
/-! # Actual ordered bucket vectors and preserved scan-boundary caches -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketScanView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryBucketScan
namespace LV
export SemiprimeD1StackChildGroupFactoryBucketLoopView (result_other result_clean result_position finalPosition)
end LV
/-- The actual ordered endpoint-vector word, with its real FALSE terminator. -/
theorem result_children (before:Stack→List Bool) (es:List Parse.Endpoint) (packet position:List Bool):
    result before es packet position (aux .jointKey)=View.records es packet position++[false]:=rfl
/-- The actual binary fresh-ID word vector consumed by the real ordinal converter. -/
theorem result_ports (before:Stack→List Bool) (es:List Parse.Endpoint) (packet position:List Bool):
    result before es packet position (aux .portBank)=SemiprimeD1TensorTapeCodec.vectorBits (View.portWords es packet position):=
  port_records_vector _
/-- Both actual reverse histories are physically empty. -/
theorem result_histories (before:Stack→List Bool) (es:List Parse.Endpoint) (packet position:List Bool):
    result before es packet position (aux .bucketHistory)=[] ∧ result before es packet position (aux .portHistory)=[]:=⟨rfl,rfl⟩
/-- Exact current fresh child-global binary counter, obtained from actual increments. -/
theorem result_position (before:Stack→List Bool) (es:List Parse.Endpoint) (packet position:List Bool)
    (hp:before (aux .globalPosition)=position):
    result before es packet position (aux .globalPosition)=LV.finalPosition es packet position:=by
  change Loop.result es (copied before es) packet position (aux .globalPosition)=_
  exact LV.result_position _ _ _ _ (by simpa [copied,aux] using hp)
/-- Every other physical source word is retained across the actual scan and ordered reversals. -/
theorem result_other (before:Stack→List Bool) (es:List Parse.Endpoint) (packet position:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (hr:k≠aux .endpointReader) (hb:k≠aux .bucketHistory)
    (hp:k≠aux .portHistory) (hg:k≠aux .globalPosition) (hj:k≠aux .jointKey) (hpb:k≠aux .portBank):
    result before es packet position k=before k:=by
  simp only [result,reversed,Function.update_of_ne hpb,Function.update_of_ne hp,
    Function.update_of_ne hj,Function.update_of_ne hb]
  rw [LV.result_other _ _ _ _ k hf hr hb hp hg]
  exact Function.update_of_ne hr _ _
/-- The actual parser and row-buffer roles are all fresh at the converter boundary. -/
theorem result_clean (before:Stack→List Bool) (es:List Parse.Endpoint) (packet position:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]):
    ∀k∈Parse.cleanRoles,result before es packet position k=[]:=by
  have hc:∀k∈Parse.cleanRoles,copied before es k=[]:=by simpa [copied,Parse.cleanRoles,aux,field] using hz
  have h:=LV.result_clean es (copied before es) packet position hc
  intro k hk
  simp only [Parse.cleanRoles,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    simpa [result,reversed,aux,field] using h _ (by simp [Parse.cleanRoles,aux,field])
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryBucketScanView
