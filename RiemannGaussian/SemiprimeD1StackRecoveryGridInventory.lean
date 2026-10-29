/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGrid
/-! # Exact literal copy/cleanup inventories of the104-word grid source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridInventory
open SemiprimeD1StackRecoveryGrid
/-- Preserving copy source and destination are distinct actual fields at every fixed source site. -/
theorem copy_source_target (part:Copy) :copySource part≠copyTarget part:=by
  cases part <;> simp [copySource,copyTarget,powerCount,aux,reg,geometryAux,divisionStack,productStack,rippleStack,rationalStack]
  all_goals rename_i p
  all_goals cases p <;> decide
/-- Every source word is disjoint from the shared actual copy scratch. -/
theorem copy_source_scratch (part:Copy) :copySource part≠aux .copyScratch:=by
  cases part <;> simp [copySource,powerCount,aux,reg,geometryAux,divisionStack,productStack,rippleStack,rationalStack]
  all_goals rename_i p
  all_goals cases p <;> decide
/-- Every acquired destination is disjoint from the shared actual copy scratch. -/
theorem copy_target_scratch (part:Copy) :copyTarget part≠aux .copyScratch:=by
  cases part <;> simp [copyTarget,aux,reg,divisionStack,productStack,rippleStack,rationalStack]
/-- The literal three-field copy has no operand aliases; this does not require any native operand value. -/
theorem copy_injective (part:Copy) :Function.Injective (copyStack part):=by
  intro a b hab
  have hxy:=copy_source_target part
  have hxz:=copy_source_scratch part
  have hyz:=copy_target_scratch part
  fin_cases a <;> fin_cases b <;> first | rfl | exact (hxy hab).elim | exact (hxy hab.symm).elim | exact (hxz hab).elim | exact (hxz hab.symm).elim | exact (hyz hab).elim | exact (hyz hab.symm).elim
/-- The actual shared-word cleanup visits precisely35 distinct R roles. -/
theorem rationalRole_injective :Function.Injective rationalRole:=by decide
/-- Retained W is never included in physical arithmetic cleanup. -/
theorem rationalRole_not_template (i:Fin 35) :rationalRole i≠SemiprimeD1StackRationalOperation.aux .template:=by
  fin_cases i <;> decide
/-- Every actual non-template operation field is included in the paid cleanup; no shadow is omitted. -/
theorem rationalRole_complete (k:R.Stack) (hk:k≠SemiprimeD1StackRationalOperation.aux .template) :
    ∃i:Fin 35,rationalRole i=k:=by
  revert k
  decide
/-- Every physically allocated geometry field, including both displaced shadows, occurs in cleanup. -/
theorem geometryRole_complete (k:G.Aux) :∃i:Fin 10,geometryRole i=k:=by
  cases k
  · exact ⟨0,rfl⟩
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩
  · exact ⟨7,rfl⟩
  · exact ⟨8,rfl⟩
  · exact ⟨9,rfl⟩
end RiemannGaussian.SemiprimeD1StackRecoveryGridInventory
