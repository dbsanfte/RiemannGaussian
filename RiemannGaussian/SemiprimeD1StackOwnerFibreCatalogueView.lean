/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueView
open SemiprimeD1StackOwnerFibreCatalogue SemiprimeD1StackOwnerFibreCatalogueSource
/-- Actual owner-filter work roles alias no upstream source or outer loop word. -/
theorem fibre_injective :Function.Injective fibreStack:=Sum.inr_injective.comp Sum.inl_injective
/-- Actual private outer roles alias no source or filter role. -/
theorem aux_injective :Function.Injective aux:=Sum.inr_injective.comp Sum.inr_injective
/-- Literal reached filter-work projection. -/
theorem data_fibre (s:R.Stack→List Bool) (f:V.Stack→List Bool) (a:Aux→List Bool) (k:V.Stack) :
    data s f a (fibreStack k)=f k:=rfl
/-- Literal reached private metadata/reader/collector projection. -/
theorem data_aux (s:R.Stack→List Bool) (f:V.Stack→List Bool) (a:Aux→List Bool) (k:Aux) :
    data s f a (aux k)=a k:=rfl
/-- Exact physical filter-role update preserving the retained actual source and every outer word. -/
theorem update_fibre (s:R.Stack→List Bool) (f:V.Stack→List Bool) (a:Aux→List Bool) (k:V.Stack) (word:List Bool) :
    Function.update (data s f a) (fibreStack k) word=data s (Function.update f k word) a:=by
  funext j;rcases j with j|j
  · exact Function.update_of_ne (by intro h;cases h) _ _
  · rcases j with j|j
    · change Function.update (data s f a) (fibreStack k) word (fibreStack j)=(Function.update f k word) j
      simp only [Function.update_apply,data_fibre,fibre_injective.eq_iff]
    · exact Function.update_of_ne (by intro h;cases h) _ _
/-- Exact physical outer-role update preserving all original source/filter data. -/
theorem update_aux (s:R.Stack→List Bool) (f:V.Stack→List Bool) (a:Aux→List Bool) (k:Aux) (word:List Bool) :
    Function.update (data s f a) (aux k) word=data s f (Function.update a k word):=by
  funext j;rcases j with j|j
  · exact Function.update_of_ne (by intro h;cases h) _ _
  · rcases j with j|j
    · exact Function.update_of_ne (by intro h;cases h) _ _
    · change Function.update (data s f a) (aux k) word (aux j)=(Function.update a k word) j
      simp only [Function.update_apply,data_aux,aux_injective.eq_iff]
/-- Exact actual E-counter, ID-reader and reverse-collector boundary. -/
def rowAux (count ids raw:List Bool) :Aux→List Bool
  | .ownerCount=>count | .readerIds=>ids | .reversed=>raw | _=>[]
/-- Mathematical all-original owner/scope routed row list supplied by the actual N-only source. -/
def pairs (bits:List Bool) (hN:0<SemiprimeBitArithmetic.bitValue bits) :=
  SemiprimeD1StackOwnerFibreOriginal.rows (SemiprimeBitArithmetic.bitValue bits) hN
/-- The actually retained routing tape has the EXACT original owner/scope grammar. -/
theorem source_pairs (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits) :
    (SemiprimeD1StackPortOwnerRoutingExecution.done bits hN).data
      (SemiprimeD1StackPortOwnerRouting.aux .output)=SemiprimeD1StackOwnerFibre.records (pairs bits hN) []:=
  SemiprimeD1StackPortOwnerRoutingExecution.output_original bits hc hN
end RiemannGaussian.SemiprimeD1StackOwnerFibreCatalogueView
