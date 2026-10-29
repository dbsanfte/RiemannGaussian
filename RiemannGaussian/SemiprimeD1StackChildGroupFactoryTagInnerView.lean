/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagInner
/-! # Exact first-index counter and whole-child exhaustion boundary
Freshness is asserted only when the real child scan was exhausted. A real hit
leaves its current fields/unread bytes present for the later paid early cleanup.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagInnerView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryTagInner
namespace VV
export SemiprimeD1StackChildGroupFactoryTagVisitView
  (result_hit result_other result_reader result_clean result_position result_candidate)
end VV
namespace Raw
export SemiprimeD1StackChildGroupFactoryTagVisit (built parsed)
end Raw
namespace Parse
export SemiprimeD1StackChildGroupFactoryChildParse (result)
end Parse
/-- Actual binary position at the first hit, or the count after physical EOF. -/
def finalPosition:List Encoding.Child→List Bool→List Bool→List Bool→List Bool
  | [],_,_,position=>position
  | p::ps,target,tag,position=>if View.hit p.1 target tag then position
    else finalPosition ps target tag (View.advance p.1 target position)
/-- All source/caller words outside the real child/search work roles are retained exactly. -/
theorem result_other (children:List Encoding.Child) (before:Stack→List Bool) (target tag position:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (hr:k≠aux .endpointReader) (hc:k≠aux .candidateTag) (hp:k≠aux .localPosition):
    result children before target tag position k=before k:=by
  induction children generalizing before position with
  | nil=>simp only [result,atEOF,Function.update_of_ne hr]
  | cons p ps ih=>
    by_cases h:View.hit p.1 target tag
    · simp only [result,h,ite_true]
      exact VV.result_other _ _ _ _ _ _ _ k hf hr hc hp
    · simp only [result,h,ite_false]
      rw [ih]
      exact VV.result_other _ _ _ _ _ _ _ k hf hr hc hp
/-- The real local binary counter, including an actual first-hit short circuit. -/
theorem result_position (children:List Encoding.Child) (before:Stack→List Bool) (target tag position:List Bool)
    (hp:before (aux .localPosition)=position):
    result children before target tag position (aux .localPosition)=finalPosition children target tag position:=by
  induction children generalizing before position with
  | nil=>simpa [result,atEOF,finalPosition,aux] using hp
  | cons p ps ih=>
    by_cases h:View.hit p.1 target tag
    · simp only [result,finalPosition,h,ite_true]
      rw [VV.result_hit _ _ _ _ _ _ _ h]
      simpa [Raw.built,Raw.parsed,Parse.result,aux] using hp
    · simp only [result,finalPosition,h,ite_false]
      exact ih _ _ (VV.result_position _ _ _ _ _ _ _ hp h)
/-- If the actual source reports no hit, the first child cannot have been a real match. -/
theorem no_hit_head (p:Encoding.Child) (ps:List Encoding.Child) (target tag:List Bool)
    (hf:found (p::ps) target tag=false):¬View.hit p.1 target tag:=by
  intro h
  simp [found,h] at hf
/-- Actual exhausted remainder when the first child had no literal/numeric match. -/
theorem no_hit_tail (p:Encoding.Child) (ps:List Encoding.Child) (target tag:List Bool)
    (hf:found (p::ps) target tag=false):found ps target tag=false:=by
  simpa only [found,no_hit_head p ps target tag hf,ite_false] using hf
/-- Only actual exhausted child scans claim an empty child reader. -/
theorem result_reader (children:List Encoding.Child) (before:Stack→List Bool) (target tag position:List Bool)
    (hf:found children target tag=false):result children before target tag position (aux .endpointReader)=[]:=by
  induction children generalizing before position with
  | nil=>rfl
  | cons p ps ih=>
    have hn:=no_hit_head p ps target tag hf
    simp only [result,hn,ite_false]
    exact ih _ _ (no_hit_tail p ps target tag hf)
/-- Actual exhausted child scans restore all nine raw/parser fresh roles. -/
theorem result_clean (children:List Encoding.Child) (before:Stack→List Bool) (target tag position:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]) (hf:found children target tag=false):
    ∀k∈Parse.cleanRoles,result children before target tag position k=[]:=by
  induction children generalizing before position with
  | nil=>
    intro k hk
    have hn:k≠aux .endpointReader:=by intro he;subst k;simp [Parse.cleanRoles,aux,field] at hk
    simpa only [result,atEOF,Function.update_of_ne hn] using hz k hk
  | cons p ps ih=>
    have hn:=no_hit_head p ps target tag hf
    simp only [result,hn,ite_false]
    exact ih _ _ (VV.result_clean _ _ _ _ _ _ _ hz hn) (no_hit_tail p ps target tag hf)
/-- Actual exhausted child scans restore the real temporary candidate-tag word. -/
theorem result_candidate (children:List Encoding.Child) (before:Stack→List Bool) (target tag position:List Bool)
    (hc:before (aux .candidateTag)=[]) (hf:found children target tag=false):
    result children before target tag position (aux .candidateTag)=[]:=by
  induction children generalizing before position with
  | nil=>simpa [result,atEOF,aux] using hc
  | cons p ps ih=>
    have hn:=no_hit_head p ps target tag hf
    simp only [result,hn,ite_false]
    exact ih _ _ (VV.result_candidate _ _ _ _ _ _ _ hc hn) (no_hit_tail p ps target tag hf)
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagInnerView
