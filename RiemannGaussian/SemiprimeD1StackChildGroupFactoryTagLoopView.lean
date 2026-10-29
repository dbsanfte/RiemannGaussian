/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagLoop
/-! # Exact computed first-index word and conditional real exhaustion invariants
No hit branch is silently treated as cleared: its unread bytes/current fields
remain in the actual bank until the separate literal paid early-stop cleanup.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagLoopView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryTagLoop
/-- Actual binary local position at the first hit, or after complete physical outer EOF. -/
def finalPosition:List Buckets.Bucket→List Bool→List Bool→List Bool→List Bool
  | [],_,_,position=>position
  | b::bs,target,tag,position=>if Inner.found b.children target tag=true then IV.finalPosition b.children target tag position
    else finalPosition bs target tag (IV.finalPosition b.children target tag position)
/-- Exact physically computed local position across the complete real nested search. -/
theorem result_position (buckets:List Buckets.Bucket) (before:Stack→List Bool) (target tag position:List Bool)
    (hp:before (aux .localPosition)=position):
    result buckets before target tag position (aux .localPosition)=finalPosition buckets target tag position:=by
  induction buckets generalizing before position with
  | nil=>simpa [result,atEOF,finalPosition,aux] using hp
  | cons b bs ih=>
    by_cases h:Inner.found b.children target tag=true
    · simp only [result,finalPosition,h,ite_true]
      exact step_position _ _ _ _ _ _ hp
    · simp only [result,finalPosition,h,Bool.false_eq_true,ite_false]
      exact ih _ _ (step_position _ _ _ _ _ _ hp)
/-- All cache/caller bytes outside the exact actual parser/read/candidate/counter roles are retained. -/
theorem result_other (buckets:List Buckets.Bucket) (before:Stack→List Bool) (target tag position:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (he:k≠aux .endpointReader) (ho:k≠aux .outerReader)
    (hcan:k≠aux .candidateTag) (hp:k≠aux .localPosition):result buckets before target tag position k=before k:=by
  induction buckets generalizing before position with
  | nil=>simp only [result,atEOF,Function.update_of_ne ho]
  | cons b bs ih=>
    by_cases h:Inner.found b.children target tag=true
    · simp only [result,h,ite_true]
      exact step_other _ _ _ _ _ _ k hf he ho hcan hp
    · simp only [result,h,Bool.false_eq_true,ite_false]
      rw [ih]
      exact step_other _ _ _ _ _ _ k hf he ho hcan hp
/-- Actual exhausted whole-search outcome implies no hit in the first real bucket. -/
theorem no_hit_head (b:Buckets.Bucket) (bs:List Buckets.Bucket) (target tag:List Bool)
    (hf:found (b::bs) target tag=false):Inner.found b.children target tag=false:=by
  by_cases h:Inner.found b.children target tag=true
  · simp [found,h] at hf
  · cases hval:Inner.found b.children target tag with
    | false=>rfl
    | true=>exact False.elim (h hval)
/-- Actual exhausted whole-search outcome implies exhaustion of the real outer suffix. -/
theorem no_hit_tail (b:Buckets.Bucket) (bs:List Buckets.Bucket) (target tag:List Bool)
    (hf:found (b::bs) target tag=false):found bs target tag=false:=by
  simpa only [found,no_hit_head b bs target tag hf,Bool.false_eq_true,ite_false] using hf
/-- Only a real whole-search exhaustion promises complete parser/raw-field freshness. -/
theorem result_clean (buckets:List Buckets.Bucket) (before:Stack→List Bool) (target tag position:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]) (hf:found buckets target tag=false):
    ∀k∈Parse.cleanRoles,result buckets before target tag position k=[]:=by
  induction buckets generalizing before position with
  | nil=>
    intro k hk
    have hn:k≠aux .outerReader:=by intro he;subst k;simp [Parse.cleanRoles,aux,field] at hk
    simpa only [result,atEOF,Function.update_of_ne hn] using hz k hk
  | cons b bs ih=>
    have hn:=no_hit_head b bs target tag hf
    simp only [result,hn,Bool.false_eq_true,ite_false]
    exact ih _ _ (step_clean _ _ _ _ _ _ hz hn) (no_hit_tail b bs target tag hf)
/-- Only actual whole-search exhaustion promises every real header destination is fresh. -/
theorem result_headerClean (buckets:List Buckets.Bucket) (before:Stack→List Bool) (target tag position:List Bool)
    (hh:∀k∈Header.cleanRoles,before k=[]) (hf:found buckets target tag=false):
    ∀k∈Header.cleanRoles,result buckets before target tag position k=[]:=by
  induction buckets generalizing before position with
  | nil=>
    intro k hk
    have hn:k≠aux .outerReader:=by intro he;subst k;simp [Header.cleanRoles,aux,field] at hk
    simpa only [result,atEOF,Function.update_of_ne hn] using hh k hk
  | cons b bs ih=>
    have hn:=no_hit_head b bs target tag hf
    simp only [result,hn,Bool.false_eq_true,ite_false]
    exact ih _ _ (step_headerClean _ _ _ _ _ _ hh hn) (no_hit_tail b bs target tag hf)
/-- Real whole-search exhaustion promises a fresh candidate tag. -/
theorem result_candidate (buckets:List Buckets.Bucket) (before:Stack→List Bool) (target tag position:List Bool)
    (hc:before (aux .candidateTag)=[]) (hf:found buckets target tag=false):
    result buckets before target tag position (aux .candidateTag)=[]:=by
  induction buckets generalizing before position with
  | nil=>simpa [result,atEOF,aux] using hc
  | cons b bs ih=>
    have hn:=no_hit_head b bs target tag hf
    simp only [result,hn,Bool.false_eq_true,ite_false]
    exact ih _ _ (step_candidate _ _ _ _ _ _ hc hn) (no_hit_tail b bs target tag hf)
/-- Real whole-search exhaustion consumes the actual outer FALSE and EOF. -/
theorem result_outerReader (buckets:List Buckets.Bucket) (before:Stack→List Bool) (target tag position:List Bool)
    (hf:found buckets target tag=false):result buckets before target tag position (aux .outerReader)=[]:=by
  induction buckets generalizing before position with
  | nil=>rfl
  | cons b bs ih=>
    have hn:=no_hit_head b bs target tag hf
    simp only [result,hn,Bool.false_eq_true,ite_false]
    exact ih _ _ (no_hit_tail b bs target tag hf)
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryTagLoopView
