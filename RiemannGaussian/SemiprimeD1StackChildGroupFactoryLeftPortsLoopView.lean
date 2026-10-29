/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsLoop
/-! # Exact actual left-port order and complete nested scan reuse boundary -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsLoopView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryLeftPortsLoop
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (row)
end Log
/-- The actual one-bucket scan prepends exactly its selected global-ID word records. -/
theorem step_portHistory (before:Stack→List Bool) (b:Bucket) (tail target:List Bool):
    step before b tail target (aux .portHistory)=
      ((Inner.portWords b.children target).flatMap Log.row).reverse++before (aux .portHistory):=by
  rw [step,Inner.result_portHistory]
  rfl
/-- Exact actual filtered port word order across every observed bucket. -/
theorem result_portHistory (buckets:List Bucket) (before:Stack→List Bool) (target:List Bool):
    result buckets before target (aux .portHistory)=
      ((portWords buckets target).flatMap Log.row).reverse++before (aux .portHistory):=by
  induction buckets generalizing before with
  | nil=>simp only [result,atEOF,portWords,List.flatMap_nil,List.reverse_nil,List.nil_append];rfl
  | cons b bs ih=>
    rw [result,ih,step_portHistory]
    simp only [portWords,List.flatMap_append,List.reverse_append,List.append_assoc]
/-- Every physical cache word outside the actual six child roles, two readers and port log is retained. -/
theorem result_other (buckets:List Bucket) (before:Stack→List Bool) (target:List Bool) (k:Stack)
    (hf:∀j,Cleanup.role j≠k) (he:k≠aux .endpointReader) (ho:k≠aux .outerReader) (hp:k≠aux .portHistory):
    result buckets before target k=before k:=by
  induction buckets generalizing before with
  | nil=>simp only [result,atEOF,Function.update_of_ne ho]
  | cons b bs ih=>rw [result,ih];exact step_other _ _ _ _ k hf he ho hp
/-- Actual entire outer reader is empty after its real EOF pair. -/
theorem result_outerReader (buckets:List Bucket) (before:Stack→List Bool) (target:List Bool):
    result buckets before target (aux .outerReader)=[]:=by
  induction buckets generalizing before with
  | nil=>rfl
  | cons b bs ih=>exact ih _
/-- Actual endpoint reader is empty even when there were no observed packets. -/
theorem result_endpointReader (buckets:List Bucket) (before:Stack→List Bool) (target:List Bool)
    (he:before (aux .endpointReader)=[]):result buckets before target (aux .endpointReader)=[]:=by
  induction buckets generalizing before with
  | nil=>simpa [result,atEOF,aux] using he
  | cons b bs ih=>exact ih _ (step_endpointReader _ _ _ _)
/-- Whole nested scan preserves actual child-parser freshness. -/
theorem result_clean (buckets:List Bucket) (before:Stack→List Bool) (target:List Bool)
    (hz:∀k∈Parse.cleanRoles,before k=[]):∀k∈Parse.cleanRoles,result buckets before target k=[]:=by
  induction buckets generalizing before with
  | nil=>
    intro k hk
    have hn:k≠aux .outerReader:=by intro he;subst k;simp [Parse.cleanRoles,aux,field] at hk
    simpa only [result,atEOF,Function.update_of_ne hn] using hz k hk
  | cons b bs ih=>exact ih _ (step_clean _ _ _ _ hz)
/-- Whole nested scan preserves actual header-parser freshness. -/
theorem result_headerClean (buckets:List Bucket) (before:Stack→List Bool) (target:List Bool)
    (hh:∀k∈Header.cleanRoles,before k=[]):∀k∈Header.cleanRoles,result buckets before target k=[]:=by
  induction buckets generalizing before with
  | nil=>
    intro k hk
    have hn:k≠aux .outerReader:=by intro he;subst k;simp [Header.cleanRoles,aux,field] at hk
    simpa only [result,atEOF,Function.update_of_ne hn] using hh k hk
  | cons b bs ih=>exact ih _ (step_headerClean _ _ _ _ hh)
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryLeftPortsLoopView
