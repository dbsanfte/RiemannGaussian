/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsLoop
/-! # Exact whole original-port index vector and actual full reuse invariant -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsLoopView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryOldPortsLoop
/-- The actual original-port reader has consumed its real FALSE and passed physical EOF. -/
theorem result_oldReader (points:List Parse.Point) (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target:List Bool):
    result points before buckets target (aux .oldReader)=[]:=by
  induction points generalizing before with
  | nil=>rfl
  | cons p ps ih=>exact ih _
/-- All twenty actual query/parser/buffer words are fresh after the complete original-port scan. -/
theorem result_fresh (points:List Parse.Point) (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target:List Bool)
    (hf:Fresh before):Fresh (result points before buckets target):=by
  induction points generalizing before with
  | nil=>
    intro j
    have hn:freshRole j≠aux .oldReader:=by fin_cases j <;> decide
    exact (Function.update_of_ne hn _ _).trans (hf j)
  | cons p ps ih=>exact ih _ (fresh_step _ _ _ _ _ hf)
/-- Every other actual caller/cache word survives the entire old-port scan. -/
theorem result_other (points:List Parse.Point) (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target:List Bool) (k:Stack)
    (hf:∀j,Early.role j≠k) (ho:k≠aux .oldReader) (ha:k≠aux .answerPosition)
    (hp:k≠aux .localPosition) (ht:k≠aux .tagWord) (hh:k≠aux .orderHistory):
    result points before buckets target k=before k:=by
  induction points generalizing before with
  | nil=>simp only [result,atEOF,Function.update_of_ne ho]
  | cons p ps ih=>rw [result,ih];exact OV.result_other _ _ _ _ _ k hf ho ha hp ht hh
/-- Exact chronological computed index records for EVERY matching original port, preserving duplicates. -/
theorem result_orderHistory (points:List Parse.Point) (before:Stack→List Bool) (buckets:List Buckets.Bucket) (target:List Bool):
    result points before buckets target (aux .orderHistory)=
      ((orderWords buckets points target).flatMap Log.row).reverse++before (aux .orderHistory):=by
  induction points generalizing before with
  | nil=>simp only [result,atEOF,orderWords,List.flatMap_nil,List.reverse_nil,List.nil_append];rfl
  | cons p ps ih=>
    rw [result,ih,OV.result_orderHistory]
    by_cases h:SemiprimeBitArithmetic.bitValue p.vertex=SemiprimeBitArithmetic.bitValue target <;>
      simp [orderWords,h,List.reverse_append,List.append_assoc]
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryOldPortsLoopView
