/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceStorage
/-! # Exact prepared incidence-query result and original-prefix classified counts
Actual acquisition of the occurrence keys, prefix cache and binary powers is a
caller obligation, discharged by their concrete sources. No supplied graph,
original evaluator, count, free mask or clock is a runtime input of this query.
The whole selector's original D1IncidenceSearch transport is a separate caller
meaning theorem; this component returns the exact actual ordered-pair sum.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceOriginal
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidenceBounds
open SemiprimeBitArithmetic (bitValue)
namespace Spec
export SemiprimeD1StackSourceIncidenceSpec (term total total_value term_formula)
end Spec
/-- Every25 acquired environment word is retained EXACTLY, including arbitrary query/chosen/prefix/nextKey. -/
theorem environment_preserved (i:Inputs) (k:SemiprimeD1StackSourceEnvironment.Stack) :
    (done i).data (environmentStack k)=environment i k :=rfl
/-- The physically acquired occurrence stream is retained byte for byte, including all repeated entries. -/
theorem occurrences_retained (i:Inputs) :(done i).data (aux .source)=tape i :=rfl
/-- All three physically acquired binary count powers are retained without unary expansion. -/
theorem powers_retained (i:Inputs) :(done i).data (aux .square)=i.square ∧
    (done i).data (aux .cube)=i.cube ∧ (done i).data (aux .fourth)=i.fourth :=⟨rfl,rfl,rfl⟩
/-- Complete actual output bytes follow the real ordered ripple additions, including their genuine padding. -/
theorem count_word (i:Inputs) :(done i).data (aux .total)=Spec.total i.ids i.square i.cube i.fourth i.rows :=rfl
/-- Actual binary numeric output is exactly the full ordered M² term sum, with diagonals and multiplicities. -/
theorem count_value (i:Inputs) :bitValue ((done i).data (aux .total))=
    (i.rows.map (fun left=>(i.rows.map (fun right=>bitValue (Spec.term i.ids i.square i.cube i.fourth left right))).sum)).sum :=
  Spec.total_value i.ids i.square i.cube i.fourth i.rows
/-- Every private parser/comparator/ID-save/adder/query-save word is genuinely empty at halt. -/
theorem work_clear (i:Inputs) (k:Aux) (hk:k≠.source ∧ k≠.square ∧ k≠.cube ∧ k≠.fourth ∧ k≠.total) :
    (done i).data (aux k)=[] :=by
  cases k <;> first | rfl | exact (hk.1 rfl).elim | exact (hk.2.1 rfl).elim |
    exact (hk.2.2.1 rfl).elim | exact (hk.2.2.2.1 rfl).elim | exact (hk.2.2.2.2 rfl).elim
/-- Every original valid prefix has precisely its classified incidence count, assuming only the actual acquired power values.
Here N/L and original endpoint ranges occur solely in the mathematical interpretation, never control or input advice. -/
theorem classified_value (i:Inputs) (L N:Nat) (hk:i.ids.length ≤ N)
    (hs:bitValue i.square=L^2) (hc:bitValue i.cube=L^3) (hf:bitValue i.fourth=L^4)
    (hr:∀row∈i.rows,bitValue row.1 < N ∧ bitValue row.2 < N) :
    bitValue ((done i).data (aux .total))=
      (i.rows.map (fun left=>(i.rows.map (fun right=>
        SemiprimeSourceIncidenceCountFormula.classifiedCount L (List.range' i.ids.length (N-i.ids.length))
          (fun k=>bitValue (SemiprimeSourceHistogramPrefix.expected i.ids k))
          (bitValue left.1) (bitValue left.2) (bitValue right.1) (bitValue right.2))).sum)).sum :=by
  rw [count_value]
  apply congrArg List.sum
  apply List.map_congr_left
  intro left hl
  apply congrArg List.sum
  apply List.map_congr_left
  intro right hh
  exact Spec.term_formula i.ids L N i.square i.cube i.fourth hs hc hf left right hk (hr left hl) (hr right hh)
/-- Complete SAME physical query, exact result/retained cache and its own source-derived whole clock. -/
theorem source_run_original (i:Inputs) :∃q ≤ polynomial i,
    SemiprimeD1StackCalls.run program q (source i)=some (done i) ∧
      (∀k,(done i).data (environmentStack k)=environment i k) ∧
      (done i).data (aux .source)=tape i ∧
      (done i).data (aux .total)=Spec.total i.ids i.square i.cube i.fourth i.rows :=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded i
  exact ⟨q,hq,hr,environment_preserved i,occurrences_retained i,count_word i⟩
end RiemannGaussian.SemiprimeD1StackSourceIncidenceOriginal
