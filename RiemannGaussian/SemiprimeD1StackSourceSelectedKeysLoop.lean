/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysParse
import RiemannGaussian.SemiprimeD1StackSourceSelectedKeysBody
/-! # Complete physical occurrence traversal and exact chronological selected-key log -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceSelectedKeysLoop
open SemiprimeD1StackSourceSelectedKeys SemiprimeD1StackSourceSelectedKeysEncoding
open SemiprimeD1StackSourceSelectedKeysPrimitives SemiprimeD1StackSourceSelectedKeysView
open SemiprimeD1StackSourceSelectedKeysParse SemiprimeD1StackSourceSelectedKeysBody
open SemiprimeD1StackProcedureTrace
/-- Actual row clock includes original pair-tag/field parsing and every subsequent physical producer stage. -/
def rowTime (i:Inputs) (own fac:List Bool) :Nat :=8*(own.length+fac.length)+17+bodyTime i own fac
/-- Own complete scan upper clock, with its actual terminal false pop. -/
def rowsTime (i:Inputs) (rows:List (List Bool×List Bool)) :Nat :=
  rows.foldr (fun row rest=>rowTime i row.1 row.2+rest) 1
/-- Each physical original occurrence emits exactly one complete oldjoint key in its input position. -/
theorem rows_run (i:Inputs) (rows:List (List Bool×List Bool)) (hist:List Bool)
    (hc:∀row∈rows,SemiprimeBitArithmetic.bitValue row.1 < i.ids.length ∧ SemiprimeBitArithmetic.bitValue row.2 < i.ids.length) :
    ∃q≤rowsTime i rows,
      Runs program q .header (view i [] [] [] (Records.records rows []) [] [] [] [] [] [] hist []) .eof
        (view i [] [] [] [] [] [] [] [] [] [] ((stream i.ids rows).reverse++hist) []) :=by
  induction rows generalizing hist with
  | nil=>
    have h:=pop_run .header .abort .eof (.parse .owner) (aux .reader)
      (view i [] [] [] (Records.records [] []) [] [] [] [] [] [] hist []) [false] rfl rfl
    change Runs program 1 _ _ _ (Function.update
      (view i [] [] [] (Records.records [] []) [] [] [] [] [] [] hist []) (aux .reader) []) at h
    rw [update_reader] at h
    exact ⟨1,le_rfl,h⟩
  | cons row rows ih=>
    rcases row with ⟨own,fac⟩
    have hh:=hc (own,fac) List.mem_cons_self
    have ht:∀row∈rows,SemiprimeBitArithmetic.bitValue row.1 < i.ids.length ∧ SemiprimeBitArithmetic.bitValue row.2 < i.ids.length:=
      fun row h=>hc row (List.mem_cons_of_mem _ h)
    have h0:=read_row i own fac hist rows
    obtain ⟨q,hq,h1⟩:=body_run i (Records.records rows []) own fac hist hh.1 hh.2
    obtain ⟨u,hu,h2⟩:=ih ((chunk i.ids (own,fac)).reverse++hist) ht
    have h:=join (join h0 h1) h2
    have he:(stream i.ids ((own,fac)::rows)).reverse++hist=
        (stream i.ids rows).reverse++((chunk i.ids (own,fac)).reverse++hist):=by
      change (chunk i.ids (own,fac)++stream i.ids rows).reverse++hist=_
      rw [List.reverse_append,List.append_assoc]
    refine ⟨_,?_,by rw [he];exact h⟩
    change 8*(own.length+fac.length)+17+q+u ≤ rowTime i own fac+rowsTime i rows
    unfold rowTime
    omega
end RiemannGaussian.SemiprimeD1StackSourceSelectedKeysLoop
