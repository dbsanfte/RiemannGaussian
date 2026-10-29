/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryStorage
/-! # Exact original individual parent-entry integer lift
This is one prepared entry source. Acquiring the actual unary port order,
alignment, activation/unit, entire table DFS and canonical recopy remains in
the caller/next factory stages; none is pretended to execute here.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryOriginal
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryPrepare SemiprimeD1StackChildTableEntryExecution
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeBitArithmetic (bitValue)
/-- Every original entry's output is a physical vector of individually lifted coefficients. -/
theorem output_bytes (oldAxes newAxes:List Nat) (oldp newp table order assignment:List Bool) (ws:List (List Bool)):
    (done oldAxes newAxes oldp newp table order assignment ws).data (aux .output)=
      vectorBits (lifted newp ws (newAxes.prod-oldAxes.prod)):=rfl
/-- All15 words of EACH actually acquired context bank remain unchanged after the complete ready/whole source. -/
theorem contexts_preserved (oldAxes newAxes:List Nat) (oldp newp table order assignment:List Bool)
    (ws:List (List Bool)) (b:Bool) (k:J.Stack):
    (done oldAxes newAxes oldp newp table order assignment ws).data (context b k)=
      (if b then Context.finalData newAxes newp else Context.finalData oldAxes oldp) k:=by cases b <;> rfl
/-- Actual paid parent-entry vector is retained, rather than supplied to the front door. -/
theorem parentEntry_bytes (oldAxes newAxes:List Nat) (oldp newp table order assignment:List Bool) (ws:List (List Bool)):
    (done oldAxes newAxes oldp newp table order assignment ws).data (aux .parentEntry)=vectorBits ws:=rfl
/-- Allocated tree-path shadow is physically empty; actual lookup path was directly aliased to gather output. -/
theorem path_shadow (oldAxes newAxes:List Nat) (oldp newp table order assignment:List Bool) (ws:List (List Bool)):
    (done oldAxes newAxes oldp newp table order assignment ws).data (treeAllocation .path)=[]:=rfl
/-- Positive extra-axis product gives each actual appended dimension positive size. -/
theorem extra_positive (extra:List Nat) (he:0<extra.prod):∀q∈extra,0<q:=by
  induction extra with
  | nil=>intro q hq;cases hq
  | cons a rest ih=>
    have hprod:0<a*rest.prod:=he
    have ha:0<a:=by
      by_contra h
      have hz:a=0:=by omega
      rw [hz,Nat.zero_mul] at hprod
      omega
    have ht:0<rest.prod:=by
      by_contra h
      have hz:rest.prod=0:=by omega
      rw [hz,Nat.mul_zero] at hprod
      omega
    intro q hq
    rcases List.mem_cons.mp hq with hq|hq
    · subst q;exact ha
    · exact ih ht q hq
/-- Exact individual integer lift after the REAL cached-order gather and REAL sequential parent table read, with old/new precision kept distinct. -/
theorem entry_words {d:Nat} (old:SemiprimeD1JetAxes.Context) (extra:List Nat) (he:0<extra.prod)
    (newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool):
    lifted newp (selected table assignment order) ((extra++old.axes).prod-old.axes.prod)=
      (SemiprimeD1ChildTableCopyTape.entry old extra (bitValue newp) table order assignment).words:=by
  rw [SemiprimeD1ChildTableCopyTape.entry_words]
  change _=(SemiprimeD1ChildTableCopy.lift old extra (bitValue newp)
    (SemiprimeD1TensorTables.lookup table (SemiprimeD1ChildTableCopy.gather assignment order).value).words).words
  rw [←gathered_original]
  exact lifted_original old extra newp (selected table assignment order) he
/-- Intrinsic canonical parent-table shape discharges the physical old-rank count internally. No rank or coefficient-count answer is an input. -/
theorem selected_shape {d:Nat} (old:SemiprimeD1JetAxes.Context) (table:SemiprimeD1TensorTables.Table d)
    (hg:SemiprimeD1TensorTables.Good old table) (order:List Nat) (assignment:List Bool):
    (selected table assignment order).length=old.axes.prod:=
  (SemiprimeD1TensorTables.lookup_good old table hg (gathered assignment order)).1
/-- Literal appended positive-axis header proves the relation between the two ACTUALLY acquired ranks. -/
theorem rank_mono (old extra:List Nat) (he:0<extra.prod):old.prod  ≤  (extra++old).prod:=by
  rw [List.prod_append]
  have h:=Nat.mul_le_mul_right old.prod (show 1  ≤  extra.prod by omega)
  simpa only [Nat.one_mul] using h
/-- Whole actual seven-input original-family entry: no given rank/q/product, no aggregate lift, no old/new-precision equality assumption. -/
theorem source_run_original {d:Nat} (old:SemiprimeD1JetAxes.Context) (ho:∀q∈old.axes,0<q)
    (extra:List Nat) (he:0<extra.prod) (oldp newp:List Bool) (hp:bitValue oldp=old.precision)
    (table:SemiprimeD1TensorTables.Table d) (hg:SemiprimeD1TensorTables.Good old table)
    (order:List Nat) (assignment:List Bool):
    ∃t   ≤   wholeBound old.axes (extra++old.axes) oldp newp table order assignment,
      SemiprimeD1StackCalls.run program t (initial (tape table) (orderTape order) assignment
        (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp)=
        some (done old.axes (extra++old.axes) oldp newp (tape table) (orderTape order) assignment (selected table assignment order)) ∧
      (done old.axes (extra++old.axes) oldp newp (tape table) (orderTape order) assignment (selected table assignment order)).data (aux .output)=
        vectorBits (SemiprimeD1ChildTableCopyTape.entry old extra (bitValue newp) table order assignment).words ∧
      ((done old.axes (extra++old.axes) oldp newp (tape table) (orderTape order) assignment
        (selected table assignment order)).data (context false J.widthCache)).length=old.precision:=by
  have hn:∀q∈extra++old.axes,0<q:=by
    intro q hq
    rcases List.mem_append.mp hq with hq|hq
    · exact extra_positive extra he q hq
    · exact ho q hq
  obtain ⟨t,ht,hr⟩:=source_run old.axes (extra++old.axes) ho hn oldp newp table order assignment
    (selected_shape old table hg order assignment) (rank_mono old.axes extra he)
  refine ⟨t,ht,hr,?_,?_⟩
  · rw [output_bytes,entry_words old extra he]
  · rw [contexts_preserved]
    exact (SemiprimeD1StackJetContextCorrectness.width_value old.axes oldp).trans hp
/-- Both literal positive-header sources are derived from original old/extra axis lineage. -/
theorem appended_positive (old extra:List Nat) (ho:∀q∈old,0<q) (he:0<extra.prod):∀q∈extra++old,0<q:=by
  intro q hq
  rcases List.mem_append.mp hq with hq|hq
  · exact extra_positive extra he q hq
  · exact ho q hq
/-- Complete original whole entry with its OWN fixed quadratic clock in actual input bytes and acquired rank/precision VALUES. -/
theorem source_run_original_bounded {d:Nat} (old:SemiprimeD1JetAxes.Context) (ho:∀q∈old.axes,0<q)
    (extra:List Nat) (he:0<extra.prod) (oldp newp:List Bool) (hp:bitValue oldp=old.precision)
    (table:SemiprimeD1TensorTables.Table d) (hg:SemiprimeD1TensorTables.Good old table)
    (order:List Nat) (assignment:List Bool):
    ∃t  ≤  SemiprimeD1StackChildTableEntryClock.wholePolynomial old.axes (extra++old.axes) oldp newp table order assignment,
      SemiprimeD1StackCalls.run program t (initial (tape table) (orderTape order) assignment
        (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp)=
        some (done old.axes (extra++old.axes) oldp newp (tape table) (orderTape order) assignment (selected table assignment order)) ∧
      (done old.axes (extra++old.axes) oldp newp (tape table) (orderTape order) assignment (selected table assignment order)).data (aux .output)=
        vectorBits (SemiprimeD1ChildTableCopyTape.entry old extra (bitValue newp) table order assignment).words ∧
      ((done old.axes (extra++old.axes) oldp newp (tape table) (orderTape order) assignment
        (selected table assignment order)).data (context false J.widthCache)).length=old.precision:=by
  obtain ⟨t,ht,hr,hout,hwidth⟩:=source_run_original old ho extra he oldp newp hp table hg order assignment
  have hb:=SemiprimeD1StackChildTableEntryBounds.wholeBound_le old.axes (extra++old.axes) ho
    (appended_positive old.axes extra ho he) oldp newp table order assignment
    (selected_shape old table hg order assignment) (rank_mono old.axes extra he)
  exact ⟨t,ht.trans hb,hr,hout,hwidth⟩
/-- The SAME ready entry reuses actual old/new context caches and returns the exact original INDIVIDUAL integer lift with its own fixed quadratic. -/
theorem ready_run_original_bounded {d:Nat} (old:SemiprimeD1JetAxes.Context) (ho:∀q∈old.axes,0<q)
    (extra:List Nat) (he:0<extra.prod) (oldp newp:List Bool)
    (table:SemiprimeD1TensorTables.Table d) (hg:SemiprimeD1TensorTables.Good old table)
    (order:List Nat) (assignment:List Bool):
    ∃t  ≤  SemiprimeD1StackChildTableEntryClock.readyPolynomial old.axes (extra++old.axes) oldp newp table order assignment,
      SemiprimeD1StackCalls.run program t (ready old.axes (extra++old.axes) oldp newp (tape table) (orderTape order) assignment)=
        some (done old.axes (extra++old.axes) oldp newp (tape table) (orderTape order) assignment (selected table assignment order)) ∧
      (done old.axes (extra++old.axes) oldp newp (tape table) (orderTape order) assignment (selected table assignment order)).data (aux .output)=
        vectorBits (SemiprimeD1ChildTableCopyTape.entry old extra (bitValue newp) table order assignment).words:=by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackChildTableEntryClock.ready_run_bounded old.axes (extra++old.axes)
    (SemiprimeD1StackChildTableEntryAcquisition.prod_positive old.axes ho)
    (SemiprimeD1StackChildTableEntryAcquisition.prod_positive (extra++old.axes) (appended_positive old.axes extra ho he))
    oldp newp table order assignment (selected_shape old table hg order assignment) (rank_mono old.axes extra he)
  refine ⟨t,ht,hr,?_⟩
  rw [output_bytes,entry_words old extra he]
end RiemannGaussian.SemiprimeD1StackChildTableEntryOriginal
