/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryBounds
/-! # SAME actual whole/ready source and genuine compiled time certificates -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryClock
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryPrepare SemiprimeD1StackChildTableEntryExecution SemiprimeD1StackChildTableEntryBounds
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1StackUnaryDivmod (unary)
/-- Fixed own whole-source coefficient and degree precede every actual parent/table/context. -/
def wholePolynomial {d:Nat} (oldAxes newAxes:List Nat) (oldp newp:List Bool)
    (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool):Nat:=
  100000000*(resource oldAxes newAxes oldp newp table order assignment)^2
/-- Same ready entry needs no context replay and has its own smaller fixed quadratic. -/
def readyPolynomial {d:Nat} (oldAxes newAxes:List Nat) (oldp newp:List Bool)
    (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool):Nat:=
  1000000*(resource oldAxes newAxes oldp newp table order assignment)^2
/-- Whole real source runs within its own VALUE-aware polynomial, no native report clock transported. -/
theorem source_run_bounded {d:Nat} (oldAxes newAxes:List Nat) (ho:∀q∈oldAxes,0<q) (hn:∀q∈newAxes,0<q)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hs:(selected table assignment order).length=oldAxes.prod) (hr:oldAxes.prod ≤ newAxes.prod):
    ∃t  ≤  wholePolynomial oldAxes newAxes oldp newp table order assignment,SemiprimeD1StackCalls.run program t
      (initial (tape table) (orderTape order) assignment (vectorBits (oldAxes.map unary)) oldp (vectorBits (newAxes.map unary)) newp)=
      some (done oldAxes newAxes oldp newp (tape table) (orderTape order) assignment (selected table assignment order)):=by
  obtain ⟨t,ht,h⟩:=source_run oldAxes newAxes ho hn oldp newp table order assignment hs hr
  exact ⟨t,ht.trans (wholeBound_le oldAxes newAxes ho hn oldp newp table order assignment hs hr),h⟩
/-- Same actual cache-ready source runs within its OWN polynomial without rerunning old/new context acquisition. -/
theorem ready_run_bounded {d:Nat} (oldAxes newAxes:List Nat) (ho:0<oldAxes.prod) (hn:0<newAxes.prod)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hs:(selected table assignment order).length=oldAxes.prod) (hr:oldAxes.prod ≤ newAxes.prod):
    ∃t  ≤  readyPolynomial oldAxes newAxes oldp newp table order assignment,SemiprimeD1StackCalls.run program t
      (ready oldAxes newAxes oldp newp (tape table) (orderTape order) assignment)=
      some (done oldAxes newAxes oldp newp (tape table) (orderTape order) assignment (selected table assignment order)):=by
  obtain ⟨t,ht,h⟩:=ready_run oldAxes newAxes ho hn oldp newp table order assignment hs hr
  exact ⟨t,ht.trans (readyBound_le oldAxes newAxes oldp newp table order assignment hs hr),h⟩
/-- Genuine finite compiled whole-source certificate, starting from the seven actual physical operand words only. -/
noncomputable def machineSource {d:Nat} (oldAxes newAxes:List Nat) (ho:∀q∈oldAxes,0<q) (hn:∀q∈newAxes,0<q)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hs:(selected table assignment order).length=oldAxes.prod) (hr:oldAxes.prod ≤ newAxes.prod):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration
        (initial (tape table) (orderTape order) assignment (vectorBits (oldAxes.map unary)) oldp (vectorBits (newAxes.map unary)) newp))
      (some (SemiprimeD1StackCalls.configuration
        (done oldAxes newAxes oldp newp (tape table) (orderTape order) assignment (selected table assignment order))))
      (wholePolynomial oldAxes newAxes oldp newp table order assignment):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .parentTable) (aux .output) (Label.local .start) program
  let h:=source_run_bounded oldAxes newAxes ho hn oldp newp table order assignment hs hr
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
/-- SAME finite program's actual ready certificate includes all real returns and retains both acquired context caches. -/
noncomputable def machineReady {d:Nat} (oldAxes newAxes:List Nat) (ho:0<oldAxes.prod) (hn:0<newAxes.prod)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hs:(selected table assignment order).length=oldAxes.prod) (hr:oldAxes.prod ≤ newAxes.prod):
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (ready oldAxes newAxes oldp newp (tape table) (orderTape order) assignment))
      (some (SemiprimeD1StackCalls.configuration
        (done oldAxes newAxes oldp newp (tape table) (orderTape order) assignment (selected table assignment order))))
      (readyPolynomial oldAxes newAxes oldp newp table order assignment):=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .parentTable) (aux .output) (Label.local .start) program
  let h:=ready_run_bounded oldAxes newAxes ho hn oldp newp table order assignment hs hr
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackChildTableEntryClock
