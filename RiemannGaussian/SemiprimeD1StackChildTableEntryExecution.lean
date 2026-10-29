/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryAcquisition
import RiemannGaussian.SemiprimeD1StackChildTableEntryPrepare
import RiemannGaussian.SemiprimeD1StackChildTableEntryLoop
/-! # Complete actual individual child-entry source and exact acquired-cache ready entry
All table/axis/rank/word values below describe existing physical input tapes or
actual callee output. The executed program is fixed before every such value.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryExecution
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
open SemiprimeD1StackChildTableEntryPrimitives SemiprimeD1StackChildTableEntryPrepare
open SemiprimeD1StackChildTableEntryAcquisition SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits tape)
open SemiprimeD1StackUnaryDivmod (unary)
namespace L
export SemiprimeD1StackChildTableEntryLoop (timeBound loop_trace)
end L
local notation "ctl"=>Label.local
/-- Actual ready-path copy/gather/read/coefficient/reverse/halt clock; original precision remains a separate retained input. -/
def readyBound {d:Nat} (oldAxes newAxes:List Nat) (newp:List Bool) (table:SemiprimeD1TensorTables.Table d)
    (order:List Nat) (assignment:List Bool):Nat:=
  SemiprimeD1StackChildTableEntryPrepare.budget oldAxes newAxes table order assignment+
    L.timeBound newp (selected table assignment order) (newAxes.prod-oldAxes.prod) ((gathered assignment order).drop d)
/-- Exact own whole budget includes BOTH actual context acquisitions and all ready-path operations. -/
def wholeBound {d:Nat} (oldAxes newAxes:List Nat) (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d)
    (order:List Nat) (assignment:List Bool):Nat:=
  SemiprimeD1StackChildTableEntryAcquisition.budget oldAxes newAxes oldp newp+
    readyBound oldAxes newAxes newp table order assignment
/-- SAME ready entry consumes the actually acquired rank caches, performs the complete real backend and individual integer lift, and retains all30 cache words. -/
theorem ready_trace {d:Nat} (oldAxes newAxes:List Nat) (ho:0<oldAxes.prod) (hn:0<newAxes.prod)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hshape:(selected table assignment order).length=oldAxes.prod) (hrank:oldAxes.prod≤newAxes.prod):
    ∃t,t+1 ≤ readyBound oldAxes newAxes newp table order assignment ∧ Runs program t (ctl .ready)
      (ready oldAxes newAxes oldp newp (tape table) (orderTape order) assignment).data (ctl .done)
      (result oldAxes newAxes oldp newp (tape table) (orderTape order) assignment (selected table assignment order)):=by
  obtain ⟨t0,ht0,h0⟩:=prepare_run oldAxes newAxes ho hn oldp newp table order assignment
  let ws:=selected table assignment order
  let zeros:=newAxes.prod-oldAxes.prod
  let path:=(gathered assignment order).drop d
  have h1:=L.loop_trace (Context.finalData oldAxes oldp) (Context.finalData newAxes newp) assignment path
    (tape table) (orderTape order) (vectorBits ws) newp ws zeros rfl
  have hs:ws.length=oldAxes.prod:=hshape
  have hc:oldAxes.prod+zeros=newAxes.prod:=by dsimp only [zeros];omega
  rw [hs,hc] at h1
  have h:=join h0 h1
  refine ⟨_,?_,h⟩
  have hp:1≤L.timeBound newp ws zeros path:=by unfold L.timeBound;omega
  unfold readyBound
  dsimp only [ws,zeros,path] at hp ⊢
  omega
/-- Exact same-cache ready halt; no geometry, precision or context source is rerun. -/
theorem ready_run {d:Nat} (oldAxes newAxes:List Nat) (ho:0<oldAxes.prod) (hn:0<newAxes.prod)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hshape:(selected table assignment order).length=oldAxes.prod) (hrank:oldAxes.prod≤newAxes.prod):
    ∃t ≤ readyBound oldAxes newAxes newp table order assignment,SemiprimeD1StackCalls.run program t
      (ready oldAxes newAxes oldp newp (tape table) (orderTape order) assignment)=
      some (done oldAxes newAxes oldp newp (tape table) (orderTape order) assignment (selected table assignment order)):=by
  obtain ⟨t,ht,h⟩:=ready_trace oldAxes newAxes ho hn oldp newp table order assignment hshape hrank
  obtain ⟨out,he,hAt⟩:=h [] (ready oldAxes newAxes oldp newp (tape table) (orderTape order) assignment) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl
    (result oldAxes newAxes oldp newp (tape table) (orderTape order) assignment (selected table assignment order)) [] out hAt
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
/-- Complete actual seven-input source includes both context calls, physical ordered read and every individually lifted coefficient. -/
theorem source_trace {d:Nat} (oldAxes newAxes:List Nat) (ho:∀q∈oldAxes,0<q) (hn:∀q∈newAxes,0<q)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hshape:(selected table assignment order).length=oldAxes.prod) (hrank:oldAxes.prod≤newAxes.prod):
    ∃t,t+1 ≤ wholeBound oldAxes newAxes oldp newp table order assignment ∧ Runs program t (ctl .start)
      (initial (tape table) (orderTape order) assignment (vectorBits (oldAxes.map unary)) oldp (vectorBits (newAxes.map unary)) newp).data
      (ctl .done) (result oldAxes newAxes oldp newp (tape table) (orderTape order) assignment (selected table assignment order)):=by
  obtain ⟨t0,ht0,h0⟩:=contexts_run oldAxes newAxes ho hn oldp newp (tape table) (orderTape order) assignment
  obtain ⟨t1,ht1,h1⟩:=ready_trace oldAxes newAxes (prod_positive oldAxes ho) (prod_positive newAxes hn)
    oldp newp table order assignment hshape hrank
  exact ⟨t0+t1,by unfold wholeBound;omega,join h0 h1⟩
/-- Whole actual halt has the exact individually lifted vector, all source words/caches retained, no work/flags/return advice. -/
theorem source_run {d:Nat} (oldAxes newAxes:List Nat) (ho:∀q∈oldAxes,0<q) (hn:∀q∈newAxes,0<q)
    (oldp newp:List Bool) (table:SemiprimeD1TensorTables.Table d) (order:List Nat) (assignment:List Bool)
    (hshape:(selected table assignment order).length=oldAxes.prod) (hrank:oldAxes.prod≤newAxes.prod):
    ∃t ≤ wholeBound oldAxes newAxes oldp newp table order assignment,SemiprimeD1StackCalls.run program t
      (initial (tape table) (orderTape order) assignment (vectorBits (oldAxes.map unary)) oldp (vectorBits (newAxes.map unary)) newp)=
      some (done oldAxes newAxes oldp newp (tape table) (orderTape order) assignment (selected table assignment order)):=by
  obtain ⟨t,ht,h⟩:=source_trace oldAxes newAxes ho hn oldp newp table order assignment hshape hrank
  obtain ⟨out,he,hAt⟩:=h []
    (initial (tape table) (orderTape order) assignment (vectorBits (oldAxes.map unary)) oldp (vectorBits (newAxes.map unary)) newp) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl
    (result oldAxes newAxes oldp newp (tape table) (orderTape order) assignment (selected table assignment order)) [] out hAt
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
end RiemannGaussian.SemiprimeD1StackChildTableEntryExecution
