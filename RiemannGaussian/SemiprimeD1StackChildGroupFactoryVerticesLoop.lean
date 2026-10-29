/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexBodyView
/-! # Entire actual all-owner/all-factor vertex loop
Every physical marker consumes one actual byte and executes both whole scope
and original-order sources before a real binary vertex increment. Isolated
vertices are included. No vertex enumeration/permutation/count supplier runs.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesLoop
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryWiring
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryPrimitives
open SemiprimeD1StackProcedureTrace
namespace Body
export SemiprimeD1StackChildGroupFactoryVertexBody (Ready result timeBound source_trace)
end Body
namespace BV
export SemiprimeD1StackChildGroupFactoryVertexBodyView (Protected result_other result_key result_ready)
end BV
namespace Work
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (freshRole)
end Work
namespace Inc
export SemiprimeD1StackChildGroupFactoryVertexIncrement (successor)
end Inc
namespace Points
export SemiprimeD1StackChildGroupFactoryOldPortParse (Point records)
end Points
namespace Buckets
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (Bucket records)
end Buckets
/-- The actual unread-marker word is untouched by either whole body source or the real increment. -/
theorem todo_protected:BV.Protected (aux .vertexTodo):=by
  constructor
  all_goals first | (intro j;fin_cases j <;> decide) | decide
/-- The actual cached complete old-port tape survives every vertex. -/
theorem points_protected:BV.Protected (aux .oldEndpoints):=by
  constructor
  all_goals first | (intro j;fin_cases j <;> decide) | decide
/-- The actual cached complete nested bucket tape survives every vertex. -/
theorem buckets_protected:BV.Protected (aux .buckets):=by
  constructor
  all_goals first | (intro j;fin_cases j <;> decide) | decide
/-- Exact actual marker pop bank. -/
def popped (before:Stack→List Bool) (todo:List Bool):Stack→List Bool:=Function.update before (aux .vertexTodo) todo
/-- Physically consuming a marker changes none of the actual required work-cache readiness. -/
theorem popped_ready (before:Stack→List Bool) (todo:List Bool) (hr:Body.Ready before):Body.Ready (popped before todo):=by
  constructor
  · intro j hj
    have hn:Work.freshRole j≠aux .vertexTodo:=by fin_cases j <;> decide
    exact (Function.update_of_ne hn _ _).trans (hr.work j hj)
  · intro k;simpa [popped,arithmetic,aux] using hr.arithmetic_clean k
  · intro k;simpa [popped,ordinal,aux] using hr.ordinal_clean k
  · simpa [popped,aux] using hr.oldReader_empty
  · simpa [popped,aux] using hr.portBank_empty
  · simpa [popped,aux] using hr.portHistory_empty
  · simpa [popped,aux] using hr.orderBank_empty
  · simpa [popped,aux] using hr.orderHistory_empty
/-- Actual loop EOF still executes its real empty pop. -/
def atEOF (before:Stack→List Bool):Stack→List Bool:=Function.update before (aux .vertexTodo) []
/-- Complete actual vertex-loop result; counter words are actual add-one outputs, not supplied ordinals. -/
def result:List Bool→(Stack→List Bool)→List Points.Point→List Buckets.Bucket→List Bool→Stack→List Bool
  | [],before,_,_,_=>atEOF before
  | _::todo,before,points,buckets,key=>result todo
      (Body.result (popped before todo) points buckets key) points buckets (Inc.successor key)
/-- Sum all actual per-marker pops/whole bodies, plus the real final EOF pop. -/
def timeBound:List Bool→(Stack→List Bool)→List Points.Point→List Buckets.Bucket→List Bool→Nat
  | [],_,_,_,_=>1
  | _::todo,before,points,buckets,key=>1+Body.timeBound (popped before todo) points buckets key+
      timeBound todo (Body.result (popped before todo) points buckets key) points buckets (Inc.successor key)
/-- Exact one physical vertex marker; both actual bit values choose the SAME real body. -/
theorem marker_trace (b:Bool) (todo:List Bool) (before:Stack→List Bool)
    (ht:before (aux .vertexTodo)=b::todo):
    Runs program 1 (.local 9 4) before (.local 9 5) (popped before todo):=by
  have h:=pop_run (.local 9 4) (.local 15 3) (.local 9 5) (.local 9 5) (aux .vertexTodo) before (b::todo) rfl ht
  cases b <;> simpa only [popped,List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] using h
/-- Exact actual vertex-loop EOF transition to the final two output reversals. -/
theorem eof_trace (before:Stack→List Bool) (ht:before (aux .vertexTodo)=[]):
    Runs program 1 (.local 9 4) before (.local 15 3) (atEOF before):=by
  have h:=pop_run (.local 9 4) (.local 15 3) (.local 9 5) (.local 9 5) (aux .vertexTodo) before [] rfl ht
  simpa only [atEOF,List.head?_nil,List.tail_nil,SemiprimeD1StackBytecode.choose] using h
/-- Whole actual all-vertex traversal, including every owner/factor marker and isolated vertex. -/
theorem source_trace (todo:List Bool) (before:Stack→List Bool) (points:List Points.Point) (buckets:List Buckets.Bucket) (key:List Bool)
    (htodo:before (aux .vertexTodo)=todo) (hp:before (aux .oldEndpoints)=Points.records points)
    (hb:before (aux .buckets)=Buckets.records buckets) (hk:before (aux .vertexKey)=key) (hr:Body.Ready before):
    ∃t≤timeBound todo before points buckets key,
      Runs program t (.local 9 4) before (.local 15 3) (result todo before points buckets key):=by
  induction todo generalizing before key with
  | nil=>exact ⟨1,le_rfl,eof_trace before htodo⟩
  | cons b todo ih=>
    have h0:=marker_trace b todo before htodo
    obtain ⟨x,hx,h1⟩:=Body.source_trace (popped before todo) points buckets key
      (by simpa [popped,aux] using hp) (by simpa [popped,aux] using hb)
      (by simpa [popped,aux] using hk) (popped_ready _ _ hr)
    let after:=Body.result (popped before todo) points buckets key
    have ht':after (aux .vertexTodo)=todo:=
      (BV.result_other _ _ _ _ _ todo_protected).trans (Function.update_self _ _ _)
    have hp':after (aux .oldEndpoints)=Points.records points:=by
      dsimp only [after]
      rw [BV.result_other _ _ _ _ _ points_protected]
      simpa [popped,aux] using hp
    have hb':after (aux .buckets)=Buckets.records buckets:=by
      dsimp only [after]
      rw [BV.result_other _ _ _ _ _ buckets_protected]
      simpa [popped,aux] using hb
    have hk':after (aux .vertexKey)=Inc.successor key:=BV.result_key _ _ _ _
    have hr':Body.Ready after:=BV.result_ready _ _ _ _ (popped_ready _ _ hr)
    obtain ⟨y,hy,h2⟩:=ih after (Inc.successor key) ht' hp' hb' hk' hr'
    refine ⟨1+x+y,?_,?_⟩
    · dsimp only [timeBound]
      dsimp only [after] at hy
      omega
    · have hwhole:=join h0 (join h1 h2)
      simpa only [result,Nat.add_assoc] using hwhole
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesLoop
