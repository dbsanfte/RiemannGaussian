/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesLoop
/-! # Exact complete all-vertex ordered logs and retained physical bank
These are projections of the actual marker-loop result, including empty and
isolated vertices. Actual binary add-one outputs determine every query key.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesLoopView
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryVerticesLoop
namespace View
export SemiprimeD1StackChildGroupFactoryVertexBodyView
  (result_vertexHistory result_factorHistory)
end View
namespace Log
export SemiprimeD1StackChildGroupFactoryWordLog (row)
end Log
namespace Unary
export SemiprimeD1StackPortOrdinalStream (result)
end Unary
namespace Left
export SemiprimeD1StackChildGroupFactoryLeftPortsLoop (portWords)
end Left
namespace Old
export SemiprimeD1StackChildGroupFactoryOldPortsLoop (orderWords)
end Old
/-- Literal forward rows whose reversals are logged by the real scope source. -/
def scopeRows : List Bool → List Buckets.Bucket → List Bool → List Bool
  | [],_,_=>[]
  | _::todo,buckets,key=>Log.row (Unary.result (Left.portWords buckets key)) ++
      scopeRows todo buckets (Inc.successor key)
/-- Literal forward rows whose reversals are logged by the real order source. -/
def orderRows : List Bool → List Points.Point → List Buckets.Bucket → List Bool → List Bool
  | [],_,_,_=>[]
  | _::todo,points,buckets,key=>Log.row (Unary.result (Old.orderWords buckets points key)) ++
      orderRows todo points buckets (Inc.successor key)
/-- Final actual binary counter word after all physical marker iterations. -/
def finalKey : List Bool → List Bool → List Bool
  | [],key=>key
  | _::todo,key=>finalKey todo (Inc.successor key)
/-- Every protected source/cache word survives all marker iterations. -/
theorem result_other (todo:List Bool) (before:Stack→List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool) (k:Stack)
    (hk:BV.Protected k) (ht:k≠aux .vertexTodo):
    result todo before points buckets key k=before k:=by
  induction todo generalizing before key with
  | nil=>simp only [result,atEOF,Function.update_of_ne ht]
  | cons b todo ih=>
    rw [result,ih,BV.result_other _ _ _ _ _ hk]
    exact Function.update_of_ne ht _ _
/-- The marker tape is genuinely exhausted at the stopped loop boundary. -/
theorem result_todo (todo:List Bool) (before:Stack→List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool):
    result todo before points buckets key (aux .vertexTodo)=[]:=by
  induction todo generalizing before key with
  | nil=>change Function.update before (aux .vertexTodo) [] (aux .vertexTodo)=[]
         exact Function.update_self _ _ _
  | cons b todo ih=>exact ih _ _
/-- All physical query/ordinal/arithmetic readiness is preserved by the complete loop. -/
theorem result_ready (todo:List Bool) (before:Stack→List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool) (hr:Body.Ready before):
    Body.Ready (result todo before points buckets key):=by
  induction todo generalizing before key with
  | nil=>exact popped_ready before [] hr
  | cons b todo ih=>exact ih _ _ (BV.result_ready _ _ _ _ (popped_ready _ _ hr))
/-- Exact complete reversed scope log, before the paid final reversal. -/
theorem result_vertexHistory (todo:List Bool) (before:Stack→List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool):
    result todo before points buckets key (aux .vertexHistory)=
      (scopeRows todo buckets key).reverse++before (aux .vertexHistory):=by
  induction todo generalizing before key with
  | nil=>simp only [result,atEOF,Function.update_of_ne (by decide : aux .vertexHistory≠aux .vertexTodo),scopeRows,List.reverse_nil,List.nil_append]
  | cons b todo ih=>
    rw [result,ih,View.result_vertexHistory]
    simp only [popped,Function.update_of_ne (by decide : aux .vertexHistory≠aux .vertexTodo),scopeRows,List.reverse_append,List.append_assoc]
/-- Exact complete reversed original-port-order log, before the paid final reversal. -/
theorem result_factorHistory (todo:List Bool) (before:Stack→List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool):
    result todo before points buckets key (aux .factorHistory)=
      (orderRows todo points buckets key).reverse++before (aux .factorHistory):=by
  induction todo generalizing before key with
  | nil=>simp only [result,atEOF,Function.update_of_ne (by decide : aux .factorHistory≠aux .vertexTodo),orderRows,List.reverse_nil,List.nil_append]
  | cons b todo ih=>
    rw [result,ih,View.result_factorHistory]
    simp only [popped,Function.update_of_ne (by decide : aux .factorHistory≠aux .vertexTodo),orderRows,List.reverse_append,List.append_assoc]
/-- Exact generated counter after the last real add-one call. -/
theorem result_key (todo:List Bool) (before:Stack→List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool) (hk:before (aux .vertexKey)=key):
    result todo before points buckets key (aux .vertexKey)=finalKey todo key:=by
  induction todo generalizing before key with
  | nil=>simpa only [result,atEOF,Function.update_of_ne (by decide : aux .vertexKey≠aux .vertexTodo),finalKey] using hk
  | cons b todo ih=>exact ih _ _ (BV.result_key _ _ _ _)
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesLoopView
