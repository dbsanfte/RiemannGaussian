/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryVertexByteBounds
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryRowByteBounds
/-! # Whole actual all-vertex bank bytes have additive, not iterated-runtime growth
Every marker executes the same restored body. The only accumulated words are
its two real ordered row logs, and the key advances by real binary addition.
Prepared duplicate packets give a uniform quartic row bound and quintic total
bank-growth bound, independently of recursive subtree runtimes.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesByteBounds
open SemiprimeD1StackChildGroupFactoryRoles SemiprimeD1StackChildGroupFactoryVerticesLoop
namespace Bytes
export SemiprimeD1StackChildGroupFactoryVertexByteBounds (rowBytes body_word_le)
end Bytes
namespace Code
export SemiprimeD1StackChildGroupFactoryCatalogueCodecs (buckets)
end Code
namespace E
export SemiprimeD1StackChildGroupFactoryBucketParse (Endpoint)
end E
/-- Popping an actual marker shortens its word and retains all other allocations. -/
theorem popped_word_le (before:Stack→List Bool) (todo:List Bool) (b:Bool) (cap:Nat)
    (ht:before (aux .vertexTodo)=b::todo) (hc:∀k,(before k).length≤cap):
    ∀k,(popped before todo k).length≤cap:=by
  intro k
  by_cases hk:k=aux .vertexTodo
  · subst k
    have h:=hc (aux .vertexTodo)
    rw [ht] at h
    simp only [popped,Function.update_self,List.length_cons] at h ⊢
    omega
  · exact (congrArg List.length (Function.update_of_ne hk _ _)).le.trans (hc k)
/-- Complete actual marker-loop stopped bank pays only the sum of actual logged row increments. -/
theorem result_word_le (todo:List Bool) (before:Stack→List Bool) (points:List Points.Point)
    (buckets:List Buckets.Bucket) (key:List Bool) (cap Q:Nat)
    (hr:Body.Ready before) (ht:before (aux .vertexTodo)=todo) (hk:before (aux .vertexKey)=key)
    (hc:∀k,(before k).length≤cap) (hq:∀target,Bytes.rowBytes points buckets target≤Q):
    ∀k,(result todo before points buckets key k).length≤cap+todo.length*Q:=by
  induction todo generalizing before key cap with
  | nil=>
    intro k
    by_cases hn:k=aux .vertexTodo
    · subst k;simp only [result,atEOF,Function.update_self,List.length_nil,Nat.zero_mul,Nat.add_zero];exact Nat.zero_le _
    · simpa only [result,atEOF,Function.update_of_ne hn,List.length_nil,Nat.zero_mul,Nat.add_zero] using hc k
  | cons b todo ih=>
    have hpop:=popped_word_le before todo b cap ht hc
    have hready:=popped_ready before todo hr
    have hkey:popped before todo (aux .vertexKey)=key:=by simpa [popped,aux] using hk
    have hbody:=Bytes.body_word_le (popped before todo) points buckets key hready hkey cap hpop
    let after:=Body.result (popped before todo) points buckets key
    have hafter:∀k,(after k).length≤cap+Q:=by intro k;exact (hbody k).trans (Nat.add_le_add_left (hq key) cap)
    have ht':after (aux .vertexTodo)=todo:=
      (BV.result_other _ _ _ _ _ todo_protected).trans (Function.update_self _ _ _)
    have hk':after (aux .vertexKey)=Inc.successor key:=BV.result_key _ _ _ _
    have hr':Body.Ready after:=BV.result_ready _ _ _ _ hready
    have hi:=ih after (Inc.successor key) (cap+Q) hr' ht' hk' hafter
    intro k
    have h:=hi k
    simpa only [result,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm Q,Nat.add_left_comm Q] using h
/-- Actual internally numbered duplicate-packet scopes/orders give one fixed quintic bank-growth envelope. -/
theorem generated_result_word_le (todo:List Bool) (before:Stack→List Bool) (points:List Points.Point)
    (packets:List (List Bool)) (es:List E.Endpoint) (key:List Bool) (cap S:Nat)
    (hr:Body.Ready before) (ht:before (aux .vertexTodo)=todo) (hk:before (aux .vertexKey)=key)
    (hc:∀k,(before k).length≤cap) (hpack:packets.length≤S) (he:es.length≤S)
    (hpoints:points.length≤S) (htodo:todo.length≤S):
    ∀k,(result todo before points (Code.buckets packets es []) key k).length≤cap+100*(S+1)^5:=by
  have h:=result_word_le todo before points (Code.buckets packets es []) key cap (100*(S+1)^4)
    hr ht hk hc (fun target=>SemiprimeD1StackChildGroupFactoryRowByteBounds.generated_rows_quartic
      packets es points target S hpack he hpoints)
  intro k
  have hk':=h k
  have hm:todo.length*(100*(S+1)^4)≤(S+1)*(100*(S+1)^4):=
    Nat.mul_le_mul_right _ (by omega)
  have heq:(S+1)*(100*(S+1)^4)=100*(S+1)^5:=by ring
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryVerticesByteBounds
