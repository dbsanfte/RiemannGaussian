/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryEncoding
/-! # Fixed physical bank views and one-word updates
These functions name fixed tape addresses in proof states only.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryView
open SemiprimeD1StackChildTableEntry SemiprimeD1StackChildTableEntryEncoding
/-- The physical gather view reads exactly its allocated component word. -/
theorem gather_get (old child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool) (k:G.Stack):
    bank old child g t r a (gather k)=g k:=rfl
/-- The physical treeAllocation view reads exactly its allocated component word. -/
theorem treeAllocation_get (old child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool) (k:T.Stack):
    bank old child g t r a (treeAllocation k)=t k:=rfl
/-- The physical reduce view reads exactly its allocated component word. -/
theorem reduce_get (old child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool) (k:R.Stack):
    bank old child g t r a (reduce k)=r k:=rfl
/-- The physical aux view reads exactly its allocated component word. -/
theorem aux_get (old child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool) (k:Aux):
    bank old child g t r a (aux k)=a k:=rfl
/-- Both context projections read all actual fifteen fields, including retained headers and acquired rank/width. -/
theorem context_get (old child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool) (b:Bool) (k:J.Stack):
    bank old child g t r a (context b k)=(if b then child else old) k:=by cases b <;> rfl
/-- A real old tape write updates exactly that physical allocated component. -/
theorem update_old (old child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool) (k:J.Stack) (xs:List Bool):
    Function.update (bank old child g t r a) (context false k) xs=bank (Function.update old k xs) child g t r a:=by
  dsimp only [bank,context]
  simp only [Bool.false_eq_true,ite_false]
  rw [Sum.update_elim_inl]
/-- A real child tape write updates exactly that physical allocated component. -/
theorem update_child (old child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool) (k:J.Stack) (xs:List Bool):
    Function.update (bank old child g t r a) (context true k) xs=bank old (Function.update child k xs) g t r a:=by
  dsimp only [bank,context]
  simp only [ite_true]
  rw [Sum.update_elim_inr,Sum.update_elim_inl]
/-- A real gather tape write updates exactly that physical allocated component. -/
theorem update_gather (old child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool) (k:G.Stack) (xs:List Bool):
    Function.update (bank old child g t r a) (gather k) xs=bank old child (Function.update g k xs) t r a:=by
  dsimp only [bank,gather]
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inl]
/-- A real tree tape write updates exactly that physical allocated component. -/
theorem update_tree (old child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool) (k:T.Stack) (xs:List Bool):
    Function.update (bank old child g t r a) (treeAllocation k) xs=bank old child g (Function.update t k xs) r a:=by
  dsimp only [bank,treeAllocation]
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inl]
/-- A real reduce tape write updates exactly that physical allocated component. -/
theorem update_reduce (old child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool) (k:R.Stack) (xs:List Bool):
    Function.update (bank old child g t r a) (reduce k) xs=bank old child g t (Function.update r k xs) a:=by
  dsimp only [bank,reduce]
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inl]
/-- A real aux tape write updates exactly that physical allocated component. -/
theorem update_aux (old child:J.Stack→List Bool) (g:G.Stack→List Bool) (t:T.Stack→List Bool) (r:R.Stack→List Bool) (a:Aux→List Bool) (k:Aux) (xs:List Bool):
    Function.update (bank old child g t r a) (aux k) xs=bank old child g t r (Function.update a k xs):=by
  dsimp only [bank,aux]
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inr]
end RiemannGaussian.SemiprimeD1StackChildTableEntryView
