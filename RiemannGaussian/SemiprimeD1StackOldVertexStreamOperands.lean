/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOldVertexStreamView
/-! # Exact physical operands of the included whole vertex source
Only three parsed fields and one physically popped activity bit enter the raw
work bank. Four actual caller headers are shared through immutable aliases.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackOldVertexStreamOperands
open SemiprimeD1StackOldVertexStream SemiprimeD1StackOldVertexStreamRoles
open SemiprimeD1StackOldVertexStreamView
/-- Exactly the three parsed source fields and acquired singleton activity. -/
def sparse (parent order scope bit : List Bool) : ChoiceStack→List Bool:=
  Function.update (Function.update (Function.update (Function.update (fun _=>[]) parentRole parent)
    orderRole order) scopeRole scope) X.activity bit
/-- The materialized actual header aliases plus these four work words are the ENTIRE real169 source entry. -/
theorem initial_sparse (i : Inputs) (parent order scope bit : List Bool) :
    materialize i (sparse parent order scope bit)=
      (SemiprimeD1StackChildVertexChoice.initial parent order i.oldAxes i.oldPrecision i.newAxes i.newPrecision scope bit).data:=by
  funext k
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rcases k with k|k
          · rcases k with k|k
            · rfl
            · rcases k with k|k
              · rfl
              · fin_cases k <;> rfl
          · rcases k with k|k
            · rcases k with k|k
              · rfl
              · rcases k with k|k
                · rfl
                · fin_cases k <;> rfl
            · rcases k with k|k
              · cases k <;> rfl
              · rcases k with k|k
                · cases k <;> rfl
                · rcases k with k|k
                  · cases k <;> rfl
                  · cases k <;> rfl
        · rcases k with k|k
          · cases k <;> rfl
          · cases k <;> rfl
    · cases k <;> rfl
  · rcases k with k|k
    · change []=(if _ then [] else [])
      split <;> rfl
    · cases k;rfl
/-- A complete native stopped source whose four headers survive is read through the SAME aliases. -/
theorem materialize_eq (i : Inputs) (source : ChoiceStack→List Bool)
    (h0 : source (axesRole false)=i.oldAxes) (h1 : source (precisionRole false)=i.oldPrecision)
    (h2 : source (axesRole true)=i.newAxes) (h3 : source (precisionRole true)=i.newPrecision) :
    materialize i source=source:=by
  funext k
  unfold materialize
  split_ifs with ha hp hb hq
  · subst k;exact h0.symm
  · subst k;exact h1.symm
  · subst k;exact h2.symm
  · subst k;exact h3.symm
  · rfl
/-- Complete empty work remains empty even at every displaced header role. -/
theorem mask_empty : mask (fun _=>[])=fun _=>[]:=by
  funext k
  unfold mask
  split <;> rfl
end RiemannGaussian.SemiprimeD1StackOldVertexStreamOperands
