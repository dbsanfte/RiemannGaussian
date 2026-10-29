/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueLoop
import RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndicesBounds
/-! # Small-kernel physical-history accumulation bounds
Only proof-side folds occur below. Runtime row acquisition remains the actual
unchanged finite218-role controller; no fold evaluator is supplied to it.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 32000
namespace RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueHistory
open SemiprimeD1StackBooleanFactorCatalogueLoop
open SemiprimeD1StackBooleanFactorCataloguePrimitives
open SemiprimeD1BooleanFactorCatalogueIndices (scopeWords vertex)
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (factorCount)
/-- Mathematical chronological composition of the actual physical row effects. -/
def fold {A : Type} (step : A→List Bool→List Bool) : List A→List Bool→List Bool
  | [],hist=>hist
  | f::fs,hist=>fold step fs (step f hist)
/-- Generic list bound isolates arithmetic from every original descriptor definition. -/
theorem fold_length {A : Type} (step : A→List Bool→List Bool) (C : Nat)
    (hc:∀a hist,(step a hist).length ≤ hist.length+C) (fs : List A) (hist : List Bool) :
    (fold step fs hist).length ≤ hist.length+C*fs.length := by
  induction fs generalizing hist with
  | nil=>simp only [fold,List.length_nil,Nat.mul_zero,Nat.add_zero,le_refl]
  | cons f fs ih=>
    have hi:=ih (step f hist)
    have hh:=hc f hist
    calc
      _ ≤ (step f hist).length+C*fs.length:=hi
      _ ≤ (hist.length+C)+C*fs.length:=Nat.add_le_add_right hh _
      _ = hist.length+C*(f::fs).length:=by simp only [List.length_cons,Nat.mul_add,Nat.mul_one];omega
/-- Exact original ordinal guards identify the actual counter-based history
with the same row effects composed in original factor order. -/
theorem afterRows_fold (bits : List Bool) (n : Nat) (fs : List (Fin (factorCount (bitValue bits))))
    (hseq:fs.map Fin.val=List.range' n fs.length) (hist : List Bool) :
    afterRows bits n fs hist=
      fold (fun f=>DA.afterHistory (vertex (bitValue bits) f) (scopeWords bits f.val)) fs hist := by
  induction fs generalizing n hist with
  | nil=>rfl
  | cons f fs ih=>
    have horder:=SemiprimeD1BooleanFactorCatalogueIndicesBounds.cons_values (bitValue bits) n f fs hseq
    have he:=congrArg (fun i=>DA.afterHistory (vertex (bitValue bits) f) (scopeWords bits i) hist) horder.1
    rw [afterRows,fold,he]
    exact ih (n+1) horder.2 _
end RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueHistory
