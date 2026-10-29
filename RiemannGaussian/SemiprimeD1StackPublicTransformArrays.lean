/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformMeaning
/-! # Actual acquired vector lengths and finite original word views -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformArrays
open SemiprimeD1StackPublicTransformMetadata SemiprimeD1StackPublicTransformWords
open SemiprimeD1StackPublicTransformQuery SemiprimeMacroEntryBitPrimitives SemiprimeBitArithmetic
/-- Original acquisition fixes both actual vector lengths without an arity answer. -/
theorem inputs_length (bits raw : List Bool) (second : Bool) :
    (inputs (rootData bits) raw second).length=size bits second := by
  rw [inputs,SemiprimeD1StackWordVectorSpec.blocks_length]
  change (count bits second).length=_
  rw [count_unary,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
/-- The second vector has exactly the same physically acquired count. -/
theorem outputs_length (bits raw : List Bool) (second : Bool) :
    (outputs (rootData bits) raw second).length=size bits second := by
  rw [outputs,SemiprimeD1StackWordVectorSpec.blocks_length]
  change (count bits second).length=_
  rw [count_unary,SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
/-- Defaulted lookup is literally the finite view on valid original positions. -/
theorem wordAt_get {n : ℕ} (xs : List (List Bool)) (hn : xs.length=n) (j : Fin n) :
    SemiprimeD1StackExprDotSpec.wordAt xs j.val=xs.get ⟨j.val,by omega⟩ := by
  simp only [SemiprimeD1StackExprDotSpec.wordAt,List.getElem?_eq_getElem (by omega : j.val<xs.length),Option.getD_some,List.get_eq_getElem]
/-- The actual executed vector guard equals canonicality of its complete finite
view, with all repeated words and original order retained. -/
theorem guard_finite {n : ℕ} (cached : List Bool) (xs : List (List Bool)) (hn : xs.length=n) :
    SemiprimeD1StackVectorCanonicalExecution.answer cached xs=true ↔
      ∀j : Fin n,bitValue (SemiprimeD1StackExprDotSpec.wordAt xs j.val)<bitValue cached := by
  rw [SemiprimeD1StackVectorCanonicalExecution.answer_true,List.forall_mem_iff_get]
  constructor
  · intro h j;rw [wordAt_get xs hn j];exact h _
  · intro h j
    have he : j.val<n := by omega
    simpa only [wordAt_get xs hn ⟨j.val,he⟩] using h ⟨j.val,he⟩
/-- Compiled dot expressions depend only on the actually traversed prefix. -/
theorem dot_congr (base : Expr) (stride frequency n : ℕ) (a b : ℕ→List Bool)
    (h : ∀j<n,a j=b j) : dotExpr base stride frequency a n=dotExpr base stride frequency b n := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    simp only [dotExpr,ih (fun j hj=>h j (by omega)),h n (by omega)]
/-- Actual list lookup and original finite wordAt give the SAME compiled source;
no evaluator result or source-size premise is used. -/
theorem dot_finite {n : ℕ} (base : Expr) (stride frequency : ℕ)
    (xs : List (List Bool)) (_hn : xs.length=n) :
    dotExpr base stride frequency (SemiprimeD1StackExprDotSpec.wordAt xs) n=
      dotExpr base stride frequency
        (SemiprimeMacroEntryBitCheck.wordAt (fun j : Fin n=>SemiprimeD1StackExprDotSpec.wordAt xs j.val)) n := by
  apply dot_congr
  intro j hj
  simp only [SemiprimeMacroEntryBitCheck.wordAt,dite_eq_left hj]
end RiemannGaussian.SemiprimeD1StackPublicTransformArrays
