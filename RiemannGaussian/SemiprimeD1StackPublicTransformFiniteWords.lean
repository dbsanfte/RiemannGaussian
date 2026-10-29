/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformOriginal
import RiemannGaussian.SemiprimeD1StackWordVectorFinite
/-! # Two complete original word families, preserving raw assignment order -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformFiniteWords
open SemiprimeD1StackWordVectorSpec SemiprimeBitArithmetic
/-- Original consecutive word coordinates, used only as a semantic view. -/
def halfWord (width : List Bool) (n : ℕ) (input : Fin (n*width.length+n*width.length)→Bool)
    (second : Bool) (j : Fin n) : List Bool :=
  List.ofFn (fun b : Fin width.length=>input ⟨(if second then n*width.length else 0)+j.val*width.length+b.val,by
    have h:=Nat.mul_le_mul_right width.length (show j.val+1≤n by omega)
    rw [Nat.add_mul,Nat.one_mul] at h
    split <;> omega⟩)
/-- Every physically acquired block has the original word-before-bit coordinates. -/
theorem block_half (width : List Bool) (n : ℕ) (input : Fin (n*width.length+n*width.length)→Bool)
    (second : Bool) (j : Fin n) :
    (((List.ofFn input).drop (if second then n*width.length else 0)).drop (j.val*width.length)).take width.length=
      halfWord width n input second j := by
  have h:=Nat.mul_le_mul_right width.length (show j.val+1≤n by omega)
  rw [Nat.add_mul,Nat.one_mul] at h
  rw [List.drop_drop]
  apply List.ext_getElem
  · simp only [List.length_take,List.length_drop,List.length_ofFn,halfWord,List.length_ofFn]
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  · intro b hb hb'
    simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn,halfWord]
/-- Two actual vector calls consume the two original halves with NO word getter
or vector-family premise on the executing machine. -/
theorem half_blocks (width : List Bool) (n : ℕ) (input : Fin (n*width.length+n*width.length)→Bool)
    (second : Bool) (j : Fin n) :
    SemiprimeD1StackExprDotSpec.wordAt
      (blocks width n ((List.ofFn input).drop (if second then n*width.length else 0))) j.val=
      halfWord width n input second j := by
  have hfull : n*width.length≤((List.ofFn input).drop (if second then n*width.length else 0)).length := by
    simp only [List.length_drop,List.length_ofFn]
    cases second <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  rw [SemiprimeD1StackExprDotSpec.wordAt,blocks_get_take width n _ j.val j.isLt hfull,Option.getD_some]
  exact block_half width n input second j
/-- Both acquired original vectors have their literal finite half-word order. -/
theorem acquired_halves (bits : List Bool) (second : Bool)
    (input : Fin (SemiprimeD1StackPublicTransformMetadata.size bits second*(SemiprimeD1StackPublicTransformMetadata.cached bits).length+
      SemiprimeD1StackPublicTransformMetadata.size bits second*(SemiprimeD1StackPublicTransformMetadata.cached bits).length)→Bool)
    (j : Fin (SemiprimeD1StackPublicTransformMetadata.size bits second)) :
    SemiprimeD1StackPublicTransformOriginal.input bits (List.ofFn input) second j=
      halfWord (SemiprimeD1StackPublicTransformMetadata.cached bits) _ input false j ∧
    SemiprimeD1StackPublicTransformOriginal.output bits (List.ofFn input) second j=
      halfWord (SemiprimeD1StackPublicTransformMetadata.cached bits) _ input true j := by
  have hn : (SemiprimeD1StackPublicTransformWords.countWord
      (SemiprimeD1StackPublicTransformMetadata.rootData bits) second).length=
      SemiprimeD1StackPublicTransformMetadata.size bits second := by
    change (SemiprimeD1StackPublicTransformMetadata.count bits second).length=_
    rw [SemiprimeD1StackPublicTransformMetadata.count_unary,
      SemiprimeD1StackUnaryDivmod.unary,List.length_replicate]
  constructor
  · change SemiprimeD1StackExprDotSpec.wordAt (blocks _ _ _) _=_
    rw [hn]
    exact half_blocks _ _ input false j
  · change SemiprimeD1StackExprDotSpec.wordAt (blocks _ _ _) _=_
    rw [hn]
    change SemiprimeD1StackExprDotSpec.wordAt
      (blocks (SemiprimeD1StackPublicTransformMetadata.cached bits) _
        ((List.ofFn input).drop (_*(SemiprimeD1StackPublicTransformMetadata.cached bits).length))) _=_
    rw [hn]
    exact half_blocks _ _ input true j
end RiemannGaussian.SemiprimeD1StackPublicTransformFiniteWords
