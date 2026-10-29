/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseAcquisition
import RiemannGaussian.SemiprimeD1StackNormalizedInverseFinishLoop
import RiemannGaussian.SemiprimeD1StackNormalizedInverseFinalCleanup
/-! # Exact whole normalized-inverse output and actual before/after cleanup states -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseEncoding
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackNormalizedInverseOuterView
open SemiprimeD1StackNormalizedInverseAcquisition SemiprimeD1StackNormalizedInverseFinishBuffers
open SemiprimeD1StackNormalizedInverseFinalCleanup
/-- Exact whole acquired native array, merely a proof/output specification. -/
def outputWords (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) := acquired a q width
/-- Actual outer-loop stopped bank BEFORE any final row reversal or cleanup. -/
def ready (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) : Words :=
  outer a q width 0 q (outputWords a q width).reverse
/-- Actual chronological output and retained counters BEFORE the real final54-field sweep. -/
def beforeCleanup (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) : Words :=
  finishBuffers (ready a q width) [] (tape (outputWords a q width))
/-- Every one of58 stopped fields: retain original array/q/W and only the acquired output. -/
def result (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) : Stack→List Bool :=
  Function.update (input (tape a) (unary q) width) (aux .output) (tape (outputWords a q width))
/-- True halted state, with both transient flags and the real outer return stack empty. -/
def done (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) : C.State Stack Label :=
  ⟨none,none,none,result a q width,[]⟩
/-- The actual ready prefix/output words are exactly the final physical reversal's honest input view. -/
theorem ready_finish (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    finishBuffers (ready a q width) (tape (outputWords a q width).reverse) [false]=ready a q width := by
  apply congrArg (fun f=>({ready a q width with auxiliary:=f}:Words))
  funext k;cases k <;> rfl
/-- The complete actual54-field cleanup has EXACTLY the declared source result, with no hidden retained work. -/
theorem clean_before (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    cleanStore (store (beforeCleanup a q width))=result a q width := by
  classical
  funext k
  by_cases h:retained k
  · rw [cleanStore,ite_eq_left h]
    rcases h with h|h|h|h <;> subst k <;> rfl
  · rw [cleanStore,ite_eq_right h]
    have hko:k≠aux .output :=fun he=>h (Or.inr (Or.inr (Or.inr he)))
    rw [result,Function.update_of_ne hko]
    rcases k with k|k
    · have ht:k≠R.aux .template := fun he=>h (Or.inl (congrArg rational he))
      change []=(if k=R.aux .template then width else [])
      rw [ite_eq_right ht]
    · rcases k with ⟨r,den⟩|k
      · rfl
      · cases k <;> first
        | rfl
        | exact (h (Or.inr (Or.inl rfl))).elim
        | exact (h (Or.inr (Or.inr (Or.inl rfl)))).elim
end RiemannGaussian.SemiprimeD1StackNormalizedInverseEncoding
