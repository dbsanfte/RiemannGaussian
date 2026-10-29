/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryPrimitives
/-! # Physical exact-count parsing and the square branch -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryCount
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryEncoding
open SemiprimeD1StackPackedFactorRecoveryPrimitives SemiprimeD1StackProcedureTrace
/-- Paid count copying preserves the original actual moment word. -/
theorem copy_count (r : R.Stack→List Bool) (s : S.Stack→List Bool) (c : List Bool)
    (hc : r (R.aux .count)=c) :
    Runs program (5*c.length+4) (ctl (.copy .count)) (bank r s (words [] [] [] []))
      (ctl .countHead) (bank r s (words [] [] c [])) := by
  have h:=copy_call .count (ctl (.copy .count)) (ctl .countHead) rfl
    (bank r s (words [] [] [] [])) c [] hc rfl rfl
  change Runs program _ _ _ _ (Function.update _ (aux .status) (c++[])) at h
  rw [List.append_nil,bank_aux,words_update] at h
  exact h
/-- Exact literal1 requires its TRUE and actual EOF; the count original is untouched. -/
theorem one_run (r : R.Stack→List Bool) (s : S.Stack→List Bool) :
    Runs program 2 (ctl .countHead) (bank r s (words [] [] [true] []))
      (ctl (.copy .squareSmall)) (bank r s (words [] [] [] [])) := by
  have h0:=pop_true (ctl .countHead) (ctl .countOneEof) (ctl .countTwoTrue) (ctl (.abort 0))
    (aux .status) (bank r s (words [] [] [true] [])) [] rfl rfl
  rw [bank_aux,words_update] at h0
  change Runs program 1 _ _ _ (bank r s (words [] [] [] [])) at h0
  have h1:=pop_empty (ctl .countOneEof) (ctl (.copy .squareSmall)) (ctl (.abort 0)) (ctl (.abort 0))
    (aux .status) (bank r s (words [] [] [] [])) rfl rfl
  rw [bank_aux,words_update] at h1
  exact join h0 h1
/-- Exact literal2 requires FALSE, TRUE and actual EOF, rejecting longer encodings. -/
theorem two_run (r : R.Stack→List Bool) (s : S.Stack→List Bool) :
    Runs program 3 (ctl .countHead) (bank r s (words [] [] [false,true] []))
      (ctl (.copy .squareLeft)) (bank r s (words [] [] [] [])) := by
  have h0:=pop_false (ctl .countHead) (ctl .countTwoTrue) (ctl .countOneEof) (ctl (.abort 0))
    (aux .status) (bank r s (words [] [] [false,true] [])) [true] rfl rfl
  rw [bank_aux,words_update] at h0
  change Runs program 1 _ _ _ (bank r s (words [] [] [true] [])) at h0
  have h1:=pop_true (ctl .countTwoTrue) (ctl .countTwoEof) (ctl (.abort 0)) (ctl (.abort 0))
    (aux .status) (bank r s (words [] [] [true] [])) [] rfl rfl
  rw [bank_aux,words_update] at h1
  change Runs program 1 _ _ _ (bank r s (words [] [] [] [])) at h1
  have h2:=pop_empty (ctl .countTwoEof) (ctl (.copy .squareLeft)) (ctl (.abort 0)) (ctl (.abort 0))
    (aux .status) (bank r s (words [] [] [] [])) rfl rfl
  rw [bank_aux,words_update] at h2
  exact join (join h0 h1) h2
/-- The square branch physically copies the actually acquired sum to both factor outputs. -/
theorem square_run (r : R.Stack→List Bool) (s : S.Stack→List Bool) (sumWord : List Bool)
    (hs : r (R.aux .sum)=sumWord) :
    Runs program ((5*sumWord.length+4)+(5*sumWord.length+4)) (ctl (.copy .squareSmall))
      (bank r s (words [] [] [] [])) (ctl (.copy .checkSmall)) (bank r s (words sumWord sumWord [] [])) := by
  have h0:=copy_call .squareSmall (ctl (.copy .squareSmall)) (ctl (.copy .squareLarge)) rfl
    (bank r s (words [] [] [] [])) sumWord [] hs rfl rfl
  change Runs program _ _ _ _ (Function.update _ (aux .small) (sumWord++[])) at h0
  rw [List.append_nil,bank_aux,words_update] at h0
  change Runs program _ _ _ _ (bank r s (words sumWord [] [] [])) at h0
  have h1:=copy_call .squareLarge (ctl (.copy .squareLarge)) (ctl (.copy .checkSmall)) rfl
    (bank r s (words sumWord [] [] [])) sumWord [] hs rfl rfl
  change Runs program _ _ _ _ (Function.update _ (aux .large) (sumWord++[])) at h1
  rw [List.append_nil,bank_aux,words_update] at h1
  exact join h0 h1
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryCount
