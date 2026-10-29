/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryFactorChecks
/-! # Actual factor multiplication and two-direction equality checks against retained N -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryValidation
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryEncoding
open SemiprimeD1StackPackedFactorRecoveryPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeD1StackPackedFactorRecoveryFactorChecks
namespace P
export SemiprimeD1StackPackedFactorRecoveryCopies (multiply_input multiply_factor)
end P
/-- Exact physically computed product bytes. -/
def productWord (small large : List Bool) : List Bool := (SemiprimeBitArithmetic.mulBits small large).bits
/-- Own cost for both factor copies and the complete actual multiplier. -/
def productTime (small large : List Bool) : ℕ := (5*small.length+4)+(5*large.length+4)+multiplyTime small large
/-- Both factors are physically copied into the real multiplier; only its actual product remains. -/
theorem product_run (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (v : SemiprimeD1StackBinarySquareRoot.Aux→List Bool) (small large : List Bool) :
    Runs program (productTime small large) (ctl (.copy .productLeft))
      (work r m v small large (X.payload [] [] [] [] [] [] [] [] []) (W.store [] [] [] [] []))
      (ctl (.copy .productCompare))
      (work r m v small large (X.payload [] [] [] [] (productWord small large) [] [] [] []) (W.store [] [] [] [] [])) := by
  let a:=A.store [] [] [] []
  let w:=W.store [] [] [] [] []
  let u:=words small large [] []
  have h0:=P.multiply_input .productLeft (ctl (.copy .productLeft)) (ctl (.copy .productRight))
    r m a w v u [] [] [] [] [] [] [] [] [] small rfl rfl rfl rfl
  simp only [List.append_nil] at h0
  have h1:=P.multiply_factor .productRight (ctl (.copy .productRight)) (ctl .product)
    r m a w v u small [] [] [] [] [] [] [] [] large rfl rfl rfl rfl
  simp only [List.append_nil] at h1
  have h2:=multiply_call r m a w v u small large (ctl .product) (ctl (.copy .productCompare)) rfl
  exact join (join h0 h1) h2
/-- Exact own cost of the two real numeric comparisons and their actual FALSE pops. -/
def equalityTime (n product : List Bool) : ℕ :=
  (5*product.length+4)+(5*n.length+4)+compareTime product n+1+
    (5*n.length+4)+(5*product.length+4)+compareTime n product+1
/-- Product=N is physically checked in BOTH numeric directions, consuming each computed answer. -/
theorem equality_run (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (v : SemiprimeD1StackBinarySquareRoot.Aux→List Bool) (small large n : List Bool)
    (hn : r R.originalInput=n)
    (hp : SemiprimeD1StackWordLessExecution.answer (productWord small large) n=false)
    (hq : SemiprimeD1StackWordLessExecution.answer n (productWord small large)=false) :
    Runs program (equalityTime n (productWord small large)) (ctl (.copy .productCompare))
      (work r m v small large (X.payload [] [] [] [] (productWord small large) [] [] [] []) (W.store [] [] [] [] []))
      (ctl .clearProduct)
      (work r m v small large (X.payload [] [] [] [] (productWord small large) [] [] [] []) (W.store [] [] [] [] [])) := by
  let a:=A.store [] [] [] []
  let x:=X.payload [] [] [] [] (productWord small large) [] [] [] []
  let u:=words small large [] []
  have h0:=copy_left .productCompare (ctl (.copy .productCompare)) (ctl (.copy .numberCompare))
    r m a x v u [] [] [] [] [] (productWord small large) rfl rfl rfl rfl
  simp only [List.append_nil] at h0
  have h1:=copy_right .numberCompare (ctl (.copy .numberCompare)) (ctl .lessProduct)
    r m a x v u (productWord small large) [] [] [] [] n rfl rfl hn rfl
  simp only [List.append_nil] at h1
  have h2:=compare_call r m a x v u (productWord small large) n (ctl .lessProduct) (ctl .productFlag) rfl
  rw [hp] at h2
  have h3:=pop_false (ctl .productFlag) (ctl (.copy .reverseNumber)) (ctl (.abort 0)) (ctl (.abort 0))
    (compare W.output) (work r m v small large x (W.store [] [] [] [] [false])) [] rfl rfl
  rw [work,view_compare,compare_output] at h3
  have h4:=copy_left .reverseNumber (ctl (.copy .reverseNumber)) (ctl (.copy .reverseProduct))
    r m a x v u [] [] [] [] [] n rfl rfl hn rfl
  simp only [List.append_nil] at h4
  have h5:=copy_right .reverseProduct (ctl (.copy .reverseProduct)) (ctl .lessNumber)
    r m a x v u n [] [] [] [] (productWord small large) rfl rfl rfl rfl
  simp only [List.append_nil] at h5
  have h6:=compare_call r m a x v u n (productWord small large) (ctl .lessNumber) (ctl .numberFlag) rfl
  rw [hq] at h6
  have h7:=pop_false (ctl .numberFlag) (ctl .clearProduct) (ctl (.abort 0)) (ctl (.abort 0))
    (compare W.output) (work r m v small large x (W.store [] [] [] [] [false])) [] rfl rfl
  rw [work,view_compare,compare_output] at h7
  exact join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7
/-- Physical final data retains both source banks and compact factors, with a literal TRUE singleton. -/
def result (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (v : SemiprimeD1StackBinarySquareRoot.Aux→List Bool) (small large : List Bool) : Stack→List Bool :=
  view r m (A.store [] [] [] []) (X.payload [] [] [] [] [] [] [] [] []) (W.store [] [] [] [] [])
    v (words small large [true] [])
/-- The actual product is drained BEFORE success is physically pushed. -/
theorem finish_run (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (v : SemiprimeD1StackBinarySquareRoot.Aux→List Bool) (small large : List Bool) :
    Runs program ((productWord small large).length+1+1) (ctl .clearProduct)
      (work r m v small large (X.payload [] [] [] [] (productWord small large) [] [] [] []) (W.store [] [] [] [] []))
      (ctl .done) (result r m v small large) := by
  have h0:=drain_call (ctl .clearProduct) (ctl .success) (multiply (.inl .right))
    (work r m v small large (X.payload [] [] [] [] (productWord small large) [] [] [] []) (W.store [] [] [] [] []))
    (productWord small large) rfl rfl
  rw [work,view_multiply,SemiprimeD1StackMultiplierExecution.payload_acc] at h0
  have h1:=push_bit (ctl .success) (ctl .done) (aux .status) true
    (work r m v small large (X.payload [] [] [] [] [] [] [] [] []) (W.store [] [] [] [] [])) rfl
  rw [work,view_aux,words_update] at h1
  exact join h0 h1
/-- Every actual comparison, copy, multiply, flag read and final drain is counted. -/
def time (n small large : List Bool) : ℕ :=
  SemiprimeD1StackPackedFactorRecoveryFactorChecks.time small+
    SemiprimeD1StackPackedFactorRecoveryFactorChecks.time large+productTime small large+
      equalityTime n (productWord small large)+((productWord small large).length+1+1)
/-- ONE common complete physical validation is used by square and distinct-prime branches. -/
theorem validate_run (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (v : SemiprimeD1StackBinarySquareRoot.Aux→List Bool) (n small large : List Bool)
    (hn : r R.originalInput=n)
    (hs : SemiprimeD1StackWordLessExecution.answer small [false,true]=false)
    (hl : SemiprimeD1StackWordLessExecution.answer large [false,true]=false)
    (hp : SemiprimeD1StackWordLessExecution.answer (productWord small large) n=false)
    (hq : SemiprimeD1StackWordLessExecution.answer n (productWord small large)=false) :
    Runs program (time n small large) (ctl (.copy .checkSmall))
      (work r m v small large (X.payload [] [] [] [] [] [] [] [] []) (W.store [] [] [] [] []))
      (ctl .done) (result r m v small large) := by
  have h0:=factor_run false r m v small large (X.payload [] [] [] [] [] [] [] [] []) hs
  have h1:=factor_run true r m v small large (X.payload [] [] [] [] [] [] [] [] []) hl
  have h2:=product_run r m v small large
  have h3:=equality_run r m v small large n hn hp hq
  have h4:=finish_run r m v small large
  exact join (join (join (join h0 h1) h2) h3) h4
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryValidation
