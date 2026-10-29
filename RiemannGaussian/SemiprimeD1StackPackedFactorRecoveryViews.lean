/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryHalves
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryValidation
/-! # Clean actual source-cache boundaries, without concrete graph unfolding -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryViews
open SemiprimeD1StackPackedFactorRecovery SemiprimeD1StackPackedFactorRecoveryEncoding
/-- The four real adder words are all physically empty at a clean boundary. -/
theorem empty_adder : A.store [] [] [] []=(fun _=>[]) := by funext k;cases k <;> rfl
/-- The nine real multiplier words are all physically empty at a clean boundary. -/
theorem empty_multiply : X.payload [] [] [] [] [] [] [] [] []=(fun _=>[]) := by
  funext k
  rcases k with k|k|k
  · cases k <;> rfl
  · fin_cases k <;> rfl
  · cases k <;> rfl
/-- The five comparison words are all physically empty after consuming the answer. -/
theorem empty_compare : W.store [] [] [] [] []=(fun _=>[]) := by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k;rfl
/-- The standard boundary retains every source cache and exposes all temporary words as EMPTY. -/
def clean (r : R.Stack→List Bool) (m : SemiprimeD1StackPackedRootMetadata.Stack→List Bool)
    (v : SemiprimeD1StackBinarySquareRoot.Aux→List Bool) (u : Aux→List Bool) : Stack→List Bool :=
  view r m (fun _=>[]) (fun _=>[]) (fun _=>[]) v u
/-- A wholly unused square-root bank is exactly the physical zero bank. -/
theorem clean_zero (r : R.Stack→List Bool) (u : Aux→List Bool) :
    clean r (fun _=>[]) (fun _=>[]) u=bank r (fun _=>[]) u := by
  funext k
  rcases k with k|k|k
  · rfl
  · rcases k with k|k|k|k|k <;> rfl
  · rfl
/-- The full frozen SQ halt provides the exact acquired clean bank with every metadata word retained. -/
theorem squareRoot_clean (r : R.Stack→List Bool) (d : List Bool) (u : Aux→List Bool) :
    bank r (SemiprimeD1StackBinarySquareRootEncoding.result d) u=
      clean r (SemiprimeD1StackBinarySquareRootEncoding.retained d [])
        (SemiprimeD1StackBinarySquareRootEncoding.words [] (SemiprimeD1StackBinarySquareRootArithmetic.output d)) u := rfl
/-- Both numerator paths have exactly this physically empty arithmetic bank. -/
theorem phase_clean (r m root small large) :
    SemiprimeD1StackPackedFactorRecoveryHalves.phase r m root small large (A.store [] [] [] [])=
      clean r m (SemiprimeD1StackBinarySquareRootEncoding.words [] root) (words small large [] []) := by
  rw [SemiprimeD1StackPackedFactorRecoveryHalves.phase,empty_adder]
  rfl
/-- The common validation entry has the same complete clean source-cache projection. -/
theorem validation_clean (r m v small large) :
    SemiprimeD1StackPackedFactorRecoveryFactorChecks.work r m v small large
      (X.payload [] [] [] [] [] [] [] [] []) (W.store [] [] [] [] [])=
      clean r m v (words small large [] []) := by
  rw [SemiprimeD1StackPackedFactorRecoveryFactorChecks.work,empty_adder,empty_multiply,empty_compare]
  rfl
/-- Common validation success retains every source word and only fills physical status TRUE. -/
theorem result_clean (r m v small large) :
    SemiprimeD1StackPackedFactorRecoveryValidation.result r m v small large=
      clean r m v (words small large [true] []) := by
  rw [SemiprimeD1StackPackedFactorRecoveryValidation.result,empty_adder,empty_multiply,empty_compare]
  rfl
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryViews
