/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineLoop
/-! # The actual reverse-catalogue fold is exactly original affine build, including literal empty product -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopOriginal
open SemiprimeD1StackRecoveryAffineLoop SemiprimeD1StackRecoveryAffineLoopView
open SemiprimeRationalBits (RationalWord)
/-- Chronological physical row traversal composes without replaying any source or recopying any accumulated tail. -/
theorem fold_append (width:List Bool) (q:Nat) (cs ds xs:List RationalWord):
    fold width q (cs++ds) xs=fold width q ds (fold width q cs xs):=by
  induction cs generalizing xs with
  | nil=>rfl
  | cons c cs ih=>exact ih (multiply width xs c q)
/-- Exact raw affine array bytes preserve the native RIGHT fold's operand order and ALL fitted scalar operations. -/
theorem fold_original (width:List Bool) (q:Nat) (slopes:List RationalWord):
    fold width q slopes.reverse [SemiprimeJetBits.oneWord]=
      (SemiprimeAffineJetBits.build width q slopes).words.toList:=by
  induction slopes with
  | nil=>rfl
  | cons c cs ih=>
    rw [List.reverse_cons,fold_append,ih]
    simp only [fold,multiply,SemiprimeAffineJetBits.build,SemiprimeAffineJetBits.affine,Array.toArray_toList]
end RiemannGaussian.SemiprimeD1StackRecoveryAffineLoopOriginal
