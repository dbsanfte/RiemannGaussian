/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffinePrimitives
import RiemannGaussian.SemiprimeD1StackRecoveryAffineView
/-! # Actual literal singleton-ONE affine empty product, even q0 and W0 -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSeed
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView SemiprimeD1StackRecoveryAffinePrimitives
open SemiprimeD1StackProcedureTrace
/-- Ten actual literal pushes construct the exact original singleton-ONE array and preserve every other word. -/
theorem seed_pushes (before:Stack→List Bool):
    Runs program 10 (.local (.seedArray 0)) before (.local .slopeLoop)
      (Function.update before (aux .array) (oneArray++before (aux .array))):=by
  let d0:=before
  let d1:=Function.update d0 (aux .array) (false::d0 (aux .array))
  have h0:=push_run (.local (.seedArray 0)) (.local (.seedArray 1)) (aux .array) false d0 rfl
  change Runs program 1 _ _ _ d1 at h0
  let d2:=Function.update d1 (aux .array) (false::d1 (aux .array))
  have h1:=push_run (.local (.seedArray 1)) (.local (.seedArray 2)) (aux .array) false d1 rfl
  change Runs program 1 _ _ _ d2 at h1
  let d3:=Function.update d2 (aux .array) (true::d2 (aux .array))
  have h2:=push_run (.local (.seedArray 2)) (.local (.seedArray 3)) (aux .array) true d2 rfl
  change Runs program 1 _ _ _ d3 at h2
  let d4:=Function.update d3 (aux .array) (true::d3 (aux .array))
  have h3:=push_run (.local (.seedArray 3)) (.local (.seedArray 4)) (aux .array) true d3 rfl
  change Runs program 1 _ _ _ d4 at h3
  let d5:=Function.update d4 (aux .array) (false::d4 (aux .array))
  have h4:=push_run (.local (.seedArray 4)) (.local (.seedArray 5)) (aux .array) false d4 rfl
  change Runs program 1 _ _ _ d5 at h4
  let d6:=Function.update d5 (aux .array) (true::d5 (aux .array))
  have h5:=push_run (.local (.seedArray 5)) (.local (.seedArray 6)) (aux .array) true d5 rfl
  change Runs program 1 _ _ _ d6 at h5
  let d7:=Function.update d6 (aux .array) (true::d6 (aux .array))
  have h6:=push_run (.local (.seedArray 6)) (.local (.seedArray 7)) (aux .array) true d6 rfl
  change Runs program 1 _ _ _ d7 at h6
  let d8:=Function.update d7 (aux .array) (false::d7 (aux .array))
  have h7:=push_run (.local (.seedArray 7)) (.local (.seedArray 8)) (aux .array) false d7 rfl
  change Runs program 1 _ _ _ d8 at h7
  let d9:=Function.update d8 (aux .array) (true::d8 (aux .array))
  have h8:=push_run (.local (.seedArray 8)) (.local (.seedArray 9)) (aux .array) true d8 rfl
  change Runs program 1 _ _ _ d9 at h8
  let d10:=Function.update d9 (aux .array) (true::d9 (aux .array))
  have h9:=push_run (.local (.seedArray 9)) (.local .slopeLoop) (aux .array) true d9 rfl
  change Runs program 1 _ _ _ d10 at h9
  have h:=join (join (join (join (join (join (join (join (join (h0) h1) h2) h3) h4) h5) h6) h7) h8) h9
  have he:d10=Function.update before (aux .array) (oneArray++before (aux .array)):=by
    simp only [d10,d9,d8,d7,d6,d5,d4,d3,d2,d1,d0,Function.update_self,Function.update_idem]
    rfl
  rw [he] at h
  exact h
/-- The actual EMPTY array role becomes literal ONE regardless of the retained q and fitted W. -/
theorem seed_run (w:Words) (ha:w.added .array=[]):
    Runs program 10 (.local (.seedArray 0)) (bank w) (.local .slopeLoop)
      (bank {w with added:=Function.update w.added .array oneArray}):=by
  have h:=seed_pushes (bank w)
  change Runs program 10 _ _ _ (Function.update (bank w) (aux .array) (oneArray++w.added .array)) at h
  rw [ha,List.append_nil,update_added] at h
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSeed
