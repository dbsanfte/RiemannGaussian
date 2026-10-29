/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives
/-! # Original phase metadata values and bounds from the actual acquired guard -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic
open SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives
/-- The actual original phase height acquired by the real divider. -/
def height (M u : Nat) : Nat :=(3*M+u-1)/u
/-- The actual original number of fresh coefficient blocks. -/
def blocks (a u M : Nat) (t : List Bool) : Nat :=height M u*(u-order a t)
/-- Accepted physical guard supplies both strict order bounds, without a supplied i. -/
theorem accepted_bounds (a u : Nat) (t : List Bool) (h : accepted a u t=true) :
    order a t<a ∧ order a t<u :=by
  unfold accepted SemiprimeD1StackPhaseGeometryGuardComponents.accepted at h
  split at h
  · cases h
  · split at h
    · rename_i ha
      exact ⟨ha,of_decide_eq_true h⟩
    · cases h
/-- Accepted paths ALWAYS have a positive actual divisor. -/
theorem accepted_positive (a u : Nat) (t : List Bool) (h : accepted a u t=true) : 0<u :=by
  have hh:=(accepted_bounds a u t h).2
  omega
/-- Height remains bounded unary metadata, even without u≤ M. -/
theorem height_le (M u : Nat) : height M u≤3*M+u :=
  (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
/-- This height is the EXACT original jetHeight/height, without native work transfer. -/
theorem height_original (M u : Nat) : height M u=SemiprimeD1ModeRate.jetHeight M u :=rfl
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic
