/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseChildContextPrimitives
/-! # Actual guard/positive-dimension facts and original context semantics -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
namespace RiemannGaussian.SemiprimeD1StackPhaseChildContextArithmetic
open SemiprimeD1StackPhaseChildContext SemiprimeD1StackPhaseChildContextPrimitives
/-- Actual header-stage success requires BOTH acquired guard and physical nonempty q. -/
def good (a u edges : Nat) (t : List Bool) : Bool :=if accepted a u t then decide (0<count a u edges t) else false
/-- Exact proof-side interpretation of the two physically executed peeks. -/
theorem good_true (a u edges : Nat) (t : List Bool) :
    good a u edges t=true ↔ accepted a u t=true ∧ 0<count a u edges t :=by
  cases ha:accepted a u t with
  | false=>simp only [good,ha,Bool.false_eq_true,ite_false,false_and]
  | true=>simp only [good,ha,ite_true,true_and,decide_eq_true_eq]
/-- Actual accepted height is positive under the ORIGINAL active parent u≤ M fact. -/
theorem height_positive (a u edges : Nat) (t : List Bool) (ha : accepted a u t=true) (huM : u≤ edges) :
    0<SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic.height edges u :=by
  have hu:=SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic.accepted_positive a u t ha
  exact Nat.div_pos (by omega) hu
/-- New outer dimension is positive for every ORIGINAL accepted phase, never a supplied dimension. -/
theorem count_positive (a u edges : Nat) (t : List Bool) (ha : accepted a u t=true) (huM : u≤ edges) :
    0<count a u edges t :=by
  have hi:SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives.order a t<u:=
    (SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic.accepted_bounds a u t ha).2
  change 0<SemiprimeD1StackPhaseWorkingPrecisionMetadataArithmetic.height edges u*
    (u-SemiprimeD1StackPhaseWorkingPrecisionMetadataPrimitives.order a t)
  exact Nat.mul_pos (height_positive a u edges t ha huM) (Nat.sub_pos_of_lt hi)
/-- The actual q field comes from the WHOLE literal P48 acquisition, not an external q operand. -/
theorem count_word (a u edges : Nat) (t p : List Bool) (ha : accepted a u t=true) :
    phase a u edges t p
      (P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.aux .q))=
      SemiprimeD1StackUnaryDivmod.unary (count a u edges t) :=by
  change SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.result a u edges t p
    (SemiprimeD1StackPhaseWorkingPrecisionMetadata.aux .q)=_
  simp only [SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.result,
    SemiprimeD1StackPhaseWorkingPrecisionMetadataExecution.resultCounts,ha,ite_true]
  rfl
/-- Original p is the literal retained BINARY precision input, for the actual old-context source. -/
theorem original_precision_word (a u edges : Nat) (t p : List Bool) :
    phase a u edges t p (P.metadataStack (SemiprimeD1StackPhaseWorkingPrecisionMetadata.aux .precision))=p :=rfl
/-- Exact new UNARY-header encoding is the same existing JetContext ABI. -/
theorem header_cons (axes : List Nat) (q : Nat) :
    header (q::axes)=true::SemiprimeSourceHistogramKeyBits.frame (SemiprimeD1StackUnaryDivmod.unary q) (header axes) :=rfl
/-- Positive old axes and actual positive q satisfy the real context producer's physical guard. -/
theorem child_positive (axes : List Nat) (hp : ∀x∈axes,0<x) (q : Nat) (hq : 0<q) :
    ∀x∈q::axes,0<x :=by
  intro x hx
  rcases List.mem_cons.mp hx with rfl|hx
  · exact hq
  · exact hp x hx
end RiemannGaussian.SemiprimeD1StackPhaseChildContextArithmetic
