/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetCoordinateLinear
import RiemannGaussian.SemiprimeD1IntegerRecoveryAcquisition

/-! # Original CURRENT-table scalar D.5 references and derived child errors
The reference polynomial is constructed from literal current table bytes. Old
coordinate extraction is linear, not multiplicative. Actual child modular
coefficient equality derives the D.5 error; no error/degree/integrality answer is
supplied for this reference.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1CurrentTableRecoveryLicence
open scoped BigOperators
open Polynomial SemiprimeD1JetAlgebra SemiprimeD1JetScalarMap SemiprimeD1JetBoxIndex
  SemiprimeD1JetLiteralLift SemiprimeD1DyadicInteger SemiprimeD1IntegralDeformation
  SemiprimeD1OriginalDeformation SemiprimeD1CurrentTableDeformation
  SemiprimeD1JetCoordinateLinear SemiprimeD1DyadicBounds
noncomputable section

/-- The scalar rational reference comes from ALL actual CURRENT old coefficient words. -/
def reference (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→List (List Bool))
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) : Polynomial ℚ :=
  polynomial (coordinate (dims axes) e he)
    (SemiprimeD1Deformation.polynomial _ (fun x => rational axes (A x)) (fun x => rational axes (B x))
      (wire (constants (dims axes)) n F r a arity owner))

/-- The reference has the ORIGINAL D.8 degree budget, with no degree oracle. -/
theorem reference_degree (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→List (List Bool))
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) :
    (reference axes n F r a arity owner A B e he).natDegree≤
      (Placements n F r a arity owner).length*(2*(2^a)-1) :=
  (polynomial_degree _ _).trans (original_degree _ n F r a arity owner _ _)

/-- Old-coordinate linear extraction commutes with the EXACT original local substitution. -/
theorem reference_local (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→List (List Bool))
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) :
    (reference axes n F r a arity owner A B e he).comp (SemiprimeD1WireKernelPaper.affine a t.val)=
      polynomial (coordinate (dims axes) e he)
        ((currentPolynomial axes n F r a arity owner t A B).map (scalarMap (dims axes) integers.subtype)) := by
  have hsub := SemiprimeD1JetCoordinateLinear.polynomial_comp (coordinate (dims axes) e he)
    (SemiprimeD1Deformation.polynomial _ (fun x => rational axes (A x)) (fun x => rational axes (B x))
      (wire (constants (dims axes)) n F r a arity owner)) (SemiprimeD1WireKernelPaper.affine a t.val)
  have hc : algebraMap ℚ (Algebra (dims axes) ℚ)=constants (dims axes) := Subsingleton.elim _ _
  rw [hc] at hsub
  rw [reference,← hsub,← current_inclusion]

/-- The two original scalar affine-coordinate definitions are exactly the same polynomial. -/
theorem original_affine (a t : ℕ) : SemiprimeD1WireKernelPaper.affine a t=
    SemiprimeD1ScaledHermite.affine (SemiprimeD1HermiteOriginal.alpha a) (SemiprimeD1HermiteNodes.node a t) := by
  simp only [SemiprimeD1WireKernelPaper.affine,SemiprimeD1ScaledHermite.affine,
    SemiprimeD1HermiteOriginal.alpha,SemiprimeD1HermiteNodes.node,Int.cast_ofNat]

/-- ACTUAL child old-coordinate residue equality DERIVES the original retained D.5 error. -/
theorem child_error (axes : List ℕ) (n F r a p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→List (List Bool))
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) (j : ℕ) (bs : List Bool)
    (hchild : coefficient (dims axes) e he
      (scalarMap (dims axes) (reduction p) ((currentPolynomial axes n F r a arity owner t A B).coeff j))=
        (SemiprimeBitArithmetic.bitValue bs:ZMod (2^p))) :
    AtLeast (p:ℤ) ((SemiprimeBitArithmetic.bitValue bs:ℚ)-
      (((reference axes n F r a arity owner A B e he).comp
        (SemiprimeD1ScaledHermite.affine (SemiprimeD1HermiteOriginal.alpha a)
          (SemiprimeD1HermiteNodes.node a t.val))).coeff j)) := by
  rw [← original_affine,reference_local,polynomial_coefficient,Polynomial.coeff_map]
  exact old_coordinate_word_error (dims axes) e he p
    ((currentPolynomial axes n F r a arity owner t A B).coeff j) bs hchild

/-- The reference's original value at zero is integral from the literal source contraction. -/
theorem reference_zero_integral (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→List (List Bool))
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) :
    AtLeast 0 ((reference axes n F r a arity owner A B e he).eval 0) := by
  rw [reference,polynomial_eval,map_zero,original_at_zero]
  have hs : (∑bits,rational axes (A bits)*rational axes (B bits))=
      scalarMap (dims axes) integers.subtype (∑bits,literal axes (A bits)*literal axes (B bits)) := by
    simp only [map_sum,map_mul,rational]
  change AtLeast 0 (coefficient (dims axes) e he _)
  rw [hs,coefficient_scalarMap]
  exact (coefficient (dims axes) e he (∑bits,literal axes (A bits)*literal axes (B bits))).property

/-- ORIGINAL native integer D.5 recovery from actual modular child-coordinate
postconditions. Degree, integrality, weights and the scalar error contract are
ALL derived here; no error/precision/weight/coefficient-answer oracle is supplied. -/
theorem original_word_recovery (axes : List ℕ) (n F r a u p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→List (List Bool))
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e)
    (hu : 0<u) (huM : u≤(Placements n F r a arity owner).length)
    (children : ℕ → Array (List Bool))
    (hchild : ∀t : Fin (SemiprimeD1WireKernelOriginal.size a),
      t.val∈SemiprimeD1HermiteNodes.active a (SemiprimeD1TaperedLoss.height
        (Placements n F r a arity owner).length u) u →
      ∀j<SemiprimeD1JetRecoveryGrid.nodeMultiplicity a (SemiprimeD1TaperedLoss.height
        (Placements n F r a arity owner).length u) u t.val,
      coefficient (dims axes) e he
        (scalarMap (dims axes) (reduction (SemiprimeD1WeightPrecision.precision a
          (Placements n F r a arity owner).length u p t.val))
          ((currentPolynomial axes n F r a arity owner t A B).coeff j))=
        (SemiprimeBitArithmetic.bitValue ((children t.val)[j]?.getD []):ZMod
          (2^SemiprimeD1WeightPrecision.precision a (Placements n F r a arity owner).length u p t.val))) :
    SemiprimeD1IntegerRecoveryResidue.finish p
      (SemiprimeD1IntegerRecoveryAcquisition.run a (Placements n F r a arity owner).length u children).result=
      SemiprimeD1RecoveryResidue.reduce p ((reference axes n F r a arity owner A B e he).eval 0) := by
  rw [SemiprimeD1IntegerRecoveryAcquisition.run_result]
  apply SemiprimeD1IntegerRecoveryResidue.original_run_modulo a _ u p hu huM
    (reference axes n F r a arity owner A B e he)
    (reference_degree axes n F r a arity owner A B e he) children
    (reference_zero_integral axes n F r a arity owner A B e he)
  intro t ht j hj
  have htN : t<SemiprimeD1WireKernelOriginal.size a :=
    Finset.mem_range.mp (Finset.mem_filter.mp ht).1
  rw [SemiprimeD1IntegerRecovery.decodedPackets_coefficient]
  have h := child_error axes n F r a _ arity owner ⟨t,htN⟩ A B e he j
    ((children t)[j]?.getD []) (hchild ⟨t,htN⟩ ht j hj)
  simpa only [SemiprimeD1IntegerRecovery.decode_eq] using h

end
end RiemannGaussian.SemiprimeD1CurrentTableRecoveryLicence
