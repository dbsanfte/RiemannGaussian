/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetCoordinateLinear
import RiemannGaussian.SemiprimeD1NetworkIntegralDeformation
import RiemannGaussian.SemiprimeD1IntegerRecoveryAcquisition

/-! # D.5 recovery for products of INDIVIDUAL current table integer lifts
The source product is formed intrinsically in the integral old-jet ring BEFORE
mapping to either rational or modular coefficients. No mod-parent aggregate word
is lifted. Concrete network wrappers below consume literal Vertex/table data.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1NetworkRecoveryLicence
open scoped BigOperators
open Polynomial SemiprimeD1JetAlgebra SemiprimeD1JetScalarMap SemiprimeD1JetBoxIndex
  SemiprimeD1JetLiteralLift SemiprimeD1DyadicInteger SemiprimeD1IntegralDeformation
  SemiprimeD1OriginalDeformation SemiprimeD1CurrentTableDeformation
  SemiprimeD1JetCoordinateLinear SemiprimeD1DyadicBounds
  SemiprimeD1NetworkIntegralDeformation SemiprimeD1LeafCounter
noncomputable section

/-- Internal scalar reference for intrinsic integral old-jet source products. -/
def reference (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→Integral axes)
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) : Polynomial ℚ :=
  polynomial (coordinate (dims axes) e he)
    (SemiprimeD1Deformation.polynomial _ (fun x => scalarMap (dims axes) integers.subtype (A x)) (fun x => scalarMap (dims axes) integers.subtype (B x))
      (wire (constants (dims axes)) n F r a arity owner))

/-- The reference has the ORIGINAL D.8 degree budget, with no degree oracle. -/
theorem reference_degree (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→Integral axes)
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) :
    (reference axes n F r a arity owner A B e he).natDegree≤
      (Placements n F r a arity owner).length*(2*(2^a)-1) :=
  (polynomial_degree _ _).trans (original_degree _ n F r a arity owner _ _)

/-- Old-coordinate linear extraction commutes with the EXACT original local substitution. -/
theorem reference_local (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→Integral axes)
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) :
    (reference axes n F r a arity owner A B e he).comp (SemiprimeD1WireKernelPaper.affine a t.val)=
      polynomial (coordinate (dims axes) e he)
        ((integralPolynomial axes n F r a arity owner t A B).map (scalarMap (dims axes) integers.subtype)) := by
  have hsub := SemiprimeD1JetCoordinateLinear.polynomial_comp (coordinate (dims axes) e he)
    (SemiprimeD1Deformation.polynomial _ (fun x => scalarMap (dims axes) integers.subtype (A x)) (fun x => scalarMap (dims axes) integers.subtype (B x))
      (wire (constants (dims axes)) n F r a arity owner)) (SemiprimeD1WireKernelPaper.affine a t.val)
  have hc : algebraMap ℚ (Algebra (dims axes) ℚ)=constants (dims axes) := Subsingleton.elim _ _
  rw [hc] at hsub
  rw [reference,← hsub,← integral_inclusion]

/-- The two original scalar affine-coordinate definitions are exactly the same polynomial. -/
theorem original_affine (a t : ℕ) : SemiprimeD1WireKernelPaper.affine a t=
    SemiprimeD1ScaledHermite.affine (SemiprimeD1HermiteOriginal.alpha a) (SemiprimeD1HermiteNodes.node a t) := by
  simp only [SemiprimeD1WireKernelPaper.affine,SemiprimeD1ScaledHermite.affine,
    SemiprimeD1HermiteOriginal.alpha,SemiprimeD1HermiteNodes.node,Int.cast_ofNat]

/-- ACTUAL child old-coordinate residue equality DERIVES the original retained D.5 error. -/
theorem child_error (axes : List ℕ) (n F r a p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→Integral axes)
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) (j : ℕ) (bs : List Bool)
    (hchild : coefficient (dims axes) e he
      (scalarMap (dims axes) (reduction p) ((integralPolynomial axes n F r a arity owner t A B).coeff j))=
        (SemiprimeBitArithmetic.bitValue bs:ZMod (2^p))) :
    AtLeast (p:ℤ) ((SemiprimeBitArithmetic.bitValue bs:ℚ)-
      (((reference axes n F r a arity owner A B e he).comp
        (SemiprimeD1ScaledHermite.affine (SemiprimeD1HermiteOriginal.alpha a)
          (SemiprimeD1HermiteNodes.node a t.val))).coeff j)) := by
  rw [← original_affine,reference_local,polynomial_coefficient,Polynomial.coeff_map]
  exact old_coordinate_word_error (dims axes) e he p
    ((integralPolynomial axes n F r a arity owner t A B).coeff j) bs hchild

/-- The reference's original value at zero is integral from the literal source contraction. -/
theorem reference_zero_integral (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→Integral axes)
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) :
    AtLeast 0 ((reference axes n F r a arity owner A B e he).eval 0) := by
  rw [reference,polynomial_eval,map_zero,original_at_zero]
  have hs : (∑bits,scalarMap (dims axes) integers.subtype (A bits)*scalarMap (dims axes) integers.subtype (B bits))=
      scalarMap (dims axes) integers.subtype (∑bits,A bits*B bits) := by
    simp only [map_sum,map_mul]
  change AtLeast 0 (coefficient (dims axes) e he _)
  rw [hs,coefficient_scalarMap]
  exact (coefficient (dims axes) e he (∑bits,A bits*B bits)).property

/-- Internal intrinsic-ring D.5 bridge. Concrete network inputs are instantiated
below by products of individually lifted actual table entries. -/
theorem integral_word_recovery (axes : List ℕ) (n F r a u p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→Integral axes)
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
          ((integralPolynomial axes n F r a arity owner t A B).coeff j))=
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

/-- Concrete scalar reference of the ACTUAL network's individual integer-entry products. -/
def networkReference (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (left right : List Vertex)
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) : Polynomial ℚ :=
  reference axes n F r a arity owner (networkValue axes left) (networkValue axes right) e he

/-- Actual individual network entry products preserve the ORIGINAL reference degree cap. -/
theorem network_reference_degree (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (left right : List Vertex)
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) :
    (networkReference axes n F r a arity owner left right e he).natDegree≤
      (Placements n F r a arity owner).length*(2*(2^a)-1) :=
  reference_degree axes n F r a arity owner _ _ e he

/-- The actual network source, including every carry, gives integral parent coordinate values. -/
theorem network_reference_zero_integral (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (left right : List Vertex)
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) :
    AtLeast 0 ((networkReference axes n F r a arity owner left right e he).eval 0) :=
  reference_zero_integral axes n F r a arity owner _ _ e he


/-- The reference's parent residue is EXACTLY the original individual-table
network contraction at parent precision, with all integer carries preserved. -/
theorem network_reference_zero_residue (axes : List ℕ) (n F r a p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (left right : List Vertex)
    (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) :
    SemiprimeD1RecoveryResidue.reduce p
      ((networkReference axes n F r a arity owner left right e he).eval 0)=
      coefficient (dims axes) e he
        (∑bits : Fin (Placements n F r a arity owner).length→Bool,
          (left.map (fun v => SemiprimeD1JetInterpretation.interpret ⟨axes,p⟩
            (SemiprimeD1TensorTables.valueAt v.table (localAssignment bits v)))).prod*
          (right.map (fun v => SemiprimeD1JetInterpretation.interpret ⟨axes,p⟩
            (SemiprimeD1TensorTables.valueAt v.table (localAssignment bits v)))).prod) := by
  let total : Integral axes := ∑bits : Fin (Placements n F r a arity owner).length→Bool,
    networkValue axes left bits*networkValue axes right bits
  have href : (networkReference axes n F r a arity owner left right e he).eval 0=
      coefficient (dims axes) e he (scalarMap (dims axes) integers.subtype total) := by
    rw [networkReference,reference,polynomial_eval,map_zero,original_at_zero]
    change coefficient (dims axes) e he
      (∑bits,scalarMap (dims axes) integers.subtype (networkValue axes left bits)*
        scalarMap (dims axes) integers.subtype (networkValue axes right bits))=_
    simp only [total,map_sum,map_mul]
  have hmod : scalarMap (dims axes) (reduction p) total=
      ∑bits : Fin (Placements n F r a arity owner).length→Bool,
        (left.map (fun v => SemiprimeD1JetInterpretation.interpret ⟨axes,p⟩
          (SemiprimeD1TensorTables.valueAt v.table (localAssignment bits v)))).prod*
        (right.map (fun v => SemiprimeD1JetInterpretation.interpret ⟨axes,p⟩
          (SemiprimeD1TensorTables.valueAt v.table (localAssignment bits v)))).prod := by
    simp only [total,map_sum,map_mul,networkValue_modular]
  rw [href,coefficient_scalarMap]
  change reduction p (coefficient (dims axes) e he total)=_
  rw [← coefficient_scalarMap (dims axes) (reduction p) total e he,hmod]

/-- ACTUAL network-data D.5 recovery, with INDIVIDUAL current entries lifted BEFORE
products. No aggregate-mod-parent table, unknown A/B value, degree, integrality,
weight, or scalar-error oracle is an input. Only child modular postconditions remain. -/
theorem network_word_recovery (axes : List ℕ) (n F r a u p : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n) (left right : List Vertex)
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
          ((networkPolynomial axes n F r a arity owner t left right).coeff j))=
        (SemiprimeBitArithmetic.bitValue ((children t.val)[j]?.getD []):ZMod
          (2^SemiprimeD1WeightPrecision.precision a (Placements n F r a arity owner).length u p t.val))) :
    SemiprimeD1IntegerRecoveryResidue.finish p
      (SemiprimeD1IntegerRecoveryAcquisition.run a (Placements n F r a arity owner).length u children).result=
      SemiprimeD1RecoveryResidue.reduce p ((networkReference axes n F r a arity owner left right e he).eval 0) :=
  integral_word_recovery axes n F r a u p arity owner _ _ e he hu huM children hchild

end
end RiemannGaussian.SemiprimeD1NetworkRecoveryLicence
