/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1CurrentTableDeformation
import RiemannGaussian.SemiprimeD1LeafCounter

/-! # Individual literal-table integer products BEFORE modular reduction
The source network value multiplies each actual entry's integer lift in the old
integral jet ring. It never lifts a mod-parent aggregate product, so carries are
retained when the same individual current entries are used at child precision.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1NetworkIntegralDeformation
open scoped BigOperators
open Polynomial SemiprimeD1JetAlgebra SemiprimeD1JetScalarMap SemiprimeD1JetBoxIndex
  SemiprimeD1JetLiteralLift SemiprimeD1DyadicInteger SemiprimeD1IntegralDeformation
  SemiprimeD1OriginalDeformation SemiprimeD1CurrentTableDeformation
  SemiprimeD1LeafCounter
noncomputable section

/-- ACTUAL individual current tensor entries are lifted BEFORE their network product. -/
def networkValue {M : ℕ} (axes : List ℕ) (vertices : List Vertex) (bits : Fin M→Bool) : Integral axes :=
  (vertices.map (fun v => literal axes
    (SemiprimeD1TensorTables.valueAt v.table (localAssignment bits v)))).prod

/-- Every individual entry reduces separately; products commute only through the
legitimate source ring map, never through a lift of an already reduced aggregate. -/
theorem networkValue_modular {M : ℕ} (axes : List ℕ) (p : ℕ) (vertices : List Vertex) (bits : Fin M→Bool) :
    scalarMap (dims axes) (reduction p) (networkValue axes vertices bits)=
      (vertices.map (fun v => SemiprimeD1JetInterpretation.interpret ⟨axes,p⟩
        (SemiprimeD1TensorTables.valueAt v.table (localAssignment bits v)))).prod := by
  simp only [networkValue,map_list_prod,List.map_map,Function.comp_def,literal_reduce]

/-- The exact rational witness is the product of individual entry lifts, with carries intact. -/
theorem networkValue_rational {M : ℕ} (axes : List ℕ) (vertices : List Vertex) (bits : Fin M→Bool) :
    scalarMap (dims axes) integers.subtype (networkValue axes vertices bits)=
      (vertices.map (fun v => rational axes
        (SemiprimeD1TensorTables.valueAt v.table (localAssignment bits v)))).prod := by
  simp only [networkValue,map_list_prod,List.map_map,Function.comp_def,rational]

/-- Actual physical multiplication at the NEW precision computes this original
individual-entry source product. No aggregate-parent-word equality is assumed. -/
theorem networkValue_executed {M : ℕ} (axes : List ℕ) (p : ℕ) (vertices : List Vertex)
    (bits : Fin M→Bool) (hpos : ∀q∈axes,0<q) :
    scalarMap (dims axes) (reduction p) (networkValue axes vertices bits)=
      SemiprimeD1JetInterpretation.interpret ⟨axes,p⟩
        (evaluateAssignment ⟨axes,p⟩ vertices (List.ofFn bits)).words := by
  rw [networkValue_modular]
  exact (evaluateAssignment_value ⟨axes,p⟩ hpos vertices bits).symm

/-- Generic internal local witness with intrinsic old-integral-jet source values. -/
def integralPolynomial (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→Integral axes) :
    Polynomial (Integral axes) :=
  SemiprimeD1Deformation.polynomial _ A B (oldWire axes n F r a arity owner t)

/-- Original local replay deformation commutes with integral-source inclusion. -/
theorem integral_inclusion (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→Integral axes) :
    (integralPolynomial axes n F r a arity owner t A B).map (scalarMap (dims axes) integers.subtype)=
      (SemiprimeD1Deformation.polynomial _
        (fun x => scalarMap (dims axes) integers.subtype (A x))
        (fun x => scalarMap (dims axes) integers.subtype (B x))
        (wire (constants (dims axes)) n F r a arity owner)).comp
          ((SemiprimeD1WireKernelPaper.affine a t.val).map (constants (dims axes))) := by
  rw [integralPolynomial,polynomial_map,polynomial_comp]
  congr 1
  funext i j
  exact oldWire_inclusion axes n F r a arity owner t i j

/-- Concrete original network local witness, with no arbitrary coefficient/value functions. -/
def networkPolynomial (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (left right : List Vertex) :
    Polynomial (Integral axes) :=
  integralPolynomial axes n F r a arity owner t (networkValue axes left) (networkValue axes right)

/-- The ACTUAL network's individual-entry product factors and acquired modular
wire entries form exactly the restricted-reduced source deformation in any algebra. -/
theorem network_modular_contraction {S : Type*} [CommRing S] (axes : List ℕ) (p : ℕ)
    (f : Algebra (dims axes) (ZMod (2^p)) →+* S) (z : S)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a)) (left right : List Vertex) :
    ((networkPolynomial axes n F r a arity owner t left right).map
      (scalarMap (dims axes) (reduction p))).eval₂ f z=
      ∑bits : Fin (Placements n F r a arity owner).length→Bool,
        f ((right.map (fun v => SemiprimeD1JetInterpretation.interpret ⟨axes,p⟩
          (SemiprimeD1TensorTables.valueAt v.table (localAssignment bits v)))).prod)*
          SemiprimeStreamingTensor.evaluate _
            (fun x => f ((left.map (fun v => SemiprimeD1JetInterpretation.interpret ⟨axes,p⟩
              (SemiprimeD1TensorTables.valueAt v.table (localAssignment x v)))).prod))
            (fun i => ∑j,
              (if packet n F r a arity owner i=packet n F r a arity owner j then
                SemiprimeD1UniversalModeData.entryValue p (f.comp (constants (dims axes))) z
                  (SemiprimeD1WireKernelOriginal.acquireOriginal a t
                    (slot n F r a arity owner i) (slot n F r a arity owner j))
               else 0)*SemiprimeStreamingTensor.bit (bits j)) := by
  rw [networkPolynomial,integralPolynomial,polynomial_map,polynomial_evaluate]
  simp only [networkValue_modular]
  apply Finset.sum_congr rfl
  intro bits _
  congr 1
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  rw [oldWire_evaluate]

end
end RiemannGaussian.SemiprimeD1NetworkIntegralDeformation
