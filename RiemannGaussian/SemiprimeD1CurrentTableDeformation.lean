/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetLiteralLift
import RiemannGaussian.SemiprimeD1IntegralDeformation

/-! # Eager CURRENT integer-table deformation over every old nilpotent coordinate
Literal coefficient words, rather than creator recipes or coefficient answers,
are lifted to one integral old-jet ring. Mapping that ring to rational and modular
old-jet rings gives the precise commuting square at each new call precision.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1CurrentTableDeformation
open scoped BigOperators
open Polynomial SemiprimeD1JetAlgebra SemiprimeD1JetScalarMap SemiprimeD1JetBoxIndex
  SemiprimeD1JetLiteralLift SemiprimeD1DyadicInteger SemiprimeD1IntegralDeformation
  SemiprimeD1OriginalDeformation
noncomputable section

/-- Scalar constants commute with the ACTUAL old-jet quotient coefficient map. -/
theorem constants_square {R S : Type*} [CommRing R] [CommRing S]
    (axes : List ℕ) (f : R →+* S) :
    (scalarMap (dims axes) f).comp (constants (dims axes))=
      (constants (dims axes)).comp f := by
  ext r
  exact scalarMap_constants (dims axes) f r

/-- Actual original local replay wires with coefficients in the entire old integral jet ring. -/
def oldWire (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (i j : Fin (Placements n F r a arity owner).length) : Polynomial (Integral axes) :=
  (localWire n F r a arity owner t i j).map (constants (dims axes))

/-- Actual current table bytes acquire the source deformation; no old tensor is recomputed. -/
def currentPolynomial (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→List (List Bool)) :
    Polynomial (Integral axes) :=
  SemiprimeD1Deformation.polynomial _ (fun x => literal axes (A x)) (fun x => literal axes (B x))
    (oldWire axes n F r a arity owner t)

/-- Actual local old-jet wires include to the original replay wires at the local affine node. -/
theorem oldWire_inclusion (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (i j : Fin (Placements n F r a arity owner).length) :
    (oldWire axes n F r a arity owner t i j).map (scalarMap (dims axes) integers.subtype)=
      (wire (constants (dims axes)) n F r a arity owner i j).comp
        ((SemiprimeD1WireKernelPaper.affine a t.val).map (constants (dims axes))) := by
  rw [oldWire,Polynomial.map_map,constants_square,← Polynomial.map_map,localWire_inclusion,
    Polynomial.map_comp]
  congr 1
  unfold wire
  split_ifs <;> simp only [Polynomial.map_id,Polynomial.map_zero]

/-- The literal rational CURRENT-table witness is the locally shifted original deformation. -/
theorem current_inclusion (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→List (List Bool)) :
    (currentPolynomial axes n F r a arity owner t A B).map (scalarMap (dims axes) integers.subtype)=
      (SemiprimeD1Deformation.polynomial _ (fun x => rational axes (A x)) (fun x => rational axes (B x))
        (wire (constants (dims axes)) n F r a arity owner)).comp
          ((SemiprimeD1WireKernelPaper.affine a t.val).map (constants (dims axes))) := by
  rw [currentPolynomial,polynomial_map,polynomial_comp]
  congr 1
  funext i j
  exact oldWire_inclusion axes n F r a arity owner t i j

/-- EVERY old coordinate of EVERY retained local coefficient is integral,
from the actual CURRENT literal word-table witness rather than an integrality oracle. -/
theorem current_coefficient_integral (axes : List ℕ) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→List (List Bool))
    (j : ℕ) (e : Fin axes.length→₀ℕ) (he : InBox (dims axes) e) :
    SemiprimeD1DyadicBounds.AtLeast 0 (coefficient (dims axes) e he
      (((SemiprimeD1Deformation.polynomial _ (fun x => rational axes (A x)) (fun x => rational axes (B x))
        (wire (constants (dims axes)) n F r a arity owner)).comp
          ((SemiprimeD1WireKernelPaper.affine a t.val).map (constants (dims axes)))).coeff j)) := by
  rw [← current_inclusion,Polynomial.coeff_map,coefficient_scalarMap]
  exact (coefficient (dims axes) e he
    ((currentPolynomial axes n F r a arity owner t A B).coeff j)).property

/-- Any target old-jet algebra sees the actual modular acquired entry on each local wire. -/
theorem oldWire_evaluate {S : Type*} [CommRing S] (axes : List ℕ) (p : ℕ)
    (f : Algebra (dims axes) (ZMod (2^p)) →+* S) (z : S)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (i j : Fin (Placements n F r a arity owner).length) :
    ((oldWire axes n F r a arity owner t i j).map (scalarMap (dims axes) (reduction p))).eval₂ f z=
      if packet n F r a arity owner i=packet n F r a arity owner j then
        SemiprimeD1UniversalModeData.entryValue p (f.comp (constants (dims axes))) z
          (SemiprimeD1WireKernelOriginal.acquireOriginal a t
            (slot n F r a arity owner i) (slot n F r a arity owner j))
      else 0 := by
  rw [oldWire,Polynomial.map_map,constants_square,← Polynomial.map_map,Polynomial.eval₂_map]
  exact localWire_evaluate p (f.comp (constants (dims axes))) z n F r a arity owner t i j

/-- The WHOLE modular contraction uses the actual CURRENT word tables and original
acquired modular entries, including ALL old axes at the new call precision. -/
theorem current_modular_contraction {S : Type*} [CommRing S] (axes : List ℕ) (p : ℕ)
    (f : Algebra (dims axes) (ZMod (2^p)) →+* S) (z : S)
    (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→List (List Bool)) :
    ((currentPolynomial axes n F r a arity owner t A B).map
      (scalarMap (dims axes) (reduction p))).eval₂ f z=
      ∑bits : Fin (Placements n F r a arity owner).length→Bool,
        f (SemiprimeD1JetInterpretation.interpret ⟨axes,p⟩ (B bits))*
          SemiprimeStreamingTensor.evaluate _ (fun x => f (SemiprimeD1JetInterpretation.interpret ⟨axes,p⟩ (A x)))
            (fun i => ∑j,
              (if packet n F r a arity owner i=packet n F r a arity owner j then
                SemiprimeD1UniversalModeData.entryValue p (f.comp (constants (dims axes))) z
                  (SemiprimeD1WireKernelOriginal.acquireOriginal a t
                    (slot n F r a arity owner i) (slot n F r a arity owner j))
               else 0)*SemiprimeStreamingTensor.bit (bits j)) := by
  rw [currentPolynomial,polynomial_map,polynomial_evaluate]
  simp only [literal_reduce]
  apply Finset.sum_congr rfl
  intro bits _
  congr 1
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  rw [oldWire_evaluate]

end
end RiemannGaussian.SemiprimeD1CurrentTableDeformation
