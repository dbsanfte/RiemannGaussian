/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1IntegralLocalKernel
import RiemannGaussian.SemiprimeD1OriginalDeformation

/-! # Actual replay-wire deformation over the integral rational subring
The local witness uses actual packet/slot bytes and actual normalized kernels.
Creator coefficients belong to the integral source ring; finite old nilpotent
coordinates may subsequently be handled coefficientwise. No execution clock is
asserted by these polynomial specification identities.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1IntegralDeformation
open scoped BigOperators
open Polynomial SemiprimeD1DyadicInteger SemiprimeD1IntegralLocalKernel
open SemiprimeD1OriginalDeformation

/-- Deformation commutes with a coefficient ring homomorphism, without domain assumptions. -/
theorem polynomial_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ℕ) (A B : (Fin M→Bool)→R) (wire : Fin M→Fin M→Polynomial R) :
    (SemiprimeD1Deformation.polynomial M A B wire).map f=
      SemiprimeD1Deformation.polynomial M (fun x => f (A x)) (fun x => f (B x))
        (fun i j => (wire i j).map f) := by
  classical
  change (Polynomial.mapRingHom f) _=_
  rw [SemiprimeD1Deformation.polynomial,map_sum]
  apply Finset.sum_congr rfl
  intro bits _
  rw [map_mul]
  have he := SemiprimeCounterNative.evaluate_map (Polynomial.mapRingHom f) M
    (fun rows => C (A rows)) (SemiprimeD1Deformation.rowForm M wire bits)
  simp only [Polynomial.coe_mapRingHom,Polynomial.map_C] at he ⊢
  rw [he]
  congr 1
  congr 1
  funext row
  simp only [SemiprimeD1Deformation.rowForm,Polynomial.map_sum,Polynomial.map_mul,
    Polynomial.map_C]
  congr 1
  funext column
  cases bits column <;> simp [SemiprimeStreamingTensor.bit]

/-- Deformation commutes with the ACTUAL scalar affine substitution. -/
theorem polynomial_comp {R : Type*} [CommRing R] (M : ℕ)
    (A B : (Fin M→Bool)→R) (wire : Fin M→Fin M→Polynomial R) (g : Polynomial R) :
    (SemiprimeD1Deformation.polynomial M A B wire).comp g=
      SemiprimeD1Deformation.polynomial M A B (fun i j => (wire i j).comp g) := by
  classical
  rw [SemiprimeD1Deformation.polynomial,Polynomial.sum_comp]
  apply Finset.sum_congr rfl
  intro bits _
  rw [Polynomial.mul_comp,Polynomial.C_comp]
  have he := SemiprimeCounterNative.evaluate_map (Polynomial.compRingHom g) M
    (fun rows => C (A rows)) (SemiprimeD1Deformation.rowForm M wire bits)
  simp only [Polynomial.coe_compRingHom,Polynomial.C_comp] at he
  rw [he]
  congr 1
  congr 1
  funext row
  simp only [SemiprimeD1Deformation.rowForm,Polynomial.sum_comp,Polynomial.mul_comp,
    Polynomial.C_comp]

/-- Evaluation commutes with the entire tensor deformation in any commutative algebra. -/
theorem polynomial_evaluate {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (z : S) (M : ℕ) (A B : (Fin M→Bool)→R)
    (wire : Fin M→Fin M→Polynomial R) :
    (SemiprimeD1Deformation.polynomial M A B wire).eval₂ f z=
      ∑bits : Fin M→Bool,f (B bits)*SemiprimeStreamingTensor.evaluate M (fun x => f (A x))
        (fun i => ∑j,(wire i j).eval₂ f z*SemiprimeStreamingTensor.bit (bits j)) := by
  classical
  change (Polynomial.eval₂RingHom f z) _=_
  rw [SemiprimeD1Deformation.polynomial,map_sum]
  apply Finset.sum_congr rfl
  intro bits _
  rw [map_mul]
  have he := SemiprimeCounterNative.evaluate_map (Polynomial.eval₂RingHom f z) M
    (fun rows => C (A rows)) (SemiprimeD1Deformation.rowForm M wire bits)
  simp only [Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C] at he ⊢
  rw [he]
  congr 1
  congr 1
  funext row
  simp only [SemiprimeD1Deformation.rowForm,Polynomial.eval₂_finsetSum,Polynomial.eval₂_mul,
    Polynomial.eval₂_C]
  apply Finset.sum_congr rfl
  intro column _
  cases bits column <;> simp [SemiprimeStreamingTensor.bit]

/-- Original local wires, constructed from actual packet equality and actual slot bytes. -/
noncomputable def localWire (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (i j : Fin (Placements n F r a arity owner).length) : Polynomial integers :=
  if packet n F r a arity owner i=packet n F r a arity owner j then
    originalPolynomial a t (slot n F r a arity owner i) (slot n F r a arity owner j)
  else 0

/-- The literal local wire includes to the original actual replay wire at t+alphaZ. -/
theorem localWire_inclusion (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (i j : Fin (Placements n F r a arity owner).length) :
    (localWire n F r a arity owner t i j).map integers.subtype=
      (wire (RingHom.id ℚ) n F r a arity owner i j).comp (SemiprimeD1WireKernelPaper.affine a t.val) := by
  unfold localWire wire
  split_ifs
  · simpa only [Polynomial.map_id] using original_inclusion a t
      (slot n F r a arity owner i) (slot n F r a arity owner j)
  · simp

/-- The actual original acquired modular entry is exactly each reduced local replay wire. -/
theorem localWire_evaluate {S : Type*} [CommRing S] (p : ℕ)
    (f : ZMod (2^p) →+* S) (z : S) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (i j : Fin (Placements n F r a arity owner).length) :
    ((localWire n F r a arity owner t i j).map (reduction p)).eval₂ f z=
      if packet n F r a arity owner i=packet n F r a arity owner j then
        SemiprimeD1UniversalModeData.entryValue p f z
          (SemiprimeD1WireKernelOriginal.acquireOriginal a t
            (slot n F r a arity owner i) (slot n F r a arity owner j))
      else 0 := by
  unfold localWire
  split_ifs
  · exact original_evaluate p a f z t _ _
  · simp

/-- Actual integral local deformation from the actual replay wires and creator values. -/
noncomputable def localPolynomial (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→integers) : Polynomial integers :=
  SemiprimeD1Deformation.polynomial _ A B (localWire n F r a arity owner t)

/-- All local rational coefficients have the explicit integral deformation witness. -/
theorem localPolynomial_inclusion (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→integers) :
    (localPolynomial n F r a arity owner t A B).map integers.subtype=
      (SemiprimeD1Deformation.polynomial _ (fun x => (A x).val) (fun x => (B x).val)
        (wire (RingHom.id ℚ) n F r a arity owner)).comp (SemiprimeD1WireKernelPaper.affine a t.val) := by
  rw [localPolynomial,polynomial_map,polynomial_comp]
  congr 1
  funext i j
  exact localWire_inclusion n F r a arity owner t i j

/-- Actual locally shifted deformation coefficients are integral by the retained witness,
not by a supplied coefficientwise integrality certificate. -/
theorem original_local_coefficient_integral (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→integers) (j : ℕ) :
    SemiprimeD1DyadicBounds.AtLeast 0
      (((SemiprimeD1Deformation.polynomial _ (fun x => (A x).val) (fun x => (B x).val)
        (wire (RingHom.id ℚ) n F r a arity owner)).comp
          (SemiprimeD1WireKernelPaper.affine a t.val)).coeff j) := by
  rw [← localPolynomial_inclusion,Polynomial.coeff_map]
  exact ((localPolynomial n F r a arity owner t A B).coeff j).property

/-- The actual modular contraction of locally reduced replay wires is the mapped
integral deformation, in any target algebra (including formal nilpotent jets). -/
theorem original_modular_contraction {S : Type*} [CommRing S] (p : ℕ)
    (f : ZMod (2^p) →+* S) (z : S) (n F r a : ℕ) [NeZero r] (arity : Fin F→ℕ)
    (owner : ((e : Fin F)×Fin (arity e))→Fin n)
    (t : Fin (SemiprimeD1WireKernelOriginal.size a))
    (A B : (Fin (Placements n F r a arity owner).length→Bool)→integers) :
    ((localPolynomial n F r a arity owner t A B).map (reduction p)).eval₂ f z=
      ∑bits : Fin (Placements n F r a arity owner).length→Bool,
        f (reduction p (B bits))*SemiprimeStreamingTensor.evaluate _ (fun x => f (reduction p (A x)))
          (fun i => ∑j,
            (if packet n F r a arity owner i=packet n F r a arity owner j then
              SemiprimeD1UniversalModeData.entryValue p f z
                (SemiprimeD1WireKernelOriginal.acquireOriginal a t
                  (slot n F r a arity owner i) (slot n F r a arity owner j))
             else 0)*SemiprimeStreamingTensor.bit (bits j)) := by
  rw [localPolynomial,polynomial_map,polynomial_evaluate]
  apply Finset.sum_congr rfl
  intro bits _
  congr 1
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  rw [localWire_evaluate]

end RiemannGaussian.SemiprimeD1IntegralDeformation
