/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeRowDerivative
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Reciprocal row correlations retain a different factor channel

Reversing the coefficients of the original monic row polynomial computes
the complete product of 1-X*G_j. Unit phases connect this observable and
its derivative to the existing deflated inverse-root batch. Hence global
inverse matches and saturated products are recoverable without enumerating
the pair matrix. Original powers and their source packets remain upstream.

The literal new channel recovers on a complete ordinary-derivative failure.
Universal coverage and the full every-run one-sixth bit budget remain open.
-/

namespace RiemannGaussian.SemiprimeReciprocalRows

open scoped BigOperators
open Polynomial SemiprimeCartesianCompletion SemiprimeEuclidRowFamily SemiprimeRowDerivative

/-- A cross inverse pair keeps the product correlation, up to a unit. -/
theorem inverse_residual_eq {R : Type*} [CommRing R] (x y : Rˣ) :
    (x : R)-((y⁻¹ : Rˣ) : R)=
      ((y⁻¹ : Rˣ) : R)*((x : R)*(y : R)-1) := by
  have h : ((y⁻¹ : Rˣ) : R)*(y : R)=1 := by simp
  linear_combination -(x : R)*h

/-- Cross-products and inverse differences have exactly the same GCD,
including all prime powers and full-modulus saturation. -/
theorem inverse_residual_gcd {n : ℕ} (x y : (ZMod n)ˣ) :
    n.gcd ((x : ZMod n)-((y⁻¹ : (ZMod n)ˣ) : ZMod n)).val=
      n.gcd ((x : ZMod n)*(y : ZMod n)-1).val := by
  rw [inverse_residual_eq]
  exact SemiprimeRHCancellation.unit_mul_gcd_eq (y⁻¹) _

/-- The reciprocal polynomial retains the whole product channel. -/
noncomputable def reciprocalPolynomial {R ι : Type*} [CommRing R]
    (S : Finset ι) (r : ι → R) : R[X] := ∏ j ∈ S, (1-C (r j)*X)

/-- The reciprocal observable is coefficient reversal of the original
monic polynomial, over composite rings as well as fields. -/
theorem reciprocalPolynomial_eq_reverse {R ι : Type*} [CommRing R] [Nontrivial R]
    (S : Finset ι) (r : ι → R) :
    reciprocalPolynomial S r=(rootPolynomial S r).reverse := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [reciprocalPolynomial,rootPolynomial,Polynomial.reverse,reflect_one]
  | @insert a S ha ih =>
    have hm : (rootPolynomial S r).Monic := monic_prod_X_sub_C r S
    have he : rootPolynomial (insert a S) r=(X-C (r a))*rootPolynomial S r := by
      simp [rootPolynomial,ha]
    have hf : (X-C (r a) : R[X]).reverse=1-C (r a)*X := by
      rw [Polynomial.reverse,natDegree_X_sub_C,reflect_sub,reflect_one_X,reflect_C]
      simp
    rw [reciprocalPolynomial,Finset.prod_insert ha,he,
      reverse_mul (by simp [hm.leadingCoeff]),hf,←ih]
    rfl

/-- This public unit is the only normalization between the reversed
polynomial and the monic inverse-root polynomial. -/
def reciprocalPhase {R ι : Type*} [CommRing R] (S : Finset ι) (r : ι → Rˣ) : Rˣ :=
  ∏ j ∈ S, -r j

/-- Retain the exact phase rather than only a norm of the polynomial. -/
theorem reciprocalPolynomial_eq_unit_phase {R ι : Type*} [CommRing R]
    (S : Finset ι) (r : ι → Rˣ) :
    reciprocalPolynomial S (fun j => (r j : R))=
      C ((reciprocalPhase S r : Rˣ) : R)*
        rootPolynomial S (fun j => (((r j)⁻¹ : Rˣ) : R)) := by
  have h (j : ι) : (1-C (r j : R)*X : R[X])=
      C (-(r j : R))*(X-C (((r j)⁻¹ : Rˣ) : R)) := by
    have he : (r j : R)*(((r j)⁻¹ : Rˣ) : R)=1 := by simp
    calc
      _ = -C (r j : R)*X+C ((r j : R)*(((r j)⁻¹ : Rˣ) : R)) := by
        rw [he,C_1]; ring
      _ = _ := by rw [map_mul,map_neg]; ring
  simp_rw [reciprocalPolynomial,h]
  rw [Finset.prod_mul_distrib]
  simp [reciprocalPhase,rootPolynomial]

/-- Value GCDs of the reversed polynomial are exact inverse-root GCDs. -/
theorem reciprocalPolynomial_eval_gcd {n : ℕ} {ι : Type*}
    (S : Finset ι) (r : ι → (ZMod n)ˣ) (t : ZMod n) :
    n.gcd ((reciprocalPolynomial S (fun j => (r j : ZMod n))).eval t).val=
      n.gcd ((rootPolynomial S (fun j => (((r j)⁻¹ : (ZMod n)ˣ) : ZMod n))).eval t).val := by
  rw [reciprocalPolynomial_eq_unit_phase,eval_mul,eval_C]
  exact SemiprimeRHCancellation.unit_mul_gcd_eq (reciprocalPhase S r) _

/-- At a global inverse match the derivative keeps the same exact unit
phase, so deflation does not discard a proper cross-pair hit. -/
theorem reciprocalPolynomial_derivative_gcd {n : ℕ} {ι : Type*}
    (S : Finset ι) (r : ι → (ZMod n)ˣ) (t : ZMod n) :
    n.gcd ((reciprocalPolynomial S (fun j => (r j : ZMod n))).derivative.eval t).val=
      n.gcd ((rootPolynomial S (fun j => (((r j)⁻¹ : (ZMod n)ˣ) : ZMod n))).derivative.eval t).val := by
  rw [reciprocalPolynomial_eq_unit_phase,derivative_C_mul,eval_mul,eval_C]
  exact SemiprimeRHCancellation.unit_mul_gcd_eq (reciprocalPhase S r) _

/-- In a hidden field this channel records products equal to one,
retaining a correlation absent from ordinary pair differences. -/
theorem reciprocalPolynomial_map_zero_iff {R F ι : Type*} [CommRing R]
    [CommRing F] [IsDomain F] (φ : R →+* F) (S : Finset ι) (r : ι → R) (t : R) :
    φ ((reciprocalPolynomial S r).eval t)=0 ↔ ∃ j ∈ S, φ (r j)*φ t=1 := by
  simp only [reciprocalPolynomial,eval_prod,eval_sub,eval_one,eval_mul,eval_C,eval_X,
    map_prod,map_sub,map_one,map_mul,Finset.prod_eq_zero_iff,sub_eq_zero]
  constructor
  · rintro ⟨j,hj,he⟩; exact ⟨j,hj,he.symm⟩
  · rintro ⟨j,hj,he⟩; exact ⟨j,hj,he.symm⟩

/-- The exact inverse-root detector, with globally distinct original
targets. Its polynomial is available by proved coefficient reversal. -/
noncomputable def recoverReciprocalRows {N : ℕ} (m : ℕ) (g : (ZMod N)ˣ) : Option ℕ :=
  recoverResidueBatch (publicRoots m (g⁻¹)) (publicRoots m g).toList

theorem recoverReciprocalRows_sound {N m d : ℕ} {g : (ZMod N)ˣ}
    (hd : recoverReciprocalRows m g=some d) : SemiprimeGroupSelection.ProperDivisor N d :=
  recoverResidueBatch_sound hd

/-- Every proper original product-pair hit is recovered, even when
other whole-modulus inverse matches require deflation. -/
theorem reciprocalRows_succeeds_of_product_pair {N m : ℕ} [NeZero N]
    (g : (ZMod N)ˣ) {e f : ℤ} (he : e ∈ publicExponents N m) (hf : f ∈ publicExponents N m)
    (hp : SemiprimeGroupSelection.ProperDivisor N
      (N.gcd (((g^e : (ZMod N)ˣ) : ZMod N)*((g^f : (ZMod N)ˣ) : ZMod N)-1).val)) :
    ∃ d, recoverReciprocalRows m g=some d := by
  have hx := List.mem_toFinset.mpr (publicRowValues_mem_of_exponent (g⁻¹) hf)
  have ht := Finset.mem_toList.mpr (List.mem_toFinset.mpr (publicRowValues_mem_of_exponent g he))
  apply recoverResidueBatch_succeeds_of_proper_pair hx ht
  simpa only [inv_zpow,inverse_residual_gcd] using hp

/-- The two scalar input axes and recovery GCD count remain bounded by
twice the original packet count. Polynomial and bit costs are separate. -/
theorem reciprocalRows_gcd_bound {N m : ℕ} (g : (ZMod N)ˣ) :
    recoveryGcdCount N (fun i => residueLeaves (publicRoots m (g⁻¹)) (i : ZMod N))
      (evaluatedColumns (publicRoots m (g⁻¹)) (publicRoots m g).toList) ≤
        2*(publicPackets N m).length := by
  have h := recoverResidueBatch_gcd_bound (publicRoots m (g⁻¹)) (publicRoots m g).toList
  simp only [Finset.length_toList] at h
  exact h.trans (by simpa [two_mul] using Nat.add_le_add (publicRoots_card_le g) (publicRoots_card_le (g⁻¹)))

/-- Literal N-only base for the original-row failure stress input. -/
def controlBase : (ZMod 2518766418595894637609)ˣ :=
  ZMod.unitOfCoprime 2 (by norm_num : Nat.Coprime 2 2518766418595894637609)

set_option maxRecDepth 32768 in
/-- Two public packets in the complete actual family retain the useful
cross-product correlation. The pair is an audit witness, not source advice. -/
theorem control_exponents :
    (3596798445668641429783915 : ℤ) ∈ publicExponents 2518766418595894637609 3691 ∧
    (3037632300775047433790237 : ℤ) ∈ publicExponents 2518766418595894637609 3691 := by
  constructor
  · apply publicExponent_mem_of_residue (j:=768) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel
  · apply publicExponent_mem_of_residue (j:=2283) (by norm_num) (by norm_num [Nat.Coprime])
    decide +kernel

/-- Actual modular powers of the retained public exponents. -/
theorem control_values :
    ((controlBase^(3596798445668641429783915 : ℤ) : (ZMod 2518766418595894637609)ˣ) :
      ZMod 2518766418595894637609)=459898352550707889411 ∧
    ((controlBase^(3037632300775047433790237 : ℤ) : (ZMod 2518766418595894637609)ˣ) :
      ZMod 2518766418595894637609)=588586918346787592002 := by
  norm_num only [controlBase,zpow_ofNat,Units.val_pow_eq_pow_val,ZMod.coe_unitOfCoprime]
  constructor <;> reduce_mod_char

/-- Their product separates an actual proper factor of the input. -/
theorem control_product_pair :
    SemiprimeGroupSelection.ProperDivisor 2518766418595894637609
      ((2518766418595894637609 : ℕ).gcd
        ((459898352550707889411*588586918346787592002-1 : ZMod 2518766418595894637609)).val) := by
  norm_num [SemiprimeGroupSelection.ProperDivisor,ZMod.val_ofNat]

/-- The full public reciprocal-root detector recovers on the original
positive-row derivative stress failure. Neither factor nor witness pair
is an input. This remains one control, not universal sixth-root coverage. -/
theorem control_reciprocal_recovers :
    ∃ d, recoverReciprocalRows 3691 controlBase=some d ∧
      SemiprimeGroupSelection.ProperDivisor 2518766418595894637609 d := by
  have hg : SemiprimeGroupSelection.ProperDivisor 2518766418595894637609
      ((2518766418595894637609 : ℕ).gcd
        (((controlBase^(3596798445668641429783915 : ℤ) : (ZMod 2518766418595894637609)ˣ) :
            ZMod 2518766418595894637609)*
          ((controlBase^(3037632300775047433790237 : ℤ) : (ZMod 2518766418595894637609)ˣ) :
            ZMod 2518766418595894637609)-1).val) := by
    rw [control_values.1,control_values.2]
    exact control_product_pair
  obtain ⟨d,hd⟩ := reciprocalRows_succeeds_of_product_pair controlBase
    control_exponents.1 control_exponents.2 hg
  exact ⟨d,hd,recoverReciprocalRows_sound hd⟩

end RiemannGaussian.SemiprimeReciprocalRows
