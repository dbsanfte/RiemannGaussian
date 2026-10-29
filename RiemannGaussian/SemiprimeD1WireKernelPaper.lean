/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WireKernelOriginal

/-! # Identification with the ORIGINAL D.7 Cauchy wire polynomial
These polynomials are specifications, never input tables. The actual entry
constructor remains acquireOriginal on a,t,x,y and integer factor data only.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1WireKernelPaper
open scoped BigOperators
open Polynomial SemiprimeD1WireKernel SemiprimeD1WireKernelFactors
open SemiprimeD1WireKernelEntry SemiprimeD1WireKernelOriginal

/-- The actual original full grid polynomial C(T). -/
noncomputable def grid (a : ℕ) : ℚ[X] :=
  ∏ q∈Finset.range (size a), (X-C (point a q:ℚ))

/-- The original D.7 factor cancellation, rather than a rational-function oracle. -/
noncomputable def omitted (a d : ℕ) : ℚ[X] :=
  ∏ q∈(Finset.range (size a)).erase d, (X-C (point a q:ℚ))

/-- Cancelling the displacement factor really reconstructs the ORIGINAL grid C. -/
theorem cancelled_grid (a d : ℕ) (hd : d<size a) :
    omitted a d*(X-C (point a d:ℚ))=grid a :=
  Finset.prod_erase_mul (Finset.range (size a)) _ (Finset.mem_range.mpr hd)

/-- Actual derivative product at original zero equals the acquired integer denominator. -/
theorem omitted_center_zero (a : ℕ) :
    (omitted a (center a)).eval 0=(derivativeProduct (size a) (center a):ℚ) := by
  rw [omitted,Polynomial.eval_prod]
  simp only [eval_sub,eval_X,eval_C,zero_sub]
  have hp := Finset.prod_erase_mul (Finset.range (size a))
    (fun q => if q=center a then (1:ℤ) else difference (center a) q)
    (Finset.mem_range.mpr (center_lt a))
  simp only [ite_true,mul_one] at hp
  have hp' : (∏ q∈(Finset.range (size a)).erase (center a),
      if q=center a then (1:ℤ) else difference (center a) q)=
      derivativeProduct (size a) (center a) := by
    simpa only [derivativeProduct,difference] using hp
  rw [← hp']
  push_cast
  apply Finset.prod_congr rfl
  intro q hq
  have hn := (Finset.mem_erase.mp hq).1
  simp only [hn,ite_false,point,difference]
  push_cast
  ring

/-- C'(0) is proved equal to the actually acquired original integer product. -/
theorem derivative_zero (a : ℕ) : (grid a).derivative.eval 0=
    (derivativeProduct (size a) (center a):ℚ) := by
  have h := cancelled_grid a (center a) (center_lt a)
  have hz : point a (center a)=0 := by simp [point]
  rw [hz,Int.cast_zero,C_0,sub_zero] at h
  rw [← h,derivative_mul]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,derivative_X,eval_X,
    mul_zero,zero_add,mul_one]
  exact omitted_center_zero a

/-- The D.7 polynomial with its ORIGINAL derivative normalizer. -/
noncomputable def kernel (a d : ℕ) : ℚ[X] :=
  C (((grid a).derivative.eval 0)⁻¹)*omitted a d

/-- Actual original t+alpha*z local coordinate, alpha=2^(a+1). -/
noncomputable def affine (a j : ℕ) : ℚ[X] :=
  C (point a j:ℚ)+C (((2:ℤ)^(a+1)):ℚ)*X

/-- Every raw local numerator factor is the original shifted D.7 factor. -/
theorem omitted_local (a j d : ℕ) :
    (omitted a d).comp (affine a j)=
      (rawPolynomial (a+1) j d).map (Int.castRingHom ℚ) := by
  unfold omitted rawPolynomial
  rw [Polynomial.prod_comp,Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro q _
  simp only [Polynomial.sub_comp,Polynomial.X_comp,Polynomial.C_comp,
    Polynomial.map_add,Polynomial.map_C,Polynomial.map_mul,Polynomial.map_X,Int.coe_castRingHom]
  have he : (point a j:ℚ)-(point a q:ℚ)=(difference j q:ℚ) := by
    unfold point difference
    push_cast
    ring
  change affine a j-C (point a q:ℚ)=_
  rw [affine]
  have hp : C (point a j:ℚ)+C (((2:ℤ)^(a+1)):ℚ)*X-C (point a q:ℚ)=
      C ((point a j:ℚ)-(point a q:ℚ))+C (((2:ℤ)^(a+1)):ℚ)*X := by
    rw [C_sub]
    ring
  rw [hp,he]
  push_cast
  rfl

/-- The original normalized finite factor constructor is EXACTLY D.7 locally. -/
theorem kernel_local (a j d : ℕ) : (kernel a d).comp (affine a j)=
    rationalKernel (a+1) (center a) j d := by
  rw [kernel,Polynomial.mul_comp,Polynomial.C_comp,derivative_zero,omitted_local]
  rfl

/-- Lemma D.4 integrality for ORIGINAL a,t,x,y, with an acquired odd denominator
and acquired integer polynomial witness, never an integrality premise. -/
theorem original_kernel_integral (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    Odd (acquireOriginal a t x y).denominator ∧
    C ((acquireOriginal a t x y).denominator:ℚ)*
        (kernel a (displacement a x y).val).comp (affine a t.val)=
      (numerator (acquireOriginal a t x y)).map (Int.castRingHom ℚ) := by
  rw [kernel_local]
  exact original_integrality a t x y

/-- The original ordered factor list has exactly 2L−1 entries. -/
theorem original_factor_count (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    (acquireOriginal a t x y).factors.length=size a-1 := by
  have h := List.toFinset_card_of_nodup (indices_nodup (a+1) (displacement a x y).val)
  have hd : (displacement a x y).val<2^(a+1) := (displacement a x y).isLt
  rw [indices_toFinset,Finset.card_erase_of_mem
    (Finset.mem_range.mpr hd),Finset.card_range] at h
  change ((indices (a+1) (displacement a x y).val).map (normalizedFactor (a+1) t.val)).length=_
  rw [List.length_map]
  exact h.symm

/-- Exact remaining power, including zero at the cancelled local factor. -/
theorem excess_add_order (k j d : ℕ) (hj : j<2^k) (hd : d<2^k) :
    excess k j d+factorOrder k j d=k := by
  have hs := Finset.sum_erase_add (Finset.range (2^k)) (factorOrder k j) (Finset.mem_range.mpr hd)
  rw [total_factor_content k j hj] at hs
  have he := omitted_content_ge k j d hj hd
  unfold excess
  omega

/-- Acquired original remaining two-exponent is at most a+1, not grid-size growth. -/
theorem original_power_bound (a : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) :
    (acquireOriginal a t x y).power ≤ a+1 := by
  have h := excess_add_order (a+1) t.val (displacement a x y).val t.isLt (displacement a x y).isLt
  change excess (a+1) t.val (displacement a x y).val ≤ a+1
  omega

/-- The unexpanded acquired integer factor data evaluates as its actual polynomial. -/
theorem numerator_mod_eval (P : ℕ) (entry : Entry) (z : ZMod (2^P)) :
    Polynomial.eval₂ (Int.castRingHom (ZMod (2^P))) z (numerator entry)=
      (2:ZMod (2^P))^entry.power*
        (entry.factors.map (fun f => (f.constant:ZMod (2^P))+(f.slope:ZMod (2^P))*z)).prod := by
  simp only [numerator,eval₂_mul,eval₂_C,eval₂_list_prod,List.map_map,Function.comp_def,
    linearPolynomial,eval₂_add,eval₂_X,Int.coe_castRingHom,Int.cast_pow,Int.cast_ofNat]

/-- The actual original modular evaluator is the unique odd-denominator residue
of the acquired integer polynomial, not a cast from the whole rational field. -/
theorem original_modular_spec (a P : ℕ) (t : Fin (size a)) (x y : Fin (2^a)) (z : ZMod (2^P)) :
    ((acquireOriginal a t x y).denominator:ZMod (2^P))*
        evaluate P (acquireOriginal a t x y) z=
      Polynomial.eval₂ (Int.castRingHom (ZMod (2^P))) z (numerator (acquireOriginal a t x y)) := by
  rw [numerator_mod_eval,evaluate]
  calc
    _=(((acquireOriginal a t x y).denominator:ZMod (2^P))*
        ((acquireOriginal a t x y).denominator:ZMod (2^P))⁻¹)*
        (2:ZMod (2^P))^(acquireOriginal a t x y).power*
        ((acquireOriginal a t x y).factors.map
          (fun f => (f.constant:ZMod (2^P))+(f.slope:ZMod (2^P))*z)).prod := by ring
    _=_ := by rw [original_inverse_correct,one_mul]

/-- The original normalizer restores the exact delta at T=0, including all zeros. -/
theorem kernel_zero (a d : ℕ) : (kernel a d).eval 0=
    if d=center a then (1:ℚ) else 0 := by
  have hn : (derivativeProduct (size a) (center a):ℚ)≠0 := by
    exact_mod_cast derivativeProduct_ne_zero (size a) (center a) (center_lt a)
  rw [kernel,eval_mul,eval_C,derivative_zero]
  by_cases hd : d=center a
  · subst d
    rw [omitted_center_zero,inv_mul_cancel₀ hn]
    simp
  · have hc : center a∈(Finset.range (size a)).erase d :=
      Finset.mem_erase.mpr ⟨Ne.symm hd,Finset.mem_range.mpr (center_lt a)⟩
    have hz : (omitted a d).eval 0=0 := by
      rw [omitted,Polynomial.eval_prod]
      apply Finset.prod_eq_zero hc
      simp [point]
    simp only [hd,ite_false,hz,mul_zero]

/-- The omitted grid index is the zero displacement precisely on the original diagonal. -/
theorem displacement_center_iff (a : ℕ) (x y : Fin (2^a)) :
    (displacement a x y).val=center a ↔ x=y := by
  constructor
  · intro h
    have hp := displacement_point a x y
    rw [h] at hp
    simp only [point,sub_self] at hp
    apply Fin.ext
    omega
  · intro h
    subst y
    simp [displacement,center]

/-- Original packet startup is exactly W(0)=I, not a supplied endpoint matrix. -/
theorem packet_kernel_zero (a : ℕ) (x y : Fin (2^a)) :
    (kernel a (displacement a x y).val).eval 0=if x=y then (1:ℚ) else 0 := by
  simp only [kernel_zero,displacement_center_iff]

end RiemannGaussian.SemiprimeD1WireKernelPaper
