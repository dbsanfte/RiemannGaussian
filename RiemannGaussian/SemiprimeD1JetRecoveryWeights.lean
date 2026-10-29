/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetRecoveryScalarHeight
import RiemannGaussian.SemiprimeHermiteArrayHeight

/-! # Actual original-grid tapered Hermite local weights
These are scalar-rational LINEAR functionals on retained coefficient arrays.
No evaluation homomorphism at -t/alpha on a nilpotent quotient is asserted.
Full variable-multiplicity Hermite reconstruction and D.10 regrouping remain
separate obligations; the local convolution/weight identity is exact.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1JetRecoveryWeights
open scoped BigOperators
open Polynomial SemiprimeD1WireKernelOriginal SemiprimeD1TaperedLoss
  SemiprimeD1JetRecoveryGrid SemiprimeJetArray SemiprimeJetRecurrence SemiprimeHermiteArrayHeight

/-- Actual original affine slopes, repeated by ORIGINAL valuation-dependent multiplicities. -/
def slopes (a h u t : ℕ) : List ℚ :=
  (List.range (size a)).flatMap (fun q =>
    if q=center a ∨ q=t then [] else List.replicate (nodeMultiplicity a h u q)
      (((2:ℤ)^(a+1):ℚ)/((point a t:ℚ)-(point a q:ℚ))))

/-- Explicit original D.9 normalized local cardinal denominator. -/
noncomputable def localCardinal (a h u t : ℕ) : ℚ[X] :=
  ∏ q∈others a t,
    ((1:ℚ[X])+C (((2:ℤ)^(a+1):ℚ)/((point a t:ℚ)-(point a q:ℚ)))*X)^nodeMultiplicity a h u q

/-- The executed original slope list describes EXACTLY the original local D.9 factors. -/
theorem slopes_product (a h u t : ℕ) :
    ((slopes a h u t).map (fun c => (1:ℚ[X])+C c*X)).prod=localCardinal a h u t := by
  let f := fun q => (((2:ℤ)^(a+1):ℚ)/((point a t:ℚ)-(point a q:ℚ)))
  have he (ls : List ℕ) :
      ((ls.flatMap (fun q => if q=center a ∨ q=t then [] else
        List.replicate (nodeMultiplicity a h u q) (f q))).map
          (fun c => (1:ℚ[X])+C c*X)).prod=
      (ls.map (fun q => if q=center a ∨ q=t then 1 else
        ((1:ℚ[X])+C (f q)*X)^nodeMultiplicity a h u q)).prod := by
    induction ls with
    | nil => simp
    | cons q ls ih =>
      by_cases hx : q=center a ∨ q=t <;> simp [hx,ih]
  rw [slopes]
  change ((List.range (size a) |>.flatMap (fun q => if q=center a ∨ q=t then [] else
      List.replicate (nodeMultiplicity a h u q) (f q))).map
        (fun c => (1:ℚ[X])+C c*X)).prod=_
  rw [he,← List.prod_toFinset _ List.nodup_range,List.toFinset_range]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul]
  unfold localCardinal
  have hs : (Finset.range (size a)).filter (fun q => ¬(q=center a ∨ q=t))=others a t := by
    ext q
    simp [others]
    tauto
  rw [hs]

/-- The local cardinal constant is1; the acquired recurrence inverse has a genuine unit input. -/
theorem localCardinal_constant (a h u t : ℕ) : (localCardinal a h u t).coeff 0=1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero,localCardinal,Polynomial.eval_prod]
  apply Finset.prod_eq_one
  intro q _
  simp

/-- Native original-grid scalar weight for one retained input coefficient.
The full finite k-range makes its linear/convolution meaning explicit. -/
def localWeight (q : ℕ) (e x : ℚ) (inv : Array ℚ) (j : ℕ) : ℚ :=
  e*∑ k∈Finset.range q,if j≤k then coefficient inv (k-j)*x^k else 0

/-- Acquired local denominator/inverse arrays and scalar linear weights. -/
structure WeightData where
  /-- Actual retained Taylor multiplicity of this original node. -/
  retained : ℕ
  /-- Actual original finite-product E_t(0). -/
  valueAtZero : ℚ
  /-- Rational scalar -t/alpha, never a nilpotent-ring evaluation oracle. -/
  argument : ℚ
  /-- Actual finite affine product report. -/
  denominator : InverseReport
  /-- Actual cached recurrence inverse report. -/
  inverse : InverseReport
  /-- Stored scalar-rational weights, acquired once for this node. -/
  weights : Array ℚ

/-- Complete original node weight acquisition; no denominator/inverse/weight answer input. -/
def acquire (a h u t : ℕ) : WeightData :=
  let q := nodeMultiplicity a h u t
  let E0 := Ezero a h u t
  let x := -(point a t:ℚ)/((2:ℤ)^(a+1):ℚ)
  let denominator := buildAffine q (slopes a h u t)
  let inverse := SemiprimeJetArray.inverse denominator.coefficients q
  ⟨q,E0,x,denominator,inverse,
    Array.ofFn (fun j : Fin q => localWeight q E0 x inverse.coefficients j.val)⟩

/-- Acquired original denominator array is the actual retained local cardinal packet. -/
theorem acquire_denominator (a h u t : ℕ) (hq : 0<nodeMultiplicity a h u t) :
    asPolynomial (acquire a h u t).denominator.coefficients=
      localCardinal a h u t %ₘ X^nodeMultiplicity a h u t := by
  exact (buildAffine_polynomial _ hq _).trans (by rw [slopes_product])

/-- Original constructed denominator has constant1, without an inverse/denominator oracle. -/
theorem acquire_denominator_constant (a h u t : ℕ) (hq : 0<nodeMultiplicity a h u t) :
    coefficient (acquire a h u t).denominator.coefficients 0=1 := by
  rw [← asPolynomial_coeff,acquire_denominator a h u t hq,coeff_mod_X_pow]
  simpa only [hq,ite_true] using localCardinal_constant a h u t

/-- Exactly the needed number of weights is stored, no full degree interpolation array. -/
theorem acquire_weights_size (a h u t : ℕ) :
    (acquire a h u t).weights.size=nodeMultiplicity a h u t := by simp [acquire]

/-- Each retained scalar is the actual constructed original-grid weight. -/
theorem acquire_weight (a h u t j : ℕ) (hj : j<nodeMultiplicity a h u t) :
    coefficient (acquire a h u t).weights j=
      localWeight (nodeMultiplicity a h u t) (Ezero a h u t)
        (-(point a t:ℚ)/((2:ℤ)^(a+1):ℚ)) (acquire a h u t).inverse.coefficients j := by
  simp [acquire,coefficient,hj]

/-- Exact truncated convolution agrees with a full finite triangular sum. -/
theorem lower_sum (q k : ℕ) (hk : k<q) (f : ℕ→ℚ) :
    (∑ j∈Finset.range q,if j≤k then f j else 0)=∑ j∈Finset.range (k+1),f j := by
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_filter,Finset.mem_range]
  omega

/-- The D.9 node scalar is precisely a LINEAR functional of the retained H coefficients. -/
theorem local_linear (q : ℕ) (e x : ℚ) (H inv : Array ℚ) :
    e*∑ k∈Finset.range q,coefficient (multiply H inv q).coefficients k*x^k=
      ∑ j∈Finset.range q,localWeight q e x inv j*coefficient H j := by
  have he : ∀ k∈Finset.range q,
      coefficient (multiply H inv q).coefficients k*x^k=
      ∑ j∈Finset.range q,if j≤k then coefficient H j*coefficient inv (k-j)*x^k else 0 := by
    intro k hk
    rw [multiply_coefficient H inv q k (Finset.mem_range.mp hk),Finset.sum_mul,
      lower_sum q k (Finset.mem_range.mp hk)]
  rw [show (∑ k∈Finset.range q,coefficient (multiply H inv q).coefficients k*x^k)=
      ∑ k∈Finset.range q,∑ j∈Finset.range q,
        if j≤k then coefficient H j*coefficient inv (k-j)*x^k else 0 from
      Finset.sum_congr rfl he]
  rw [Finset.sum_comm]
  simp only [localWeight,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

/-- Original node weight execution equals its ACTUAL cached inverse/convolution output. -/
theorem original_local_linear (a h u t : ℕ) (H : Array ℚ) :
    (acquire a h u t).valueAtZero*
      (∑ k∈Finset.range (acquire a h u t).retained,
        coefficient (multiply H (acquire a h u t).inverse.coefficients
          (acquire a h u t).retained).coefficients k*(acquire a h u t).argument^k)=
    ∑ j∈Finset.range (acquire a h u t).retained,
      coefficient (acquire a h u t).weights j*coefficient H j := by
  rw [local_linear]
  apply Finset.sum_congr rfl
  intro j hj
  rw [acquire_weight a h u t j (Finset.mem_range.mp hj)]
  rfl

/-- Polynomial interpretation of a finite retained array evaluates by its coefficient sum. -/
theorem array_eval (a : Array ℚ) (x : ℚ) :
    (asPolynomial a).eval x=∑ k∈Finset.range a.size,coefficient a k*x^k := by
  simp only [asPolynomial,jetPolynomial,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

/-- Actual scalar weights give the EXACT D.9 LOCAL quotient contribution from
retained data and the original acquired cardinal inverse, not a desired inverse premise. -/
theorem original_node_formula (a h u t : ℕ) (H : Array ℚ)
    (hq : 0<nodeMultiplicity a h u t) :
    Ezero a h u t*
      (SemiprimeHermiteRecovery.localQuotient (asPolynomial H)
        (localCardinal a h u t %ₘ X^nodeMultiplicity a h u t)
        (nodeMultiplicity a h u t)).eval (-(point a t:ℚ)/((2:ℤ)^(a+1):ℚ))=
    ∑ j∈Finset.range (nodeMultiplicity a h u t),
      coefficient (acquire a h u t).weights j*coefficient H j := by
  rw [← acquire_denominator a h u t hq,
    ← quotient_correct H (acquire a h u t).denominator.coefficients
      (nodeMultiplicity a h u t) (acquire_denominator_constant a h u t hq)]
  change Ezero a h u t*(asPolynomial
      (multiply H (acquire a h u t).inverse.coefficients (nodeMultiplicity a h u t)).coefficients).eval
        (-(point a t:ℚ)/((2:ℤ)^(a+1):ℚ))=_
  rw [array_eval,multiply_size]
  exact original_local_linear a h u t H

/-- Apply the actual acquired weights to each coordinate; no ring product/evaluation is used. -/
def combineCoordinates (m : ℕ) (data : WeightData) (H : ℕ→Fin m→ℚ) : Fin m→ℚ :=
  fun c => ∑ j∈Finset.range data.retained,coefficient data.weights j*H j c

/-- Coordinatewise addition is preserved by the actual scalar linear combiner. -/
theorem combineCoordinates_add (m : ℕ) (data : WeightData) (H K : ℕ→Fin m→ℚ) :
    combineCoordinates m data (fun j c => H j c+K j c)=
      fun c => combineCoordinates m data H c+combineCoordinates m data K c := by
  funext c
  simp only [combineCoordinates,mul_add,Finset.sum_add_distrib]

/-- Scalar multiplication is preserved, including finite free nilpotent-algebra coordinates. -/
theorem combineCoordinates_smul (m : ℕ) (data : WeightData) (H : ℕ→Fin m→ℚ) (r : ℚ) :
    combineCoordinates m data (fun j c => r*H j c)=
      fun c => r*combineCoordinates m data H c := by
  funext c
  simp only [combineCoordinates,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end RiemannGaussian.SemiprimeD1JetRecoveryWeights
