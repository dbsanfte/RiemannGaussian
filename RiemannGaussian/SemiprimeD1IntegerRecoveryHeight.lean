/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1IntegerRecovery

/-! # Original-derived heights of every integer recovery suffix
The bounds concern the actual acquired scalar weights and actual decoded child
words. A child word length bound is an internal recursive-stage contract, not a
requested numerator, inverse, or recovery answer.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1IntegerRecoveryHeight
open SemiprimeD1IntegerRecovery SemiprimeD1HermiteWeightBits
  SemiprimeD1WeightPrecision SemiprimeD1WireKernelOriginal
  SemiprimeD1TaperedLoss SemiprimeD1JetRecoveryGrid SemiprimeD1JetRecoveryWeights

/-- The actual retained term count is at most original grid size times4M. -/
theorem terms_length (a M u : ℕ) (hM : u≤M) (children : ℕ → Array (List Bool)) :
    (terms a M u children).length≤ size a*(4*M) := by
  let f : ℕ → List Term := fun t =>
    let w := acquire a (height M u) u t
    (List.range w.retained).map fun j =>
      ⟨SemiprimeJetArray.coefficient w.weights j,(children t)[j]?.getD []⟩
  have hf : ∀t,(f t).length≤4*M := by
    intro t
    simp only [f,List.length_map,List.length_range]
    change nodeMultiplicity a (height M u) u t≤4*M
    exact nodeMultiplicity_le a M u t hM
  have hall : ∀xs : List ℕ,(xs.flatMap f).length≤xs.length*(4*M) := by
    intro xs
    induction xs with
    | nil => simp
    | cons t ts ih =>
      simpa only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,one_mul,Nat.add_comm] using
        Nat.add_le_add (hf t) ih
  exact (hall _).trans (Nat.mul_le_mul_right _ (by simpa only [List.length_range] using List.length_filter_le (fun t => decide (t≠center a ∧ 0<nodeMultiplicity a (height M u) u t)) (List.range (size a))))

/-- Every term has the actual original scalar-weight dyadic bound. -/
theorem term_bounds (a M u : ℕ) (hM : u≤M) (children : ℕ → Array (List Bool))
    (v : Term) (hv : v∈terms a M u children) :
    v.weight.den≤2^weightEnvelope a M ∧ v.weight.num.natAbs≤2^weightEnvelope a M := by
  obtain ⟨t,ht,hq,j,hj,rfl⟩ := terms_mem a M u children v hv
  have hb := original_weight_bits a (height M u) u ⟨t,ht⟩ hq j hj
  have he := original_weightExponent_le a M u t hM
  exact ⟨hb.1.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) he),
    hb.2.trans (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) he)⟩

/-- The actual product denominator grows in bits, rather than in repeated rational sums. -/
theorem denominator_bound (a M u : ℕ) (hM : u≤M) (children : ℕ → Array (List Bool)) :
    denominator (terms a M u children)≤2^(weightEnvelope a M*(terms a M u children).length) := by
  unfold denominator
  have hp := List.prod_le_pow_length ((terms a M u children).map fun t => t.weight.den)
    (2^weightEnvelope a M) (by
      intro d hd
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hd
      exact (term_bounds a M u hM children t ht).1)
  simpa only [List.length_map,← pow_mul] using hp

/-- Actual child decoding has a derived dyadic cap from its original word length. -/
theorem decode_bound (P : ℕ) (bs : List Bool) (hb : bs.length≤P) : decode bs≤2^P := by
  rw [decode_eq]
  exact (SemiprimeBitArithmetic.bitValue_lt_width bs).le.trans
    (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hb)

/-- Every acquired child occurrence obeys the recursive word-width contract. -/
theorem term_child_bound (a M u P : ℕ) (children : ℕ → Array (List Bool))
    (hc : ∀(t j : ℕ), ((children t)[j]?.getD []).length≤P)
    (v : Term) (hv : v∈terms a M u children) : decode v.child≤2^P := by
  obtain ⟨t,_,_,j,_,rfl⟩ := terms_mem a M u children v hv
  exact decode_bound P _ (hc t j)

/-- All actual suffix numerators share a cancellation-independent derived height. -/
theorem original_suffix_bound (a M u P : ℕ) (hM : u≤M)
    (children : ℕ → Array (List Bool))
    (hc : ∀(t j : ℕ), ((children t)[j]?.getD []).length≤P) (k : ℕ) :
    (accumulate (denominator (terms a M u children)) ((terms a M u children).drop k)).natAbs≤
      (terms a M u children).length*
        (2^weightEnvelope a M*2^(weightEnvelope a M*(terms a M u children).length)*2^P) := by
  have h := accumulate_suffix_abs (denominator (terms a M u children))
    (2^weightEnvelope a M) (2^P) (terms a M u children) k
    (fun t ht => (term_bounds a M u hM children t ht).2)
    (fun t ht => term_child_bound a M u P children hc t ht)
  exact h.trans (Nat.mul_le_mul_left _
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (denominator_bound a M u hM children))))

/-- Explicit original-dimension logarithmic cap for every integer accumulation frame. -/
def recoveryExponent (a M P : ℕ) : ℕ :=
  size a*(4*M)+(1+size a*(4*M))*weightEnvelope a M+P

/-- Actual ALL-suffix dyadic bound, using only original dimensions and child width. -/
theorem original_suffix_bits (a M u P : ℕ) (hM : u≤M)
    (children : ℕ → Array (List Bool))
    (hc : ∀(t j : ℕ), ((children t)[j]?.getD []).length≤P) (k : ℕ) :
    (accumulate (denominator (terms a M u children)) ((terms a M u children).drop k)).natAbs≤
      2^recoveryExponent a M P := by
  have hlen := terms_length a M u hM children
  have ht : (terms a M u children).length≤2^(size a*(4*M)) :=
    hlen.trans (SemiprimeD1HermiteDenominatorBits.self_le_two_power _)
  calc
    _ ≤ (terms a M u children).length*
        (2^weightEnvelope a M*2^(weightEnvelope a M*(terms a M u children).length)*2^P) :=
      original_suffix_bound a M u P hM children hc k
    _ ≤ 2^(size a*(4*M))*(2^weightEnvelope a M*
          2^(weightEnvelope a M*(size a*(4*M)))*2^P) :=
      Nat.mul_le_mul ht (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.mul_le_mul_left _ hlen))))
    _ = _ := by simp only [← pow_add,recoveryExponent];congr 1;ring

/-- Independent original dimensions expose the literal fixed polynomial. -/
def recoveryPolynomial (a M N P : ℕ) : ℕ :=
  N*(4*M)+(1+N*(4*M))*weightPolynomial a M N+P

/-- The runtime-derived exponent is the polynomial at the original acquired grid size. -/
theorem recoveryExponent_eq (a M P : ℕ) :
    recoveryExponent a M P=recoveryPolynomial a M (size a) P := by
  simp only [recoveryExponent,recoveryPolynomial,weightEnvelope_eq]

/-- Pure arithmetic monotonicity, with no original execution terms in tactic context. -/
theorem recoveryPolynomial_mono {a M N P A B D E : ℕ}
    (ha : a≤A) (hM : M≤B) (hN : N≤D) (hP : P≤E) :
    recoveryPolynomial a M N P≤recoveryPolynomial A B D E := by
  unfold recoveryPolynomial
  exact Nat.add_le_add (Nat.add_le_add (by gcongr)
    (Nat.mul_le_mul (by gcongr) (weightPolynomial_mono ha hM hN))) hP

/-- An explicit fixed monomial bounds every actual integer recovery frame logarithm. -/
theorem recoveryPolynomial_diagonal (S : ℕ) :
    recoveryPolynomial S S S S≤10000*(S+1)^6 := by
  unfold recoveryPolynomial weightPolynomial inversePolynomial
  nlinarith [Nat.zero_le (S^2),Nat.zero_le (S^3),Nat.zero_le (S^4),Nat.zero_le (S^5),Nat.zero_le (S^6)]

end RiemannGaussian.SemiprimeD1IntegerRecoveryHeight
