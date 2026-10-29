/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCounterPacketHeight

/-!
# Local truth-prefix and leaf-product heights

Partial truth sums are masked tensor tables of the same arity. Partial leaf
products have explicit integer numerators padded to the same arity denominator.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace RiemannGaussian.SemiprimeLocalPrefixHeight
open scoped BigOperators
open Polynomial
open SemiprimeStreamingTensor SemiprimeStreamingTensorHeight
open SemiprimeCounterPacketHeight SemiprimeJetArrayHeight
attribute [local instance] Classical.propDecidable

/-- The actual partial product used while building one interpolation leaf. -/
def leafProduct {C : Type*} [CommRing C] (w : ℕ) (eta : Fin w → Bool)
    (selected : Finset (Fin w)) (ports : Fin w → C) : C :=
  ∏ i ∈ selected, if eta i then ports i else 1-ports i

/-- A truth-table subtotal is the same-arity tensor with a literal zero mask. -/
theorem masked_evaluate {C : Type*} [CommRing C] (w : ℕ)
    (T : (Fin w → Bool) → C) (ports : Fin w → C) (truth : Finset (Fin w → Bool)) :
    evaluate w (fun eta => if eta ∈ truth then T eta else 0) ports =
      ∑ eta ∈ truth, T eta * leafProduct w eta Finset.univ ports := by
  rw [evaluate_eq_sum]
  simp only [ite_mul, zero_mul, leafProduct, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- A mask preserves the actual integer-table coefficient bound. -/
theorem masked_table_abs (w : ℕ) (T : (Fin w → Bool) → ℤ)
    (hT : ∀ eta, |T eta| ≤ 1) (truth : Finset (Fin w → Bool)) (eta : Fin w → Bool) :
    |(if eta ∈ truth then T eta else 0 : ℤ)| ≤ 1 := by
  split_ifs
  · exact hT eta
  · norm_num

/-- Missing leaf ports are padded by the known integer denominator power. -/
def leafNumerator (d w : ℕ) (eta : Fin w → Bool) (selected : Finset (Fin w))
    (P : Fin w → Polynomial ℤ) : Polynomial ℤ :=
  C ((d : ℤ)^(w-selected.card)) * ∏ i ∈ selected, if eta i then P i else C (d : ℤ)-P i

/-- The padding is an exact common-denominator identity, without any division
by a port or by a possibly vanishing local factor. -/
theorem leafNumerator_map (d w : ℕ) (eta : Fin w → Bool) (selected : Finset (Fin w))
    (P : Fin w → Polynomial ℤ) (ports : Fin w → Polynomial ℚ)
    (hP : ∀ i, (P i).map (Int.castRingHom ℚ)=C (d : ℚ)*ports i) :
    (leafNumerator d w eta selected P).map (Int.castRingHom ℚ) =
      C ((d : ℚ)^w)*leafProduct w eta selected ports := by
  have hc : selected.card ≤ w := (Finset.card_le_univ selected).trans_eq (by simp)
  have hi (i : Fin w) :
      (if eta i then P i else C (d : ℤ)-P i).map (Int.castRingHom ℚ) =
        C (d : ℚ)*(if eta i then ports i else 1-ports i) := by
    cases he : eta i
    · simp only [ Bool.false_eq_true, ite_false, Polynomial.map_sub, Polynomial.map_C, hP]
      change C (d : ℚ)-C (d : ℚ)*ports i = _
      ring
    · simp only [ ite_true, hP]
  simp only [leafNumerator, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_prod, hi, Finset.prod_mul_distrib, Finset.prod_const, ← C_pow, leafProduct]
  have hcast (k : ℕ) : (Int.castRingHom ℚ) ((d : ℤ)^k) = (d : ℚ)^k := by
    rw [map_pow, map_natCast]
  rw [hcast]
  change C ((d : ℚ)^(w-selected.card)) *
    (C ((d : ℚ)^selected.card) * _) = _
  rw [← mul_assoc, ← C_mul, ← pow_add, Nat.sub_add_cancel hc]

/-- Every intermediate leaf product has a bounded numerator at the original arity. -/
theorem leafNumerator_bound (d w B J : ℕ) (hJ : 1 ≤ J) (eta : Fin w → Bool)
    (selected : Finset (Fin w)) (P : Fin w → Polynomial ℤ)
    (hP : ∀ i k, k<J → |(P i).coeff k| ≤ (B : ℤ)) (k : ℕ) (hk : k<J) :
    |(leafNumerator d w eta selected P).coeff k| ≤ (((J*(d+2*B))^w : ℕ) : ℤ) := by
  have hc : selected.card ≤ w := (Finset.card_le_univ selected).trans_eq (by simp)
  have hfactor (i : Fin w) (j : ℕ) (hj : j<J) :
      |(if eta i then P i else C (d : ℤ)-P i).coeff j| ≤ (d+B : ℕ) := by
    cases he : eta i
    · simp only [ Bool.false_eq_true, ite_false, Polynomial.coeff_sub]
      have hC : |(C (d : ℤ)).coeff j| ≤ (d : ℤ) := by
        simp only [Polynomial.coeff_C]
        split_ifs <;> simp
      exact (abs_sub _ _).trans (by exact_mod_cast add_le_add hC (hP i j hj))
    · simp only [ ite_true]
      exact (hP i j hj).trans (by exact_mod_cast Nat.le_add_left B d)
  have hp := abs_coeff_prod_le selected
    (fun i => if eta i then P i else C (d : ℤ)-P i) J hJ (fun _ => (d+B : ℕ))
    (fun _ => by positivity) (fun i _ j hj => hfactor i j hj) k hk
  simp only [Finset.prod_const] at hp
  have hb : |(∏ i ∈ selected, if eta i then P i else C (d : ℤ)-P i).coeff k| ≤
      (J*(d+B) : ℕ)^selected.card := by
    simpa only [Nat.cast_mul, mul_pow, Nat.cast_pow] using hp
  rw [leafNumerator, Polynomial.coeff_C_mul, abs_mul, abs_pow, Int.abs_natCast]
  calc
    _ ≤ (d : ℤ)^(w-selected.card)*(J*(d+B) : ℕ)^selected.card :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (J*(d+2*B) : ℕ)^(w-selected.card)*(J*(d+2*B) : ℕ)^selected.card := by
      have hd : d ≤ J*(d+2*B) := by nlinarith
      have hdb : J*(d+B) ≤ J*(d+2*B) := by nlinarith
      have hnat := Nat.mul_le_mul (Nat.pow_le_pow_left hd (w-selected.card))
        (Nat.pow_le_pow_left hdb selected.card)
      exact_mod_cast hnat
    _ = _ := by push_cast; rw [← pow_add, Nat.sub_add_cancel hc]

/-- The corrected tensor value itself has a literal same-arity denominator. -/
theorem evaluate_representation (d w B J : ℕ) (hd : 0<d) (_hJ : 1≤J)
    (T : (Fin w → Bool) → ℤ) (hT : ∀ eta, |T eta| ≤ 1)
    (P : Fin w → Polynomial ℤ) (ports : Fin w → Polynomial ℚ)
    (hP : ∀ i, (P i).map (Int.castRingHom ℚ)=C (d : ℚ)*ports i)
    (hb : ∀ i k, k<J → |(P i).coeff k| ≤ (B : ℤ)) (k : ℕ) (hk : k<J) :
    Representation ((evaluate w (fun eta => C (T eta : ℚ)) ports).coeff k)
      (d^w) ((J*(d+2*B))^w) := by
  have hdZ : (d : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  have hm := polynomialNumerator_map (d : ℤ) hdZ w T P
  have hports (i : Fin w) : C ((d : ℚ)⁻¹)*(P i).map (Int.castRingHom ℚ)=ports i := by
    rw [hP, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hdq, C_1, one_mul]
  simp only [Int.cast_natCast, hports] at hm
  refine ⟨(polynomialNumerator (d : ℤ) w T P).coeff k, ?_, ?_⟩
  · have he := congrArg (fun p : Polynomial ℚ => p.coeff k) hm
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at he
    change (((polynomialNumerator (d : ℤ) w T P).coeff k : ℤ) : ℚ)=_ at he
    apply (eq_div_iff (by exact_mod_cast Nat.ne_of_gt (pow_pos hd _))).mpr
    simpa only [Nat.cast_pow, mul_comm] using he.symm
  · have h := abs_coeff_polynomialNumerator_le (d : ℤ) w J T P (B : ℤ)
      (by positivity) hT hb k hk
    have h' : (((polynomialNumerator (d : ℤ) w T P).coeff k).natAbs : ℤ) ≤
        ((J*(d+2*B))^w : ℕ) := by
      simpa only [Int.natCast_natAbs, Int.abs_natCast, Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using h
    exact_mod_cast h'

/-- The actual selected-port leaf coefficient inherits the same arity denominator. -/
theorem leaf_representation (d w B J : ℕ) (hd : 0<d) (hJ : 1≤J)
    (eta : Fin w → Bool) (selected : Finset (Fin w))
    (P : Fin w → Polynomial ℤ) (ports : Fin w → Polynomial ℚ)
    (hP : ∀ i, (P i).map (Int.castRingHom ℚ)=C (d : ℚ)*ports i)
    (hb : ∀ i k, k<J → |(P i).coeff k| ≤ (B : ℤ)) (k : ℕ) (hk : k<J) :
    Representation ((leafProduct w eta selected ports).coeff k) (d^w) ((J*(d+2*B))^w) := by
  have hm := leafNumerator_map d w eta selected P ports hP
  refine ⟨(leafNumerator d w eta selected P).coeff k, ?_, ?_⟩
  · have he := congrArg (fun p : Polynomial ℚ => p.coeff k) hm
    simp only [Polynomial.coeff_map, Polynomial.coeff_C_mul] at he
    change (((leafNumerator d w eta selected P).coeff k : ℤ) : ℚ)=_ at he
    apply (eq_div_iff (by exact_mod_cast Nat.ne_of_gt (pow_pos hd _))).mpr
    simpa only [Nat.cast_pow, mul_comm] using he.symm
  · have h := leafNumerator_bound d w B J hJ eta selected P hb k hk
    have h' : (((leafNumerator d w eta selected P).coeff k).natAbs : ℤ) ≤ ((J*(d+2*B))^w : ℕ) := by
      simpa only [Int.natCast_natAbs] using h
    exact_mod_cast h'

section Native
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Actual native source inputs supply all local numerator polynomials at once. -/
theorem built_local_inputs (arity : E → ℕ) {r Q : ℕ}
    (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R B T : ℕ)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i=v)).card ≤ B)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (e : E) (t : ℤ) (ht : |t| ≤ (T : ℤ)) (x U : Finset V) :
    ∃ P : Fin (arity e) → Polynomial ℤ,
      (∀ i, (P i).map (Int.castRingHom ℚ)=C (SemiprimeSourceRowHeight.rowDenominator Q R : ℚ)*
        correctedPort ((builtRows arity owner en ε R) e i) (t : ℚ) R x U) ∧
      ∀ i k, |(P i).coeff k| ≤ (Fintype.card V*SemiprimeTaylorHeight.shiftBound R
        (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) T : ℕ) := by
  choose P hP hb using fun i : Fin (arity e) =>
    builtLayout_correctedPort_representation owner Sigma.fst en ε R B T howner hQ hAQ ⟨e,i⟩ t ht x U
  exact ⟨P,hP,hb⟩

/-- Every actual truth-loop subtotal has a native same-arity denominator and
bounded numerator; no cancellation or output-fit oracle is assumed. -/
theorem built_truth_prefix_representation (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    {r Q : ℕ} (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R B T J : ℕ) (hJ : 1≤J)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i=v)).card ≤ B)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hentry : ∀ e eta, |Tentry e eta| ≤ 1)
    (e : E) (t : ℤ) (ht : |t| ≤ (T : ℤ)) (x U : Finset V)
    (truth : Finset (Fin (arity e) → Bool)) (k : ℕ) (hk : k<J) :
    Representation ((∑ eta ∈ truth, C (Tentry e eta : ℚ)*leafProduct (arity e) eta Finset.univ
      (fun i => correctedPort ((builtRows arity owner en ε R) e i) (t : ℚ) R x U)).coeff k)
      ((SemiprimeSourceRowHeight.rowDenominator Q R)^arity e)
      ((J*(SemiprimeSourceRowHeight.rowDenominator Q R+2*(Fintype.card V*SemiprimeTaylorHeight.shiftBound R
        (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) T)))^arity e) := by
  obtain ⟨P,hP,hb⟩ := built_local_inputs arity owner en ε R B T howner hQ hAQ e t ht x U
  have h := evaluate_representation (SemiprimeSourceRowHeight.rowDenominator Q R) (arity e)
    (Fintype.card V*SemiprimeTaylorHeight.shiftBound R (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) T)
    J (SemiprimeSourceRowHeight.rowDenominator_pos Q R) hJ
    (fun eta => if eta ∈ truth then Tentry e eta else 0) (masked_table_abs _ _ (hentry e) truth)
    P (fun i => correctedPort ((builtRows arity owner en ε R) e i) (t : ℚ) R x U) hP
    (fun i j _ => hb i j) k hk
  have htable : (fun eta => C ((if eta ∈ truth then Tentry e eta else 0 : ℤ) : ℚ)) =
      (fun eta => if eta ∈ truth then C (Tentry e eta : ℚ) else 0) := by
    funext eta
    split_ifs <;> simp
  rw [htable, masked_evaluate] at h
  exact h

/-- Every actual port-product prefix uses the padded full local denominator. -/
theorem built_leaf_prefix_representation (arity : E → ℕ) {r Q : ℕ}
    (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R B T J : ℕ) (hJ : 1≤J)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i=v)).card ≤ B)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (e : E) (t : ℤ) (ht : |t| ≤ (T : ℤ)) (x U : Finset V)
    (eta : Fin (arity e) → Bool) (selected : Finset (Fin (arity e))) (k : ℕ) (hk : k<J) :
    Representation ((leafProduct (arity e) eta selected
      (fun i => correctedPort ((builtRows arity owner en ε R) e i) (t : ℚ) R x U)).coeff k)
      ((SemiprimeSourceRowHeight.rowDenominator Q R)^arity e)
      ((J*(SemiprimeSourceRowHeight.rowDenominator Q R+2*(Fintype.card V*SemiprimeTaylorHeight.shiftBound R
        (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) T)))^arity e) := by
  obtain ⟨P,hP,hb⟩ := built_local_inputs arity owner en ε R B T howner hQ hAQ e t ht x U
  exact leaf_representation (SemiprimeSourceRowHeight.rowDenominator Q R) (arity e)
    (Fintype.card V*SemiprimeTaylorHeight.shiftBound R (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) T)
    J (SemiprimeSourceRowHeight.rowDenominator_pos Q R) hJ eta selected P
    (fun i => correctedPort ((builtRows arity owner en ε R) e i) (t : ℚ) R x U) hP
    (fun i j _ => hb i j) k hk

/-- The entry-weighted leaf-product prefix obeys the same bound as its unweighted
leaf: Boolean entries cannot introduce a new denominator or larger numerator. -/
theorem built_weighted_leaf_prefix_representation (arity : E → ℕ)
    (Tentry : (e : E) → (Fin (arity e) → Bool) → ℤ)
    {r Q : ℕ} (owner : ((e : E) × Fin (arity e)) → V)
    (en : SemiprimeSourceLayout.Enumerations ((e : E) × Fin (arity e)) V E r Q)
    (ε : ℚ) (R B T J : ℕ) (hJ : 1≤J)
    (howner : ∀ v, (Finset.univ.filter (fun i => owner i=v)).card ≤ B)
    (hQ : 1≤Q) (hAQ : OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R ≤ Q)
    (hentry : ∀ e eta, |Tentry e eta| ≤ 1)
    (e : E) (t : ℤ) (ht : |t| ≤ (T : ℤ)) (x U : Finset V)
    (eta : Fin (arity e) → Bool) (selected : Finset (Fin (arity e))) (k : ℕ) (hk : k<J) :
    Representation ((C (Tentry e eta : ℚ)*leafProduct (arity e) eta selected
      (fun i => correctedPort ((builtRows arity owner en ε R) e i) (t : ℚ) R x U)).coeff k)
      ((SemiprimeSourceRowHeight.rowDenominator Q R)^arity e)
      ((J*(SemiprimeSourceRowHeight.rowDenominator Q R+2*(Fintype.card V*SemiprimeTaylorHeight.shiftBound R
        (B*2^SemiprimeSourceRowHeight.rowNumeratorExponent Q R) T)))^arity e) := by
  have h := built_leaf_prefix_representation arity owner en ε R B T J hJ howner hQ hAQ e t ht x U eta selected k hk
  have hc : Representation (Tentry e eta : ℚ) 1 1 := by
    refine ⟨Tentry e eta, by simp, ?_⟩
    have he : ((Tentry e eta).natAbs : ℤ) ≤ 1 := by simpa only [Int.natCast_natAbs] using hentry e eta
    exact_mod_cast he
  rw [Polynomial.coeff_C_mul]
  simpa only [Nat.one_mul] using representation_mul hc h

end Native

end RiemannGaussian.SemiprimeLocalPrefixHeight

#print axioms RiemannGaussian.SemiprimeLocalPrefixHeight.built_truth_prefix_representation
#print axioms RiemannGaussian.SemiprimeLocalPrefixHeight.built_leaf_prefix_representation

#print axioms RiemannGaussian.SemiprimeLocalPrefixHeight.built_weighted_leaf_prefix_representation
