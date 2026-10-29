/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-!
# Exact recovery from the counter's Taylor packets

The distinct sample points and their retained Taylor coefficients determine the
entire counting polynomial at its actual degree bound. This uses polynomial
divisibility, including multiplicities; values at the sample points alone do not
suffice. The explicit rational Hermite computation still needs its execution
refinement and bit-cost proof.
-/

namespace RiemannGaussian.SemiprimeHermiteRecovery
open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

theorem zero_of_taylor_packets (points : Finset K) (J : ℕ) (p : Polynomial K)
    (hdegree : p.natDegree < points.card * J)
    (hjets : ∀ t ∈ points, ∀ k < J, (taylor t p).coeff k = 0) : p = 0 := by
  classical
  have hdiv : (∏ t ∈ points, (X - C t)^J) ∣ p := by
    apply Finset.prod_dvd_of_coprime
    · intro a ha b hb hab
      exact (pairwise_coprime_X_sub_C (s := fun x : K => x) Function.injective_id hab).pow
    · intro t ht
      rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
      simpa only [taylor_apply] using hjets t ht
  have hprod : (∏ t ∈ points, (X - C t)^J).natDegree = points.card * J := by
    rw [natDegree_prod_of_monic points (fun t => (X-C t)^J)
      (fun t _ => (monic_X_sub_C t).pow J)]
    simp
  by_contra hp
  have hle := natDegree_le_of_dvd hdiv hp
  rw [hprod] at hle
  omega

theorem eq_of_taylor_packets (points : Finset K) (J : ℕ) (p q : Polynomial K)
    (hp : p.natDegree < points.card * J) (hq : q.natDegree < points.card * J)
    (hjets : ∀ t ∈ points, ∀ k < J, (taylor t p).coeff k = (taylor t q).coeff k) :
    p = q := by
  apply sub_eq_zero.mp
  apply zero_of_taylor_packets points J (p-q)
  · exact (natDegree_sub_le p q).trans_lt (max_lt hp hq)
  · intro t ht k hk
    simpa only [map_sub, coeff_sub, sub_eq_zero] using hjets t ht k hk

/-- The exact Q positive rational nodes used by the implementation. -/
def samplePoints (Q : ℕ) : Finset ℚ :=
  Finset.univ.image (fun i : Fin Q => (i.val : ℚ) + 1)

theorem samplePoints_card (Q : ℕ) : (samplePoints Q).card = Q := by
  classical
  have hinj : Function.Injective (fun i : Fin Q => (i.val : ℚ) + 1) := by
    intro i j h
    apply Fin.ext
    exact_mod_cast add_right_cancel h
  simp only [samplePoints, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin]

theorem eq_of_counter_packets (Q J : ℕ) (p q : Polynomial ℚ)
    (hp : p.natDegree < Q*J) (hq : q.natDegree < Q*J)
    (hjets : ∀ i : Fin Q, ∀ k < J,
      (taylor ((i.val : ℚ)+1) p).coeff k = (taylor ((i.val : ℚ)+1) q).coeff k) :
    p = q := by
  apply eq_of_taylor_packets (samplePoints Q) J p q
  · simpa only [samplePoints_card] using hp
  · simpa only [samplePoints_card] using hq
  · intro t ht k hk
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    exact hjets i k hk

/-- The code's J=floor(dR/Q)+1 supplies strictly more coefficients than degree. -/
theorem counter_precision_sufficient (Q d R : ℕ) (hQ : 0 < Q) :
    d*R < Q*(d*R/Q+1) := by
  have h := Nat.mod_lt (d*R) hQ
  have he := Nat.mod_add_div (d*R) Q
  nlinarith

/-- Explicit finite geometric inverse of a polynomial with constant coefficient one. -/
noncomputable def inverseJet (L : Polynomial K) (J : ℕ) : Polynomial K :=
  ∑ i ∈ Finset.range J, (1-L)^i

theorem inverseJet_congruence (L : Polynomial K) (J : ℕ) (hL : L.coeff 0 = 1) :
    X^J ∣ L * inverseJet L J - 1 := by
  have hx : X ∣ 1-L := X_dvd_iff.mpr (by simp [hL])
  have hgeom : L * inverseJet L J = 1-(1-L)^J := by
    have h := geom_sum_mul_neg (1-L) J
    simpa [inverseJet, mul_comm] using h
  rw [hgeom]
  convert (pow_dvd_pow_of_dvd hx J).neg_right using 1; ring

/-- The local quotient is a genuine truncation of a constructed inverse product. -/
noncomputable def localQuotient (H L : Polynomial K) (J : ℕ) : Polynomial K :=
  (H * inverseJet L J) %ₘ X^J

theorem localQuotient_congruence (H L : Polynomial K) (J : ℕ)
    (hL : L.coeff 0 = 1) : X^J ∣ L * localQuotient H L J-H := by
  have hmod := dvd_modByMonic_sub (H*inverseJet L J) (X^J)
  have hi := inverseJet_congruence L J hL
  have h := dvd_add (hmod.mul_left L) (hi.mul_left H)
  convert h using 1
  simp only [localQuotient]
  ring

theorem localQuotient_degree (H L : Polynomial K) (J : ℕ) (hJ : 0 < J) :
    (localQuotient H L J).natDegree < J := by
  have hne : (X : Polynomial K)^J ≠ 1 := by
    intro h
    have := congrArg natDegree h
    simp at this
    omega
  simpa [localQuotient] using natDegree_modByMonic_lt (H*inverseJet L J) (monic_X.pow J) hne

/-- Normalized Hermite cardinal factor, exactly the finite product used in code. -/
noncomputable def cardinalFactor (points : Finset K) (J : ℕ) (t : K) : Polynomial K :=
  by
    classical
    exact ∏ s ∈ points.erase t, ((X-C s)*C ((t-s)⁻¹))^J

theorem cardinalFactor_eval (points : Finset K) (J : ℕ) (t : K) :
    (cardinalFactor points J t).eval t = 1 := by
  classical
  unfold cardinalFactor
  rw [eval_prod]
  apply Finset.prod_eq_one
  intro s hs
  have hst : t-s ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hs))
  simp [hst]

theorem cardinalFactor_dvd (points : Finset K) (J : ℕ) (s t : K)
    (hs : s ∈ points) (hst : s ≠ t) : (X-C s)^J ∣ cardinalFactor points J t := by
  classical
  have hfactor : (X-C s)^J ∣ ((X-C s)*C ((t-s)⁻¹))^J :=
    pow_dvd_pow_of_dvd (dvd_mul_right _ _) J
  exact hfactor.trans (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hst, hs⟩))

theorem cardinalFactor_degree (points : Finset K) (J : ℕ) (t : K) (ht : t ∈ points) :
    (cardinalFactor points J t).natDegree ≤ (points.card-1) * J := by
  classical
  refine (natDegree_prod_le _ _).trans ?_
  calc
    ∑ s ∈ points.erase t, (((X-C s)*C ((t-s)⁻¹))^J).natDegree ≤ ∑ _s ∈ points.erase t, J := by
      apply Finset.sum_le_sum
      intro s hs
      exact natDegree_pow_le.trans (by
        have h := natDegree_mul_C_le (X-C s) ((t-s)⁻¹)
        simp only [natDegree_X_sub_C] at h
        simpa only [Nat.mul_comm, Nat.mul_one] using Nat.mul_le_mul_right J h)
    _ = _ := by rw [Finset.sum_const, Finset.card_erase_of_mem ht]; simp

/-- The explicit Hermite contribution of one node, using a constructed inverse. -/
noncomputable def hermiteTerm (points : Finset K) (J : ℕ) (H : Polynomial K) (t : K) : Polynomial K :=
  cardinalFactor points J t * taylor (-t)
    (localQuotient (taylor t H) (taylor t (cardinalFactor points J t)) J)

theorem hermiteTerm_local (points : Finset K) (J : ℕ) (H : Polynomial K) (t : K) :
    (X-C t)^J ∣ hermiteTerm points J H t-H := by
  rw [X_sub_C_pow_dvd_iff]
  change X^J ∣ taylor t (hermiteTerm points J H t-H)
  simp only [hermiteTerm, map_sub, taylor_mul, taylor_taylor, add_neg_cancel, taylor_zero]
  apply localQuotient_congruence
  rw [taylor_coeff_zero, cardinalFactor_eval]

theorem hermiteTerm_other (points : Finset K) (J : ℕ) (H : Polynomial K) (s t : K)
    (hs : s ∈ points) (hst : s ≠ t) : (X-C s)^J ∣ hermiteTerm points J H t :=
  (cardinalFactor_dvd points J s t hs hst).mul_right _

theorem hermiteTerm_degree (points : Finset K) (J : ℕ) (hJ : 0 < J)
    (H : Polynomial K) (t : K) (ht : t ∈ points) :
    (hermiteTerm points J H t).natDegree < points.card*J := by
  classical
  have h1 := cardinalFactor_degree points J t ht
  have h2 := localQuotient_degree (taylor t H) (taylor t (cardinalFactor points J t)) J hJ
  have h3 : (cardinalFactor points J t *
      taylor (-t) (localQuotient (taylor t H) (taylor t (cardinalFactor points J t)) J)).natDegree ≤
      (cardinalFactor points J t).natDegree +
      (taylor (-t) (localQuotient (taylor t H) (taylor t (cardinalFactor points J t)) J)).natDegree :=
    natDegree_mul_le
  rw [natDegree_taylor] at h3
  have hc : points.card-1+1 = points.card := Nat.sub_add_cancel (Finset.card_pos.mpr ⟨t, ht⟩)
  change _ < _
  dsimp only [hermiteTerm]
  nlinarith

/-- Full explicit finite Hermite reconstruction; the local inverse and its
congruence are constructed above, not assumed as matching Taylor packets. -/
theorem explicit_hermite_reconstruction (points : Finset K) (J : ℕ) (hJ : 0 < J)
    (H : Polynomial K) (hH : H.natDegree < points.card*J) :
    (∑ t ∈ points, hermiteTerm points J H t) = H := by
  classical
  apply eq_of_taylor_packets points J
  · refine (natDegree_sum_le _ _).trans_lt ?_
    apply (Finset.sup_lt_iff (by omega : 0 < points.card*J)).mpr
    intro t ht
    exact hermiteTerm_degree points J hJ H t ht
  · exact hH
  · intro t ht k hk
    have hdiv : (X-C t)^J ∣ (∑ s ∈ points, hermiteTerm points J H s)-H := by
      have hd : (X-C t)^J ∣ ∑ s ∈ points,
          (hermiteTerm points J H s - if s=t then H else 0) := by
        apply Finset.dvd_sum
        intro s hs
        by_cases hst : s=t
        · subst s
          simpa using hermiteTerm_local points J H t
        · simp only [hst, ↓reduceIte, sub_zero]
          exact hermiteTerm_other points J H t s ht (Ne.symm hst)
      simpa only [Finset.sum_sub_distrib, Finset.sum_ite_eq', ht, ↓reduceIte] using hd
    rw [X_sub_C_pow_dvd_iff, X_pow_dvd_iff] at hdiv
    have hzero := hdiv k hk
    simpa only [taylor_apply, sub_comp, coeff_sub, sub_eq_zero] using hzero

/-- Only the retained local packet is used by the inverse computation. -/
theorem localQuotient_truncate (H L : Polynomial K) (J : ℕ) :
    localQuotient (H %ₘ X^J) L J = localQuotient H L J := by
  unfold localQuotient
  apply modByMonic_eq_of_dvd_sub (monic_X.pow J)
  have h := (dvd_modByMonic_sub H (X^J)).mul_right (inverseJet L J)
  simpa only [sub_mul] using h

/-- Exact scalar formula implemented by hermite_at_zero. -/
theorem explicit_hermite_at_zero (points : Finset K) (J : ℕ) (hJ : 0 < J)
    (H : Polynomial K) (hH : H.natDegree < points.card*J) :
    H.eval 0 = ∑ t ∈ points, (cardinalFactor points J t).eval 0 *
      (localQuotient ((taylor t H) %ₘ X^J)
        (taylor t (cardinalFactor points J t)) J).eval (-t) := by
  have h := congrArg (fun p : Polynomial K => p.eval 0)
    (explicit_hermite_reconstruction points J hJ H hH)
  simp only [eval_finsetSum, hermiteTerm, eval_mul, taylor_eval, zero_add,
    localQuotient_truncate] at h ⊢
  exact h.symm

#print axioms localQuotient_truncate
#print axioms explicit_hermite_at_zero
#print axioms explicit_hermite_reconstruction
#print axioms inverseJet_congruence
#print axioms localQuotient_congruence
#print axioms localQuotient_degree
#print axioms cardinalFactor_eval
#print axioms zero_of_taylor_packets
#print axioms eq_of_taylor_packets
#print axioms samplePoints_card
#print axioms eq_of_counter_packets
#print axioms counter_precision_sufficient
end RiemannGaussian.SemiprimeHermiteRecovery
