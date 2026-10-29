/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetRecoveryWeights

/-! # Explicit indexed variable-multiplicity Hermite identity
The cardinal products and finite local inverse are constructed. Distinct nodes,
retained multiplicities and a polynomial degree bound imply the identity; no
matching reconstructed-jet or Hermite-correctness oracle is supplied.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1HermiteIdentity
open Polynomial
open scoped BigOperators
open SemiprimeHermiteRecovery
variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

/-- Actual total number of retained scalar coordinates. -/
def total (s : Finset ι) (m : ι→ℕ) : ℕ := ∑ t∈s,m t

omit [DecidableEq ι] in
/-- Variable-multiplicity jet vanishing forces zero at the exact actual degree cutoff. -/
theorem zero_of_packets (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (hinj : Set.InjOn node (s: Set ι)) (p : K[X]) (hp : p.natDegree<total s m)
    (hjets : ∀ t∈s,∀ k< m t,(taylor (node t) p).coeff k=0) : p=0 := by
  have hdiv : (∏ t∈s,(X-C (node t))^m t)∣p := by
    apply Finset.prod_dvd_of_coprime
    · intro a ha b hb hab
      have hn : node a≠node b := fun he => hab (hinj ha hb he)
      exact (pairwise_coprime_X_sub_C (s:=fun x:K => x) Function.injective_id hn).pow
    · intro t ht
      rw [X_sub_C_pow_dvd_iff,X_pow_dvd_iff]
      simpa only [taylor_apply] using hjets t ht
  have hdegree : (∏ t∈s,(X-C (node t))^m t).natDegree=total s m := by
    rw [natDegree_prod_of_monic s (fun t => (X-C (node t))^m t)
      (fun t _ => (monic_X_sub_C (node t)).pow (m t))]
    simp [total]
  by_contra hn
  have hle := natDegree_le_of_dvd hdiv hn
  rw [hdegree] at hle
  omega

omit [DecidableEq ι] in
/-- Actual finite packets uniquely determine the scalar polynomial. -/
theorem eq_of_packets (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (hinj : Set.InjOn node (s:Set ι)) (p q : K[X])
    (hp : p.natDegree<total s m) (hq : q.natDegree<total s m)
    (hjets : ∀ t∈s,∀ k< m t,(taylor (node t) p).coeff k=(taylor (node t) q).coeff k) : p=q := by
  apply sub_eq_zero.mp
  apply zero_of_packets s node m hinj (p-q) ((natDegree_sub_le p q).trans_lt (max_lt hp hq))
  intro t ht k hk
  simpa only [map_sub,coeff_sub,sub_eq_zero] using hjets t ht k hk

/-- Explicit variable-multiplicity cardinal factor, from the supplied distinct original nodes. -/
noncomputable def cardinal (s : Finset ι) (node : ι→K) (m : ι→ℕ) (t : ι) : K[X] :=
  ∏ q∈s.erase t,((X-C (node q))*C ((node t-node q)⁻¹))^m q

/-- Original normalization at its own node is exact1. -/
theorem cardinal_eval (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (hinj : Set.InjOn node (s:Set ι)) (t : ι) (ht : t∈s) :
    (cardinal s node m t).eval (node t)=1 := by
  rw [cardinal,eval_prod]
  apply Finset.prod_eq_one
  intro q hq
  have hqt : q≠t := (Finset.mem_erase.mp hq).1
  have hqn : node t-node q≠0 := sub_ne_zero.mpr (fun he => hqt (hinj (Finset.mem_of_mem_erase hq) ht he.symm))
  simp [hqn]

/-- Cardinal factor vanishes to the exact OTHER-node multiplicity. -/
theorem cardinal_dvd (s : Finset ι) (node : ι→K) (m : ι→ℕ) (t q : ι)
    (hq : q∈s) (hqt : q≠t) : (X-C (node q))^m q∣cardinal s node m t := by
  have h : (X-C (node q))^m q∣((X-C (node q))*C ((node t-node q)⁻¹))^m q :=
    pow_dvd_pow_of_dvd (dvd_mul_right _ _) (m q)
  exact h.trans (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hqt,hq⟩))

/-- Actual cardinal degree bound uses the sum of the OTHER retained multiplicities. -/
theorem cardinal_degree (s : Finset ι) (node : ι→K) (m : ι→ℕ) (t : ι) :
    (cardinal s node m t).natDegree≤∑ q∈s.erase t,m q := by
  refine (natDegree_prod_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro q _
  exact natDegree_pow_le.trans (by
    have h := natDegree_mul_C_le (X-C (node q)) ((node t-node q)⁻¹)
    simp only [natDegree_X_sub_C] at h
    simpa only [Nat.mul_comm,Nat.mul_one] using Nat.mul_le_mul_right (m q) h)

/-- Constructed local Hermite summand, with the actual finite inverse/truncation. -/
noncomputable def term (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (H : K[X]) (t : ι) : K[X] :=
  cardinal s node m t*taylor (-(node t))
    (localQuotient (taylor (node t) H) (taylor (node t) (cardinal s node m t)) (m t))

/-- The actual constructed term has the requested OWN-node jet. -/
theorem term_local (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (hinj : Set.InjOn node (s:Set ι)) (H : K[X]) (t : ι) (ht : t∈s) :
    (X-C (node t))^m t∣term s node m H t-H := by
  rw [X_sub_C_pow_dvd_iff]
  change X^m t∣taylor (node t) (term s node m H t-H)
  simp only [term,map_sub,taylor_mul,taylor_taylor,add_neg_cancel,taylor_zero]
  apply localQuotient_congruence
  rw [taylor_coeff_zero,cardinal_eval s node m hinj t ht]

/-- The actual constructed term has all required OTHER-node zeros. -/
theorem term_other (s : Finset ι) (node : ι→K) (m : ι→ℕ) (H : K[X]) (t q : ι)
    (hq : q∈s) (hqt : q≠t) : (X-C (node q))^m q∣term s node m H t :=
  (cardinal_dvd s node m t q hq hqt).mul_right _

/-- Constructed term has strictly smaller degree than the ACTUAL total multiplicity. -/
theorem term_degree (s : Finset ι) (node : ι→K) (m : ι→ℕ) (H : K[X]) (t : ι)
    (ht : t∈s) (hm : 0< m t) : (term s node m H t).natDegree<total s m := by
  have h1 := cardinal_degree s node m t
  have h2 := localQuotient_degree (taylor (node t) H) (taylor (node t) (cardinal s node m t)) (m t) hm
  have h3 : (term s node m H t).natDegree≤(cardinal s node m t).natDegree+
      (localQuotient (taylor (node t) H) (taylor (node t) (cardinal s node m t)) (m t)).natDegree := by
    unfold term
    exact natDegree_mul_le.trans (Nat.add_le_add_left (by rw [natDegree_taylor]) _)
  have he := Finset.sum_erase_add s m ht
  change _=total s m at he
  omega

/-- GLOBAL variable-multiplicity Hermite identity from the actual finite products
and inverse recurrence, without an assumed reconstructed-jets equality. -/
theorem reconstruction (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (hinj : Set.InjOn node (s:Set ι)) (hm : ∀t∈s,0< m t) (H : K[X])
    (hH : H.natDegree<total s m) : (∑ t∈s,term s node m H t)=H := by
  apply eq_of_packets s node m hinj
  · refine (natDegree_sum_le _ _).trans_lt ?_
    apply (Finset.sup_lt_iff (by omega : 0<total s m)).mpr
    intro t ht
    exact term_degree s node m H t ht (hm t ht)
  · exact hH
  · intro t ht k hk
    have hdiv : (X-C (node t))^m t∣(∑ q∈s,term s node m H q)-H := by
      have hd : (X-C (node t))^m t∣∑ q∈s,(term s node m H q-if q=t then H else 0) := by
        apply Finset.dvd_sum
        intro q hq
        by_cases hqt : q=t
        · subst q
          simpa using term_local s node m hinj H t ht
        · simp only [hqt,ite_false,sub_zero]
          exact term_other s node m H q t ht (Ne.symm hqt)
      simpa only [Finset.sum_sub_distrib,Finset.sum_ite_eq',ht,ite_true] using hd
    rw [X_sub_C_pow_dvd_iff,X_pow_dvd_iff] at hdiv
    have hz := hdiv k hk
    simpa only [taylor_apply,sub_comp,coeff_sub,sub_eq_zero] using hz

/-- Exact global scalar linear-combination formula at zero, using only retained jets. -/
theorem at_zero (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (hinj : Set.InjOn node (s:Set ι)) (hm : ∀t∈s,0< m t) (H : K[X])
    (hH : H.natDegree<total s m) :
    H.eval 0=∑ t∈s,(cardinal s node m t).eval 0*
      (localQuotient ((taylor (node t) H)%ₘ X^m t)
        (taylor (node t) (cardinal s node m t)) (m t)).eval (-(node t)) := by
  have he := congrArg (fun p:K[X] => p.eval 0) (reconstruction s node m hinj hm H hH)
  simp only [eval_finsetSum,term,eval_mul,taylor_eval,zero_add,localQuotient_truncate] at he ⊢
  exact he.symm

/-- Finite FREE coefficient vectors recover coordinatewise from the actual scalar identity.
No ring evaluation map on a nilpotent quotient is invoked. -/
theorem coordinates_at_zero (s : Finset ι) (node : ι→ℚ) (m : ι→ℕ)
    (hinj : Set.InjOn node (s:Set ι)) (hm : ∀t∈s,0< m t)
    (c : ℕ) (H : Fin c→ℚ[X]) (hH : ∀j,(H j).natDegree<total s m) :
    (fun j => (H j).eval 0)=fun j => ∑ t∈s,(cardinal s node m t).eval 0*
      (localQuotient ((taylor (node t) (H j))%ₘ X^m t)
        (taylor (node t) (cardinal s node m t)) (m t)).eval (-(node t)) := by
  funext j
  exact at_zero s node m hinj hm (H j) (hH j)

end RiemannGaussian.SemiprimeD1HermiteIdentity
