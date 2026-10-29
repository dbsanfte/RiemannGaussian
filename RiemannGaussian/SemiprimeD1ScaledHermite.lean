/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HermiteIdentity

/-! # Exact scaled variable-multiplicity Hermite recovery from retained jets
All substitution occurs on scalar rational polynomials, followed by a scalar
linear coefficient functional. This is not a ring evaluation on a jet quotient.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1ScaledHermite
open Polynomial
open scoped BigOperators
open SemiprimeHermiteRecovery SemiprimeD1HermiteIdentity
variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

/-- Original local affine parameter T=t+alpha*z. -/
noncomputable def affine (α t : K) : K[X] := C t+C α*X

/-- Scalar polynomial inverse parameter z=(T-t)/alpha. -/
noncomputable def pullback (α t : K) : K[X] := (X-C t)*C α⁻¹

/-- The ORIGINAL affine parameter changes are inverse over the scalar field. -/
theorem affine_pullback (α t : K) (hα : α≠0) : (affine α t).comp (pullback α t)=X := by
  simp only [affine,pullback,add_comp,C_comp,mul_comp,X_comp]
  have hi : C α*C α⁻¹=(1:K[X]) := by rw [← C_mul,mul_inv_cancel₀ hα,C_1]
  calc
    _ = C t+(C α*C α⁻¹)*(X-C t) := by ring
    _ = X := by rw [hi,one_mul];ring

/-- The actual scaled local Hermite quotient uses its constructed finite inverse. -/
noncomputable def quotient (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (α : K) (H : K[X]) (t : ι) : K[X] :=
  localQuotient (H.comp (affine α (node t)))
    ((cardinal s node m t).comp (affine α (node t))) (m t)

/-- Constructed scaled Hermite term in the ORIGINAL T variable. -/
noncomputable def term (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (α : K) (H : K[X]) (t : ι) : K[X] :=
  cardinal s node m t*(quotient s node m α H t).comp (pullback α (node t))

/-- Own-node agreement is DERIVED from the finite local inverse and affine composition. -/
theorem term_local (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (hinj : Set.InjOn node (s:Set ι)) (α : K) (hα : α≠0) (H : K[X]) (t : ι) (ht : t∈s) :
    (X-C (node t))^m t∣term s node m α H t-H := by
  have hL : ((cardinal s node m t).comp (affine α (node t))).coeff 0=1 := by
    rw [coeff_zero_eq_eval_zero,eval_comp]
    simpa [affine] using cardinal_eval s node m hinj t ht
  have hlocal := localQuotient_congruence (H.comp (affine α (node t)))
    ((cardinal s node m t).comp (affine α (node t))) (m t) hL
  have hd := map_dvd (compRingHom (pullback α (node t))) hlocal
  change (X^m t).comp (pullback α (node t))∣
    (((cardinal s node m t).comp (affine α (node t)))*quotient s node m α H t-
      H.comp (affine α (node t))).comp (pullback α (node t)) at hd
  simp only [pow_comp,X_comp,sub_comp,mul_comp,comp_assoc,affine_pullback α (node t) hα,comp_X] at hd
  have hbase : (X-C (node t))^m t∣(pullback α (node t))^m t :=
    pow_dvd_pow_of_dvd (dvd_mul_right _ _) _
  exact hbase.trans hd

/-- Other-node vanishing uses only the explicit cardinal factor. -/
theorem term_other (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (α : K) (H : K[X]) (t q : ι) (hq : q∈s) (hqt : q≠t) :
    (X-C (node q))^m q∣term s node m α H t :=
  (cardinal_dvd s node m t q hq hqt).mul_right _

/-- Actual term degree is strictly below total retained multiplicity. -/
theorem term_degree (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (α : K) (H : K[X]) (t : ι) (ht : t∈s) (hm : 0< m t) :
    (term s node m α H t).natDegree<total s m := by
  have h1 := cardinal_degree s node m t
  have h2 := localQuotient_degree (H.comp (affine α (node t)))
    ((cardinal s node m t).comp (affine α (node t))) (m t) hm
  have hp : (pullback α (node t)).natDegree≤1 := by
    exact (natDegree_mul_C_le (X-C (node t)) α⁻¹).trans_eq (natDegree_X_sub_C (node t))
  have hc : ((quotient s node m α H t).comp (pullback α (node t))).natDegree≤
      (quotient s node m α H t).natDegree := by
    exact natDegree_comp_le.trans (by simpa only [Nat.mul_one] using
      (Nat.mul_le_mul_left ((quotient s node m α H t).natDegree) hp))
  have h3 : (term s node m α H t).natDegree≤(cardinal s node m t).natDegree+
      (quotient s node m α H t).natDegree := natDegree_mul_le.trans (Nat.add_le_add_left hc _)
  have he := Finset.sum_erase_add s m ht
  change _=total s m at he
  change (quotient s node m α H t).natDegree< m t at h2
  omega

/-- Scaled GLOBAL Hermite identity, from actual variable multiplicities and finite inverse. -/
theorem reconstruction (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (hinj : Set.InjOn node (s:Set ι)) (hm : ∀t∈s,0< m t)
    (α : K) (hα : α≠0) (H : K[X]) (hH : H.natDegree<total s m) :
    (∑ t∈s,term s node m α H t)=H := by
  apply eq_of_packets s node m hinj
  · refine (natDegree_sum_le _ _).trans_lt ?_
    apply (Finset.sup_lt_iff (by omega : 0<total s m)).mpr
    intro t ht
    exact term_degree s node m α H t ht (hm t ht)
  · exact hH
  · intro t ht k hk
    have hd : (X-C (node t))^m t∣∑ q∈s,(term s node m α H q-if q=t then H else 0) := by
      apply Finset.dvd_sum
      intro q hq
      by_cases hqt : q=t
      · subst q
        simpa using term_local s node m hinj α hα H t ht
      · simp only [hqt,ite_false,sub_zero]
        exact term_other s node m α H q t ht (Ne.symm hqt)
    have he : (X-C (node t))^m t∣(∑ q∈s,term s node m α H q)-H := by
      simpa only [Finset.sum_sub_distrib,Finset.sum_ite_eq',ht,ite_true] using hd
    rw [X_sub_C_pow_dvd_iff,X_pow_dvd_iff] at he
    simpa only [taylor_apply,sub_comp,coeff_sub,sub_eq_zero] using he k hk

/-- EXACT D.9 at zero, using ONLY the actual retained SCALED Taylor packets. -/
theorem at_zero (s : Finset ι) (node : ι→K) (m : ι→ℕ)
    (hinj : Set.InjOn node (s:Set ι)) (hm : ∀t∈s,0< m t)
    (α : K) (hα : α≠0) (H : K[X]) (hH : H.natDegree<total s m) :
    H.eval 0=∑ t∈s,(cardinal s node m t).eval 0*
      (localQuotient ((H.comp (affine α (node t)))%ₘ X^m t)
        ((cardinal s node m t).comp (affine α (node t))) (m t)).eval (-(node t)/α) := by
  have he := congrArg (fun p:K[X] => p.eval 0) (reconstruction s node m hinj hm α hα H hH)
  simp only [eval_finsetSum,term,eval_mul,eval_comp,pullback,eval_mul,eval_sub,eval_X,eval_C,
    zero_sub,quotient,localQuotient_truncate,div_eq_mul_inv] at he ⊢
  exact he.symm

end RiemannGaussian.SemiprimeD1ScaledHermite
