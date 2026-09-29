/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAllocationConcentration
import RiemannGaussian.ZetaRieszBalancedCompanion
import RiemannGaussian.ZetaRieszMarkedSaturation
import Mathlib.Analysis.SpecialFunctions.Bernstein
/-!
# Variation of the literal factorial allocation

Binomial variance controls the radial derivative before phase cancellation.
The estimates include every selected order and do not require the allocated
fraction to tend to zero.
-/
open scoped BigOperators Classical
open RiemannGaussian.ZetaRieszJointAllocation
namespace RiemannGaussian.ZetaRieszAllocationVariation
noncomputable section

/-- Exact variance of the full factorial allocation. -/
theorem mass_variance (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (n+1), ((n : ℝ)*x-k)^2*mass n k x) = (n : ℝ)*x*(1-x) := by
  have h := congrArg (Polynomial.eval x) (bernsteinPolynomial.variance ℝ n)
  simpa [Polynomial.eval_finsetSum,bernsteinPolynomial,mass,mul_assoc,mul_comm,mul_left_comm] using h

/-- Any fixed order selection has score bounded by the full variance. -/
theorem selected_score_sq_le (n : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range (n+1))
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    (∑ k ∈ S, mass n k x*((k : ℝ)-n*x))^2 ≤ (n : ℝ)*x*(1-x) := by
  have hm (k : ℕ) := mass_nonneg n k hx hx1
  have hprob : (∑ k ∈ S, mass n k x) ≤ 1 :=
    (Finset.sum_le_sum_of_subset_of_nonneg hS (fun k _ _ => hm k)).trans_eq (mass_total n x)
  have hvar : (∑ k ∈ S, mass n k x*((k : ℝ)-n*x)^2) ≤ (n : ℝ)*x*(1-x) := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg hS
      (f := fun k => ((n : ℝ)*x-k)^2*mass n k x) (fun k _ _ => mul_nonneg (sq_nonneg _) (hm k))
    rw [mass_variance] at h
    calc
      _ = ∑ k ∈ S, ((n : ℝ)*x-k)^2*mass n k x :=
        Finset.sum_congr rfl (fun k _ => by ring)
      _ ≤ _ := h
  have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun k => Real.sqrt (mass n k x))
    (fun k => Real.sqrt (mass n k x)*((k : ℝ)-n*x))
  have he (k : ℕ) : Real.sqrt (mass n k x)*(Real.sqrt (mass n k x)*((k : ℝ)-n*x)) =
      mass n k x*((k : ℝ)-n*x) := by rw [← mul_assoc,← pow_two,Real.sq_sqrt (hm k)]
  simp_rw [he,mul_pow,Real.sq_sqrt (hm _)] at hc
  apply hc.trans
  have hs0 : 0 ≤ ∑ k ∈ S, mass n k x*((k : ℝ)-n*x)^2 :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hm k) (sq_nonneg _))
  exact (mul_le_mul_of_nonneg_right hprob hs0).trans (by simpa only [one_mul] using hvar)

private theorem mul_pow_pred (a : ℝ) (k : ℕ) :
    (k : ℝ)*a^(k-1)*a = (k : ℝ)*a^k := by
  cases k with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel,pow_succ]; ring

/-- The literal binomial mass has this exact score derivative. -/
theorem hasDerivAt_mass {n k : ℕ} (hk : k ≤ n) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (mass n k) (mass n k x*((k : ℝ)-n*x)/(x*(1-x))) x := by
  have hd := (((hasDerivAt_id x).pow k).mul
    (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).pow (n-k))).mul_const (n.choose k : ℝ)
  apply hd.congr_deriv
  simp only [Pi.pow_apply,Pi.sub_apply,id_eq,mul_one,zero_sub]
  apply (eq_div_iff (mul_ne_zero hx.ne' (by linarith : (1-x : ℝ) ≠ 0))).mpr
  dsimp only [mass]
  have hp := mul_pow_pred x k
  have hq := mul_pow_pred (1-x) (n-k)
  rw [Nat.cast_sub hk] at hq ⊢
  linear_combination (n.choose k : ℝ)*(1-x)^(n-k)*(1-x)*hp-
    (n.choose k : ℝ)*x^k*x*hq


/-- Differentiate the selected factorial orders without deleting any atoms. -/
theorem hasDerivAt_selected_mass (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (fun t => ∑ k ∈ S, mass n k t)
      ((∑ k ∈ S, mass n k x*((k : ℝ)-n*x))/(x*(1-x))) x := by
  have h := HasDerivAt.sum (fun k hk =>
    hasDerivAt_mass (Nat.lt_succ_iff.mp (Finset.mem_range.mp (hS hk))) hx hx1)
  have he : (∑ k ∈ S, mass n k) = (fun t => ∑ k ∈ S, mass n k t) := by
    ext t
    simp only [Finset.sum_apply]
  rw [he] at h
  simpa only [← Finset.sum_div] using h

/-- The selected mass derivative obeys the binomial variance bound. -/
theorem selected_derivative_sq_le (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ((∑ k ∈ S, mass n k x*((k : ℝ)-n*x))/(x*(1-x)))^2 ≤
      (n : ℝ)/(x*(1-x)) := by
  have hd : 0 < x*(1-x) := mul_pos hx (by linarith)
  rw [div_pow]
  apply (div_le_iff₀ (sq_pos_of_pos hd)).mpr
  have h := selected_score_sq_le n S hS hx.le hx1.le
  apply h.trans_eq
  field_simp


/-- A cofactor log share changes slowly along a radial prime period. -/
theorem radial_derivative_bound (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {b T : ℝ} (hb : 0 < b) (hT : 0 < T)
    (hbT : b ≤ (3/4 : ℝ)*T) :
    ∃ D : ℝ, HasDerivAt (fun t => ∑ k ∈ S, mass n k (b/t)) D T ∧
      |D| ≤ 2*Real.sqrt n/T := by
  let x := b/T
  have hx : 0 < x := div_pos hb hT
  have hxU : x ≤ 3/4 := (div_le_iff₀ hT).mpr hbT
  have hx1 : x < 1 := by linarith
  have hy : 0 < 1-x := by linarith
  let score := ∑ k ∈ S, mass n k x*((k : ℝ)-n*x)
  let D := score/(x*(1-x))*(-b/T^2)
  have hr := ((hasDerivAt_const T b).div (hasDerivAt_id T) hT.ne')
  simp only [zero_mul,mul_one,zero_sub] at hr
  have hd := (hasDerivAt_selected_mass n S hS hx hx1).comp T hr
  refine ⟨D,hd,?_⟩
  have hscore : score^2 ≤ (n : ℝ)*x*(1-x) := selected_score_sq_le n S hS hx.le hx1.le
  have hratio : score^2 ≤ 3*(n : ℝ)*(1-x)^2 := by
    have hh := mul_le_mul_of_nonneg_right (show x ≤ 3*(1-x) by linarith)
      (show 0 ≤ (n : ℝ)*(1-x) by positivity)
    nlinarith only [hscore,hh]
  have he : D*T = -score/(1-x) := by
    dsimp only [D,x]
    field_simp
  have hsq : (D*T)^2 ≤ 3*(n : ℝ) := by
    rw [he,div_pow,neg_sq]
    exact (div_le_iff₀ (sq_pos_of_pos hy)).mpr hratio
  have habs : |D*T| ≤ 2*Real.sqrt n := by
    nlinarith [sq_abs (D*T),Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n),
      Real.sqrt_nonneg (n : ℝ),abs_nonneg (D*T)]
  apply (le_div_iff₀ hT).mpr
  simpa only [abs_mul,abs_of_pos hT] using habs

/-- The complementary share has the same uniform radial derivative bound. -/
theorem complementary_radial_derivative_bound (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {b T : ℝ} (hb : 0 < b) (hT : 0 < T)
    (hbT : b ≤ (3/4 : ℝ)*T) :
    ∃ D : ℝ, HasDerivAt (fun t => ∑ k ∈ S, mass n k (1-b/t)) D T ∧
      |D| ≤ 2*Real.sqrt n/T := by
  let x := 1-b/T
  have hxL : 1/4 ≤ x := by dsimp [x]; linarith [(div_le_iff₀ hT).mpr hbT]
  have hx : 0 < x := by linarith
  have hx1 : x < 1 := by dsimp [x]; linarith [div_pos hb hT]
  let score := ∑ k ∈ S, mass n k x*((k : ℝ)-n*x)
  let D := score/(x*(1-x))*(b/T^2)
  have hr := (hasDerivAt_const T (1 : ℝ)).sub
    ((hasDerivAt_const T b).div (hasDerivAt_id T) hT.ne')
  simp only [zero_mul,mul_one,zero_sub,neg_div,neg_neg,id_eq] at hr
  have hd := (hasDerivAt_selected_mass n S hS hx hx1).comp T hr
  refine ⟨D,hd,?_⟩
  have hscore : score^2 ≤ (n : ℝ)*x*(1-x) := selected_score_sq_le n S hS hx.le hx1.le
  have hratio : score^2 ≤ 3*(n : ℝ)*x^2 := by
    have hh := mul_le_mul_of_nonneg_right (show 1-x ≤ 3*x by linarith)
      (show 0 ≤ (n : ℝ)*x by positivity)
    nlinarith only [hscore,hh]
  have he : D*T = score/x := by
    dsimp only [D,x]
    field_simp
    rw [sub_sub_cancel]
    field_simp
  have hsq : (D*T)^2 ≤ 3*(n : ℝ) := by
    rw [he,div_pow]
    exact (div_le_iff₀ (sq_pos_of_pos hx)).mpr hratio
  have habs : |D*T| ≤ 2*Real.sqrt n := by
    nlinarith [sq_abs (D*T),Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n),
      Real.sqrt_nonneg (n : ℝ),abs_nonneg (D*T)]
  apply (le_div_iff₀ hT).mpr
  simpa only [abs_mul,abs_of_pos hT] using habs

private theorem radial_lipschitz (n : ℕ) (f : ℝ → ℝ) {b v δ T U : ℝ}
    (_hb : 0 < b) (hv : 100 ≤ v) (_hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hbv : b ≤ (7/10 : ℝ)*v)
    (hT : T ∈ Set.Icc (v-δ) (v+δ)) (hU : U ∈ Set.Icc (v-δ) (v+δ))
    (hd : ∀ t, 0 < t → b ≤ (3/4 : ℝ)*t →
      ∃ D, HasDerivAt f D t ∧ |D| ≤ 2*Real.sqrt n/t) :
    |f T-f U| ≤ (4*Real.sqrt n/v)*|T-U| := by
  have hder (t : ℝ) (ht : t ∈ Set.Icc (v-δ) (v+δ)) :
      HasDerivAt f (deriv f t) t ∧ ‖deriv f t‖ ≤ 4*Real.sqrt n/v := by
    have ht0 : 0 < t := by linarith [ht.1]
    obtain ⟨D,hD,hDb⟩ := hd t ht0 (by linarith [ht.1])
    refine ⟨hD.deriv ▸ hD,?_⟩
    rw [hD.deriv,Real.norm_eq_abs]
    apply hDb.trans
    apply (div_le_div_iff₀ ht0 (by linarith : 0 < v)).mpr
    have hh := mul_le_mul_of_nonneg_left (show v ≤ 2*t by linarith [ht.1])
      (show 0 ≤ 2*Real.sqrt n by positivity)
    nlinarith only [hh]
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hder t ht).1.hasDerivWithinAt) (fun t ht => (hder t ht).2)
      (convex_Icc (v-δ) (v+δ)) hU hT

/-- The original selected orders vary by at most a square-root radial cost. -/
theorem selected_mass_radial_lipschitz (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {b v δ T U : ℝ}
    (hb : 0 < b) (hv : 100 ≤ v) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hbv : b ≤ (133/200 : ℝ)*v)
    (hT : T ∈ Set.Icc (v-δ) (v+δ)) (hU : U ∈ Set.Icc (v-δ) (v+δ)) :
    |(∑ k ∈ S, mass n k (b/T))-(∑ k ∈ S, mass n k (b/U))| ≤
      (4*Real.sqrt n/v)*|T-U| :=
  radial_lipschitz n _ hb hv hδ hδu (by linarith) hT hU
    (fun _ ht hbt => radial_derivative_bound n S hS hb ht hbt)

/-- This controls fixed cofactor-prime incidences, including small primes. -/
theorem complementary_mass_radial_lipschitz (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {b v δ T U : ℝ}
    (hb : 0 < b) (hv : 100 ≤ v) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hbv : b ≤ (133/200 : ℝ)*v)
    (hT : T ∈ Set.Icc (v-δ) (v+δ)) (hU : U ∈ Set.Icc (v-δ) (v+δ)) :
    |(∑ k ∈ S, mass n k (1-b/T))-(∑ k ∈ S, mass n k (1-b/U))| ≤
      (4*Real.sqrt n/v)*|T-U| :=
  radial_lipschitz n _ hb hv hδ hδu (by linarith) hT hU
    (fun _ ht hbt => complementary_radial_derivative_bound n S hS hb ht hbt)

/-- The same selected-order variation remains valid through the unsaturated cofactor band. -/
theorem selected_mass_radial_lipschitz_wide (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {b v δ T U : ℝ}
    (hb : 0 < b) (hv : 100 ≤ v) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hbv : b ≤ (7/10 : ℝ)*v)
    (hT : T ∈ Set.Icc (v-δ) (v+δ)) (hU : U ∈ Set.Icc (v-δ) (v+δ)) :
    |(∑ k ∈ S, mass n k (b/T))-(∑ k ∈ S, mass n k (b/U))| ≤
      (4*Real.sqrt n/v)*|T-U| :=
  radial_lipschitz n _ hb hv hδ hδu (by linarith) hT hU
    (fun _ ht hbt => radial_derivative_bound n S hS hb ht hbt)

/-- The complementary incidence bound also covers the wider cofactor band. -/
theorem complementary_mass_radial_lipschitz_wide (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {b v δ T U : ℝ}
    (hb : 0 < b) (hv : 100 ≤ v) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hbv : b ≤ (7/10 : ℝ)*v)
    (hT : T ∈ Set.Icc (v-δ) (v+δ)) (hU : U ∈ Set.Icc (v-δ) (v+δ)) :
    |(∑ k ∈ S, mass n k (1-b/T))-(∑ k ∈ S, mass n k (1-b/U))| ≤
      (4*Real.sqrt n/v)*|T-U| :=
  radial_lipschitz n _ hb hv hδ hδu (by linarith) hT hU
    (fun _ ht hbt => complementary_radial_derivative_bound n S hS hb ht hbt)

/-- Exact allocation along a prime fibre, with the eligible-prime mask retained. -/
theorem boundedShare_prime_fibre (A : Finset ℕ) (N : ℕ) {a p : ℕ}
    (ha : Squarefree a) (hc : 2 ≤ a.primeFactors.card) (hp : p.Prime)
    (hpd : ¬p ∣ a) (hpA : p ∈ A) :
    boundedShare A N (p*a) =
      (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
        mass (N+1) k (Real.log a/Real.log (p*a : ℕ)))+
      ∑ q ∈ a.primeFactors.filter (· ∈ A),
        ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
          mass (N+1) k (1-Real.log q/Real.log (p*a : ℕ)) := by
  have hsf := Nat.squarefree_mul_iff.mpr ⟨hp.coprime_iff_not_dvd.mpr hpd,hp.squarefree,ha⟩
  have hpm : p ∉ a.primeFactors := fun h => hpd (Nat.dvd_of_mem_primeFactors h)
  have hpf : (p*a).primeFactors = insert p a.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero ha.ne_zero,hp.primeFactors,Finset.singleton_union]
  have hcount : 3 ≤ (p*a).primeFactors.card := by
    rw [hpf,Finset.card_insert_of_notMem hpm]; omega
  have hne : p*a ≠ 1 := by intro h; simp [h] at hcount
  have hn1 : 1 < p*a := by have := hsf.ne_zero; omega
  have hnp : ¬(p*a).Prime := by intro h; simp [h.primeFactors] at hcount
  have hl : 0 < Real.log (p*a : ℕ) := Real.log_pos (by exact_mod_cast hn1)
  have hel (q : ℕ) (hq : q ∈ (p*a).primeFactors) : eligibleCofactor q (p*a/q) :=
    ZetaRieszMarkedSaturation.cofactor_data hsf hcount hq
  rw [boundedShare,if_pos ⟨hsf,hn1,hnp⟩,
    ZetaRieszBalancedCompanion.share_eq_binomial_sum A N hsf hn1]
  have he : (∑ q ∈ (p*a).primeFactors,
      if q ∈ A ∧ eligibleCofactor q (p*a/q) then
        ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
          mass (N+1) k (Real.log (p*a/q : ℕ)/Real.log (p*a : ℕ)) else 0) =
      ∑ q ∈ (p*a).primeFactors, if q ∈ A then
        ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
          mass (N+1) k (Real.log (p*a/q : ℕ)/Real.log (p*a : ℕ)) else 0 := by
    apply Finset.sum_congr rfl
    intro q hq
    simp only [hel q hq,and_true]
  rw [he,hpf,Finset.sum_insert hpm,if_pos hpA,Nat.mul_div_cancel_left a hp.pos]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with hqA
  · have hqp := Nat.prime_of_mem_primeFactors hq
    have hd : q ∣ p*a := dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hq) p
    have hlog : Real.log (p*a/q : ℕ) = Real.log (p*a : ℕ)-Real.log q := by
      rw [Nat.cast_div hd (by exact_mod_cast hqp.ne_zero),
        Real.log_div (by exact_mod_cast hsf.ne_zero) (by exact_mod_cast hqp.ne_zero)]
    rw [hlog,sub_div,div_self hl.ne']
  · rfl

/-- Actual six-prime allocation varies slowly even across its transition.
Only the moving owner must remain in the literal eligible-prime set. -/
theorem boundedShare_fibre_variation (A : Finset ℕ) (N : ℕ) {a p q : ℕ}
    (ha : Squarefree a) (hc : a.primeFactors.card = 5)
    (hp : p.Prime) (hpd : ¬p ∣ a) (hpA : p ∈ A)
    (hq : q.Prime) (hqd : ¬q ∣ a) (hqA : q ∈ A)
    {v δ : ℝ} (hv : 100 ≤ v) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hav : Real.log a ≤ (133/200 : ℝ)*v)
    (hpT : Real.log (p*a : ℕ) ∈ Set.Icc (v-δ) (v+δ))
    (hqT : Real.log (q*a : ℕ) ∈ Set.Icc (v-δ) (v+δ)) :
    |boundedShare A N (p*a)-boundedShare A N (q*a)| ≤
      (24*Real.sqrt (N+1)/v)*|Real.log (p*a : ℕ)-Real.log (q*a : ℕ)| := by
  have ha1 : 1 < a := by
    have hne : a ≠ 1 := by intro h; simp [h] at hc
    have := ha.ne_zero
    omega
  have hlog : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha1)
  have hS : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1+1) := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  rw [boundedShare_prime_fibre A N ha (by omega) hp hpd hpA,
    boundedShare_prime_fibre A N ha (by omega) hq hqd hqA]
  have hfirst := selected_mass_radial_lipschitz (N+1) _ hS hlog hv hδ hδu hav hpT hqT
  simp only [Nat.cast_add,Nat.cast_one] at hfirst
  let B := (4*Real.sqrt (N+1)/v)*|Real.log (p*a : ℕ)-Real.log (q*a : ℕ)|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hrow (r : ℕ) (hr : r ∈ a.primeFactors.filter (· ∈ A)) :
      |(∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
        mass (N+1) k (1-Real.log r/Real.log (p*a : ℕ)))-
       (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
        mass (N+1) k (1-Real.log r/Real.log (q*a : ℕ)))| ≤ B := by
    have hrp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1
    have hrdiv := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hr).1
    have hrlog : Real.log r ≤ Real.log a := Real.log_le_log
      (by exact_mod_cast hrp.pos) (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero ha.ne_zero) hrdiv)
    simpa only [B,Nat.cast_add,Nat.cast_one] using complementary_mass_radial_lipschitz (N+1) _ hS
      (Real.log_pos (by exact_mod_cast hrp.one_lt)) hv hδ hδu (hrlog.trans hav) hpT hqT
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hrow)
  rw [Finset.sum_const,nsmul_eq_mul] at hsum
  have hcard : ((a.primeFactors.filter (· ∈ A)).card : ℝ) ≤ 5 := by
    exact_mod_cast (Finset.card_filter_le _ _).trans_eq hc
  have hsum5 := hsum.trans (mul_le_mul_of_nonneg_right hcard hB)
  rw [Finset.sum_sub_distrib] at hsum5
  have hab := abs_add_le
    ((∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k (Real.log a/Real.log (p*a : ℕ)))-
      ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k (Real.log a/Real.log (q*a : ℕ)))
    ((∑ r ∈ a.primeFactors.filter (· ∈ A), ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      mass (N+1) k (1-Real.log r/Real.log (p*a : ℕ)))-
      ∑ r ∈ a.primeFactors.filter (· ∈ A), ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      mass (N+1) k (1-Real.log r/Real.log (q*a : ℕ)))
  dsimp only [B] at hsum5
  convert (hab.trans (add_le_add hfirst hsum5)) using 1 <;> congr 1 <;> ring

/-- Any fixed prime-count sector has the same allocation-variation mechanism.
The explicit factor is four times the total number of prime legs. -/
theorem boundedShare_fibre_variation_of_count (A : Finset ℕ) (N : ℕ) {a p q : ℕ}
    (ha : Squarefree a) (hc : 2 ≤ a.primeFactors.card)
    (hp : p.Prime) (hpd : ¬p ∣ a) (hpA : p ∈ A)
    (hq : q.Prime) (hqd : ¬q ∣ a) (hqA : q ∈ A)
    {v δ : ℝ} (hv : 100 ≤ v) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hav : Real.log a ≤ (7/10 : ℝ)*v)
    (hpT : Real.log (p*a : ℕ) ∈ Set.Icc (v-δ) (v+δ))
    (hqT : Real.log (q*a : ℕ) ∈ Set.Icc (v-δ) (v+δ)) :
    |boundedShare A N (p*a)-boundedShare A N (q*a)| ≤
      (4*((a.primeFactors.card : ℝ)+1)*Real.sqrt (N+1)/v)*|Real.log (p*a : ℕ)-Real.log (q*a : ℕ)| := by
  have ha1 : 1 < a := by
    have hne : a ≠ 1 := by intro h; simp [h] at hc
    have := ha.ne_zero
    omega
  have hlog : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha1)
  have hS : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1+1) := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  rw [boundedShare_prime_fibre A N ha (by omega) hp hpd hpA,
    boundedShare_prime_fibre A N ha (by omega) hq hqd hqA]
  have hfirst := selected_mass_radial_lipschitz_wide (N+1) _ hS hlog hv hδ hδu hav hpT hqT
  simp only [Nat.cast_add,Nat.cast_one] at hfirst
  let B := (4*Real.sqrt (N+1)/v)*|Real.log (p*a : ℕ)-Real.log (q*a : ℕ)|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hrow (r : ℕ) (hr : r ∈ a.primeFactors.filter (· ∈ A)) :
      |(∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
        mass (N+1) k (1-Real.log r/Real.log (p*a : ℕ)))-
       (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
        mass (N+1) k (1-Real.log r/Real.log (q*a : ℕ)))| ≤ B := by
    have hrp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1
    have hrdiv := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hr).1
    have hrlog : Real.log r ≤ Real.log a := Real.log_le_log
      (by exact_mod_cast hrp.pos) (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero ha.ne_zero) hrdiv)
    simpa only [B,Nat.cast_add,Nat.cast_one] using complementary_mass_radial_lipschitz_wide (N+1) _ hS
      (Real.log_pos (by exact_mod_cast hrp.one_lt)) hv hδ hδu (hrlog.trans hav) hpT hqT
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hrow)
  rw [Finset.sum_const,nsmul_eq_mul] at hsum
  have hcard : ((a.primeFactors.filter (· ∈ A)).card : ℝ) ≤ a.primeFactors.card := by
    exact_mod_cast Finset.card_filter_le a.primeFactors (· ∈ A)
  have hsum5 := hsum.trans (mul_le_mul_of_nonneg_right hcard hB)
  rw [Finset.sum_sub_distrib] at hsum5
  have hab := abs_add_le
    ((∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k (Real.log a/Real.log (p*a : ℕ)))-
      ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k (Real.log a/Real.log (q*a : ℕ)))
    ((∑ r ∈ a.primeFactors.filter (· ∈ A), ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      mass (N+1) k (1-Real.log r/Real.log (p*a : ℕ)))-
      ∑ r ∈ a.primeFactors.filter (· ∈ A), ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      mass (N+1) k (1-Real.log r/Real.log (q*a : ℕ)))
  dsimp only [B] at hsum5
  convert (hab.trans (add_le_add hfirst hsum5)) using 1 <;> congr 1 <;> ring

/-- A cofactor log share changes slowly along a radial prime period. -/
theorem radial_derivative_bound_99 (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {b T : ℝ} (hb : 0 < b) (hT : 0 < T)
    (hbT : b ≤ (99/100 : ℝ)*T) :
    ∃ D : ℝ, HasDerivAt (fun t => ∑ k ∈ S, mass n k (b/t)) D T ∧
      |D| ≤ 10*Real.sqrt n/T := by
  let x := b/T
  have hx : 0 < x := div_pos hb hT
  have hxU : x ≤ 99/100 := (div_le_iff₀ hT).mpr hbT
  have hx1 : x < 1 := by linarith
  have hy : 0 < 1-x := by linarith
  let score := ∑ k ∈ S, mass n k x*((k : ℝ)-n*x)
  let D := score/(x*(1-x))*(-b/T^2)
  have hr := ((hasDerivAt_const T b).div (hasDerivAt_id T) hT.ne')
  simp only [zero_mul,mul_one,zero_sub] at hr
  have hd := (hasDerivAt_selected_mass n S hS hx hx1).comp T hr
  refine ⟨D,hd,?_⟩
  have hscore : score^2 ≤ (n : ℝ)*x*(1-x) := selected_score_sq_le n S hS hx.le hx1.le
  have hratio : score^2 ≤ 99*(n : ℝ)*(1-x)^2 := by
    have hh := mul_le_mul_of_nonneg_right (show x ≤ 99*(1-x) by linarith)
      (show 0 ≤ (n : ℝ)*(1-x) by positivity)
    nlinarith only [hscore,hh]
  have he : D*T = -score/(1-x) := by
    dsimp only [D,x]
    field_simp
  have hsq : (D*T)^2 ≤ 99*(n : ℝ) := by
    rw [he,div_pow,neg_sq]
    exact (div_le_iff₀ (sq_pos_of_pos hy)).mpr hratio
  have habs : |D*T| ≤ 10*Real.sqrt n := by
    nlinarith [sq_abs (D*T),Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n),
      Real.sqrt_nonneg (n : ℝ),abs_nonneg (D*T)]
  apply (le_div_iff₀ hT).mpr
  simpa only [abs_mul,abs_of_pos hT] using habs

/-- The complementary share has the same uniform radial derivative bound. -/
theorem complementary_radial_derivative_bound_99 (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {b T : ℝ} (hb : 0 < b) (hT : 0 < T)
    (hbT : b ≤ (99/100 : ℝ)*T) :
    ∃ D : ℝ, HasDerivAt (fun t => ∑ k ∈ S, mass n k (1-b/t)) D T ∧
      |D| ≤ 10*Real.sqrt n/T := by
  let x := 1-b/T
  have hxL : 1/100 ≤ x := by dsimp [x]; linarith [(div_le_iff₀ hT).mpr hbT]
  have hx : 0 < x := by linarith
  have hx1 : x < 1 := by dsimp [x]; linarith [div_pos hb hT]
  let score := ∑ k ∈ S, mass n k x*((k : ℝ)-n*x)
  let D := score/(x*(1-x))*(b/T^2)
  have hr := (hasDerivAt_const T (1 : ℝ)).sub
    ((hasDerivAt_const T b).div (hasDerivAt_id T) hT.ne')
  simp only [zero_mul,mul_one,zero_sub,neg_div,neg_neg,id_eq] at hr
  have hd := (hasDerivAt_selected_mass n S hS hx hx1).comp T hr
  refine ⟨D,hd,?_⟩
  have hscore : score^2 ≤ (n : ℝ)*x*(1-x) := selected_score_sq_le n S hS hx.le hx1.le
  have hratio : score^2 ≤ 99*(n : ℝ)*x^2 := by
    have hh := mul_le_mul_of_nonneg_right (show 1-x ≤ 99*x by linarith)
      (show 0 ≤ (n : ℝ)*x by positivity)
    nlinarith only [hscore,hh]
  have he : D*T = score/x := by
    dsimp only [D,x]
    field_simp
    rw [sub_sub_cancel]
    field_simp
  have hsq : (D*T)^2 ≤ 99*(n : ℝ) := by
    rw [he,div_pow]
    exact (div_le_iff₀ (sq_pos_of_pos hx)).mpr hratio
  have habs : |D*T| ≤ 10*Real.sqrt n := by
    nlinarith [sq_abs (D*T),Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) n),
      Real.sqrt_nonneg (n : ℝ),abs_nonneg (D*T)]
  apply (le_div_iff₀ hT).mpr
  simpa only [abs_mul,abs_of_pos hT] using habs


private theorem radial_lipschitz_985 (n : ℕ) (f : ℝ → ℝ) {b v δ T U : ℝ}
    (_hb : 0 < b) (hv : 100 ≤ v) (_hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hbv : b ≤ (197/200 : ℝ)*v)
    (hT : T ∈ Set.Icc (v-δ) (v+δ)) (hU : U ∈ Set.Icc (v-δ) (v+δ))
    (hd : ∀ t, 0 < t → b ≤ (99/100 : ℝ)*t →
      ∃ D, HasDerivAt f D t ∧ |D| ≤ 10*Real.sqrt n/t) :
    |f T-f U| ≤ (20*Real.sqrt n/v)*|T-U| := by
  have hder (t : ℝ) (ht : t ∈ Set.Icc (v-δ) (v+δ)) :
      HasDerivAt f (deriv f t) t ∧ ‖deriv f t‖ ≤ 20*Real.sqrt n/v := by
    have ht0 : 0 < t := by linarith [ht.1]
    obtain ⟨D,hD,hDb⟩ := hd t ht0 (by linarith [ht.1])
    refine ⟨hD.deriv ▸ hD,?_⟩
    rw [hD.deriv,Real.norm_eq_abs]
    apply hDb.trans
    apply (div_le_div_iff₀ ht0 (by linarith : 0 < v)).mpr
    have hh := mul_le_mul_of_nonneg_left (show v ≤ 2*t by linarith [ht.1])
      (show 0 ≤ 10*Real.sqrt n by positivity)
    nlinarith only [hh]
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hder t ht).1.hasDerivWithinAt) (fun t ht => (hder t ht).2)
      (convex_Icc (v-δ) (v+δ)) hU hT

/-- The same selected-order variation remains valid through the unsaturated cofactor band. -/
theorem selected_mass_radial_lipschitz_98 (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {b v δ T U : ℝ}
    (hb : 0 < b) (hv : 100 ≤ v) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hbv : b ≤ (49/50 : ℝ)*v)
    (hT : T ∈ Set.Icc (v-δ) (v+δ)) (hU : U ∈ Set.Icc (v-δ) (v+δ)) :
    |(∑ k ∈ S, mass n k (b/T))-(∑ k ∈ S, mass n k (b/U))| ≤
      (20*Real.sqrt n/v)*|T-U| :=
  radial_lipschitz_985 n _ hb hv hδ hδu (by linarith) hT hU
    (fun _ ht hbt => radial_derivative_bound_99 n S hS hb ht hbt)

/-- The complementary incidence bound also covers the wider cofactor band. -/
theorem complementary_mass_radial_lipschitz_98 (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {b v δ T U : ℝ}
    (hb : 0 < b) (hv : 100 ≤ v) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hbv : b ≤ (49/50 : ℝ)*v)
    (hT : T ∈ Set.Icc (v-δ) (v+δ)) (hU : U ∈ Set.Icc (v-δ) (v+δ)) :
    |(∑ k ∈ S, mass n k (1-b/T))-(∑ k ∈ S, mass n k (1-b/U))| ≤
      (20*Real.sqrt n/v)*|T-U| :=
  radial_lipschitz_985 n _ hb hv hδ hδu (by linarith) hT hU
    (fun _ ht hbt => complementary_radial_derivative_bound_99 n S hS hb ht hbt)

/-- The same selected-order variation remains valid through the unsaturated cofactor band. -/
theorem selected_mass_radial_lipschitz_985 (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {b v δ T U : ℝ}
    (hb : 0 < b) (hv : 100 ≤ v) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hbv : b ≤ (197/200 : ℝ)*v)
    (hT : T ∈ Set.Icc (v-δ) (v+δ)) (hU : U ∈ Set.Icc (v-δ) (v+δ)) :
    |(∑ k ∈ S, mass n k (b/T))-(∑ k ∈ S, mass n k (b/U))| ≤
      (20*Real.sqrt n/v)*|T-U| :=
  radial_lipschitz_985 n _ hb hv hδ hδu (by linarith) hT hU
    (fun _ ht hbt => radial_derivative_bound_99 n S hS hb ht hbt)

/-- The complementary incidence bound also covers the wider cofactor band. -/
theorem complementary_mass_radial_lipschitz_985 (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (n+1)) {b v δ T U : ℝ}
    (hb : 0 < b) (hv : 100 ≤ v) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hbv : b ≤ (197/200 : ℝ)*v)
    (hT : T ∈ Set.Icc (v-δ) (v+δ)) (hU : U ∈ Set.Icc (v-δ) (v+δ)) :
    |(∑ k ∈ S, mass n k (1-b/T))-(∑ k ∈ S, mass n k (1-b/U))| ≤
      (20*Real.sqrt n/v)*|T-U| :=
  radial_lipschitz_985 n _ hb hv hδ hδu (by linarith) hT hU
    (fun _ ht hbt => complementary_radial_derivative_bound_99 n S hS hb ht hbt)


/-- Any fixed prime-count sector has the same allocation-variation mechanism.
The explicit factor is twenty times the total number of prime legs. -/
theorem boundedShare_fibre_variation_985 (A : Finset ℕ) (N : ℕ) {a p q : ℕ}
    (ha : Squarefree a) (hc : 2 ≤ a.primeFactors.card)
    (hp : p.Prime) (hpd : ¬p ∣ a) (hpA : p ∈ A)
    (hq : q.Prime) (hqd : ¬q ∣ a) (hqA : q ∈ A)
    {v δ : ℝ} (hv : 100 ≤ v) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hav : Real.log a ≤ (197/200 : ℝ)*v)
    (hpT : Real.log (p*a : ℕ) ∈ Set.Icc (v-δ) (v+δ))
    (hqT : Real.log (q*a : ℕ) ∈ Set.Icc (v-δ) (v+δ)) :
    |boundedShare A N (p*a)-boundedShare A N (q*a)| ≤
      (20*((a.primeFactors.card : ℝ)+1)*Real.sqrt (N+1)/v)*|Real.log (p*a : ℕ)-Real.log (q*a : ℕ)| := by
  have ha1 : 1 < a := by
    have hne : a ≠ 1 := by intro h; simp [h] at hc
    have := ha.ne_zero
    omega
  have hlog : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha1)
  have hS : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1+1) := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  rw [boundedShare_prime_fibre A N ha (by omega) hp hpd hpA,
    boundedShare_prime_fibre A N ha (by omega) hq hqd hqA]
  have hfirst := selected_mass_radial_lipschitz_985 (N+1) _ hS hlog hv hδ hδu hav hpT hqT
  simp only [Nat.cast_add,Nat.cast_one] at hfirst
  let B := (20*Real.sqrt (N+1)/v)*|Real.log (p*a : ℕ)-Real.log (q*a : ℕ)|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hrow (r : ℕ) (hr : r ∈ a.primeFactors.filter (· ∈ A)) :
      |(∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
        mass (N+1) k (1-Real.log r/Real.log (p*a : ℕ)))-
       (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
        mass (N+1) k (1-Real.log r/Real.log (q*a : ℕ)))| ≤ B := by
    have hrp := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1
    have hrdiv := Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hr).1
    have hrlog : Real.log r ≤ Real.log a := Real.log_le_log
      (by exact_mod_cast hrp.pos) (by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero ha.ne_zero) hrdiv)
    simpa only [B,Nat.cast_add,Nat.cast_one] using complementary_mass_radial_lipschitz_985 (N+1) _ hS
      (Real.log_pos (by exact_mod_cast hrp.one_lt)) hv hδ hδu (hrlog.trans hav) hpT hqT
  have hsum := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hrow)
  rw [Finset.sum_const,nsmul_eq_mul] at hsum
  have hcard : ((a.primeFactors.filter (· ∈ A)).card : ℝ) ≤ a.primeFactors.card := by
    exact_mod_cast Finset.card_filter_le a.primeFactors (· ∈ A)
  have hsum5 := hsum.trans (mul_le_mul_of_nonneg_right hcard hB)
  rw [Finset.sum_sub_distrib] at hsum5
  have hab := abs_add_le
    ((∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k (Real.log a/Real.log (p*a : ℕ)))-
      ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k (Real.log a/Real.log (q*a : ℕ)))
    ((∑ r ∈ a.primeFactors.filter (· ∈ A), ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      mass (N+1) k (1-Real.log r/Real.log (p*a : ℕ)))-
      ∑ r ∈ a.primeFactors.filter (· ∈ A), ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      mass (N+1) k (1-Real.log r/Real.log (q*a : ℕ)))
  dsimp only [B] at hsum5
  convert (hab.trans (add_le_add hfirst hsum5)) using 1 <;> congr 1 <;> ring


/-- The preceding 98-percent allocation estimate remains available unchanged. -/
theorem boundedShare_fibre_variation_98 (A : Finset ℕ) (N : ℕ) {a p q : ℕ}
    (ha : Squarefree a) (hc : 2 ≤ a.primeFactors.card)
    (hp : p.Prime) (hpd : ¬p ∣ a) (hpA : p ∈ A)
    (hq : q.Prime) (hqd : ¬q ∣ a) (hqA : q ∈ A)
    {v δ : ℝ} (hv : 100 ≤ v) (hδ : 0 ≤ δ) (hδu : δ ≤ 1/16)
    (hav : Real.log a ≤ (49/50 : ℝ)*v)
    (hpT : Real.log (p*a : ℕ) ∈ Set.Icc (v-δ) (v+δ))
    (hqT : Real.log (q*a : ℕ) ∈ Set.Icc (v-δ) (v+δ)) :
    |boundedShare A N (p*a)-boundedShare A N (q*a)| ≤
      (20*((a.primeFactors.card : ℝ)+1)*Real.sqrt (N+1)/v)*|Real.log (p*a : ℕ)-Real.log (q*a : ℕ)| := by
  exact boundedShare_fibre_variation_985 A N ha hc hp hpd hpA hq hqd hqA
    hv hδ hδu (by linarith) hpT hqT


end
end RiemannGaussian.ZetaRieszAllocationVariation
