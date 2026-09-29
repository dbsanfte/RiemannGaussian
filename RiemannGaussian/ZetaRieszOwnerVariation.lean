/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszNonownerAllocation
import RiemannGaussian.ZetaRieszAllocationVariation
import RiemannGaussian.ZetaRieszPrimeIntervals

/-!
# Count-free variation of the retained owner allocation

After the global nonowner payment, only one binomial allocation remains per
label. Its radial derivative has a uniform square-root bound on EVERY cofactor
share in (0,1). Near share one the original unpaid-order tail supplies the bound;
there is no artificial upper share cap and no prime-count factor.
-/

namespace RiemannGaussian.ZetaRieszOwnerVariation
noncomputable section
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszBalancedCompanion ZetaRieszAllocationVariation
open ZetaRieszPrimeEndpoint

/-- The same literal unpaid orders have an exponential bound in the
predecessor binomial distribution needed by the score derivative. -/
theorem unpaid_predecessor_mass_le (N : ℕ) {x : ℝ} (hx : (1/2 : ℝ) ≤ x)
    (hx1 : x ≤ 1) :
    (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass N k x) ≤
      Real.exp (-(N : ℝ)/64) := by
  have hx0 : 0 ≤ x := by linarith
  have ht : 0 ≤ Real.log (3/2 : ℝ) := Real.log_nonneg (by norm_num)
  have hUS : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1) := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  have hB : ∀ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      1 ≤ Real.exp ((13/32 : ℝ)*N*Real.log (3/2 : ℝ))*(2/3 : ℝ)^k := by
    intro k hk
    have hkcut := (ZetaRieszWingHighOrders.unpaidOrders_support hk).2.1
    have hc : (k : ℝ) ≤ (13/32 : ℝ)*N := by
      have hn : 32*k ≤ 13*N := by omega
      have hnR : (32 : ℝ)*k ≤ 13*N := by exact_mod_cast hn
      linarith
    have he : (2/3 : ℝ) = Real.exp (-Real.log (3/2 : ℝ)) := by
      rw [Real.exp_neg,Real.exp_log (by norm_num : (0 : ℝ) < 3/2)]
      norm_num
    rw [he,← Real.exp_nat_mul,← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc ht]
  have hh := selected_tilt_bound N _ hUS hx0 hx1 (by norm_num : (0 : ℝ) ≤ 2/3)
    (Real.exp_pos ((13/32 : ℝ)*N*Real.log (3/2 : ℝ))).le hB
  have hb : ((2/3 : ℝ)*x+(1-x))^N ≤ (5/6 : ℝ)^N :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have he : Real.exp ((13/32 : ℝ)*N*Real.log (3/2 : ℝ))*(5/6 : ℝ)^N =
      Real.exp ((N : ℝ)*(Real.log (5/6 : ℝ)+(13/32 : ℝ)*Real.log (3/2 : ℝ))) := by
    rw [show (5/6 : ℝ)^N = Real.exp ((N : ℝ)*Real.log (5/6 : ℝ)) by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 5/6)],← Real.exp_add]
    congr 1
    ring
  apply (hh.trans (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le)).trans
  rw [he]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left balanced_log_rate (Nat.cast_nonneg (α := ℝ) N)]

/-- Lowering the binomial degree removes the apparent radial singularity
at cofactor share one, retaining the exact factorial coefficients. -/
theorem mass_degree_lower {N k : ℕ} (hk : k ≤ N) (x : ℝ) :
    ((N+1 : ℕ) - (k : ℝ))*mass (N+1) k x =
      ((N+1 : ℕ) : ℝ)*(1-x)*mass N k x := by
  have hc : (N.choose k : ℝ)*((N+1 : ℕ) : ℝ) =
      ((N+1).choose k : ℝ)*(((N+1 : ℕ) : ℝ)-k) := by
    have h := congrArg (fun a : ℕ => (a : ℝ)) (Nat.choose_mul_succ_eq N k)
    push_cast [Nat.cast_sub (by omega : k ≤ N+1)] at h
    simpa only [Nat.cast_add,Nat.cast_one] using h
  unfold mass
  rw [show N+1-k = (N-k)+1 by omega,pow_succ]
  linear_combination -x^k*(1-x)^(N-k+1)*hc

/-- The exponential tail absorbs its derivative's linear order factor,
uniformly including the small orders. -/
theorem successor_exp_le_six_sqrt (N : ℕ) :
    ((N : ℝ)+1)*Real.exp (-(N : ℝ)/64) ≤ 6*Real.sqrt (N+1 : ℕ) := by
  have he := Real.add_one_le_exp ((N : ℝ)/32)
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hbase : (N : ℝ)+1 ≤ 32*Real.exp ((N : ℝ)/32) := by linarith
  have heq : Real.exp ((N : ℝ)/32)*Real.exp (-(N : ℝ)/32) = 1 := by
    rw [← Real.exp_add,show (N : ℝ)/32 + -(N : ℝ)/32 = 0 by ring,Real.exp_zero]
  have hmul := mul_le_mul_of_nonneg_right hbase (Real.exp_pos (-(N : ℝ)/32)).le
  have hh : ((N : ℝ)+1)*Real.exp (-(N : ℝ)/32) ≤ 32 := by
    nlinarith only [hmul,heq]
  have hsq : Real.exp (-(N : ℝ)/64)^2 = Real.exp (-(N : ℝ)/32) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hs := mul_le_mul_of_nonneg_left hh (show 0 ≤ (N : ℝ)+1 by positivity)
  rw [← hsq] at hs
  have hr := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (N+1))
  push_cast at hr ⊢
  nlinarith [Real.exp_pos (-(N : ℝ)/64),Real.sqrt_nonneg ((N : ℝ)+1)]

/-- On the entire share interval, the retained owner allocation has a
count-free square-root radial derivative. The high-share proof uses the
literal unpaid-order exponential tail, not a discarded allocation. -/
theorem owner_radial_derivative_bound (N : ℕ) {b T : ℝ}
    (hb : 0 < b) (hT : b < T) :
    ∃ D : ℝ, HasDerivAt (fun t =>
      ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k (b/t)) D T ∧
        |D| ≤ 6*Real.sqrt (N+1 : ℕ)/T := by
  have hT0 : 0 < T := hb.trans hT
  have hUS : ZetaRieszWingHighOrders.unpaidOrders N ⊆ Finset.range (N+1+1) := by
    intro k hk
    have h := unpaid_orders_submajority N k hk
    simp only [Finset.mem_range]
    omega
  by_cases hlow : b ≤ (3/4 : ℝ)*T
  · obtain ⟨D,hD,hDb⟩ := radial_derivative_bound (N+1) _ hUS hb hT0 hlow
    refine ⟨D,hD,hDb.trans ?_⟩
    exact div_le_div_of_nonneg_right (by nlinarith [Real.sqrt_nonneg (N+1 : ℕ)]) hT0.le
  · let x := b/T
    have hx : 0 < x := div_pos hb hT0
    have hx1 : x < 1 := (div_lt_one hT0).mpr hT
    have hxL : (3/4 : ℝ) < x := (lt_div_iff₀ hT0).mpr (lt_of_not_ge hlow)
    let score := ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
      mass (N+1) k x*((k : ℝ)-(N+1 : ℕ)*x)
    let D := score/(x*(1-x))*(-b/T^2)
    have hr := (hasDerivAt_const T b).div (hasDerivAt_id T) hT0.ne'
    simp only [zero_mul,mul_one,zero_sub] at hr
    have hd := (hasDerivAt_selected_mass (N+1) _ hUS hx hx1).comp T hr
    refine ⟨D,hd,?_⟩
    have he : D*T = -score/(1-x) := by
      dsimp only [D,x]
      field_simp
    have hs0 : score ≤ 0 := by
      apply Finset.sum_nonpos
      intro k hk
      have hkn : (k : ℝ) ≤ ((N+1 : ℕ) : ℝ)/2 := by
        have := unpaid_orders_submajority N k hk
        have h : (2 : ℝ)*k < (N+1 : ℕ) := by exact_mod_cast this
        linarith
      apply mul_nonpos_of_nonneg_of_nonpos (mass_nonneg (N+1) k hx.le hx1.le)
      nlinarith [Nat.cast_nonneg (α := ℝ) (N+1)]
    have hscore : -score ≤ ((N+1 : ℕ) : ℝ)*(1-x)*Real.exp (-(N : ℝ)/64) := by
      calc
        -score = ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
            mass (N+1) k x*((N+1 : ℕ)*x-k) := by
          simp only [score,← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ ≤ ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
            ((N+1 : ℕ) : ℝ)*(1-x)*mass N k x := by
          apply Finset.sum_le_sum
          intro k hk
          have hkN : k ≤ N := by have := unpaid_orders_submajority N k hk; omega
          rw [← mass_degree_lower hkN x]
          have hmul := mul_le_mul_of_nonneg_left hx1.le
            (show (0 : ℝ) ≤ (N+1 : ℕ) by positivity)
          nlinarith [mul_le_mul_of_nonneg_left (sub_le_sub_right hmul k)
            (mass_nonneg (N+1) k hx.le hx1.le)]
        _ = ((N+1 : ℕ) : ℝ)*(1-x) *
            ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass N k x := by rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (unpaid_predecessor_mass_le N (by linarith) hx1.le) (by positivity)
    have hDT : |D*T| ≤ 6*Real.sqrt (N+1 : ℕ) := by
      rw [he,abs_of_nonneg (div_nonneg (neg_nonneg.mpr hs0) (by linarith))]
      apply ((div_le_iff₀ (show 0 < 1-x by linarith)).mpr ?_).trans
        (successor_exp_le_six_sqrt N)
      simpa only [Nat.cast_add,Nat.cast_one,mul_assoc,mul_left_comm,mul_comm] using hscore
    apply (le_div_iff₀ hT0).mpr
    simpa only [abs_mul,abs_of_pos hT0] using hDT

/-- Uniform radial variation of the single owner mass. In contrast to the
old sum of incidence bounds, neither a cofactor-share cap nor a count factor
appears. The full unpaid order selection is retained. -/
theorem owner_mass_lipschitz (N : ℕ) {b v δ T U : ℝ} (hb : 0 < b)
    (hv : 100 ≤ v) (hδ : δ ≤ 1/16) (hbv : b < v-δ)
    (hT : T ∈ Set.Icc (v-δ) (v+δ)) (hU : U ∈ Set.Icc (v-δ) (v+δ)) :
    |(∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k (b/T)) -
      (∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k (b/U))| ≤
        (12*Real.sqrt (N+1 : ℕ)/v)*|T-U| := by
  let f := fun t => ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N, mass (N+1) k (b/t)
  have hder (t : ℝ) (ht : t ∈ Set.Icc (v-δ) (v+δ)) :
      HasDerivAt f (deriv f t) t ∧ ‖deriv f t‖ ≤ 12*Real.sqrt (N+1 : ℕ)/v := by
    have hbt : b < t := hbv.trans_le ht.1
    have ht0 : 0 < t := hb.trans hbt
    obtain ⟨D,hD,hDb⟩ := owner_radial_derivative_bound N hb hbt
    refine ⟨hD.deriv ▸ hD,?_⟩
    rw [hD.deriv,Real.norm_eq_abs]
    apply hDb.trans
    apply (div_le_div_iff₀ ht0 (by linarith : 0 < v)).mpr
    have hh := mul_le_mul_of_nonneg_left (show v ≤ 2*t by linarith [ht.1])
      (show 0 ≤ 6*Real.sqrt (N+1 : ℕ) by positivity)
    nlinarith only [hh]
  simpa only [f,Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hder t ht).1.hasDerivWithinAt) (fun t ht => (hder t ht).2)
      (convex_Icc (v-δ) (v+δ)) hU hT

/-- Restricting the EXISTING prime selection to one genuine incidence
gives its exact binomial allocation, with eligibility unchanged. -/
theorem single_prime_share (A : Finset ℕ) (N : ℕ) {n p : ℕ}
    (hs : Squarefree n) (hc : 3 ≤ n.primeFactors.card)
    (hp : p ∈ n.primeFactors) (hpA : p ∈ A) :
    boundedShare (A ∩ {p}) N n =
      ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
        mass (N+1) k (Real.log (n/p : ℕ)/Real.log n) := by
  have hn1 : 1 < n := by
    have hn0 := hs.ne_zero
    have hne : n ≠ 1 := by intro h; simp [h] at hc
    omega
  have hnp : ¬n.Prime := by intro h; simp [h.primeFactors] at hc
  have he : eligibleCofactor p (n/p) := ZetaRieszMarkedSaturation.cofactor_data hs hc hp
  rw [boundedShare,if_pos ⟨hs,hn1,hnp⟩,share_eq_binomial_sum _ N hs hn1]
  rw [Finset.sum_eq_single p]
  · simp [hpA,he]
  · intro q _ hqp
    simp [hqp]
  · exact fun h => (h hp).elim

/-- Actual unique ownership turns the retained allocation into one
binomial mass on the cofactor share. No composite completion is involved. -/
theorem owner_share_fibre (A : Finset ℕ) (N : ℕ) {a p : ℕ}
    (ha : Squarefree a) (hc : 2 ≤ a.primeFactors.card) (hp : p.Prime)
    (hmax : ∀ q ∈ a.primeFactors, q < p) (hpA : p ∈ A) :
    boundedShare (A ∩ {largestPrime (p*a)}) N (p*a) =
      ∑ k ∈ ZetaRieszWingHighOrders.unpaidOrders N,
        mass (N+1) k (Real.log a/Real.log (p*a : ℕ)) := by
  have hpd : ¬p ∣ a := fun h => (lt_irrefl p) (hmax p
    (hp.mem_primeFactors h ha.ne_zero))
  have hsf := Nat.squarefree_mul_iff.mpr ⟨hp.coprime_iff_not_dvd.mpr hpd,hp.squarefree,ha⟩
  have hpf : (p*a).primeFactors = insert p a.primeFactors := by
    rw [Nat.primeFactors_mul hp.ne_zero ha.ne_zero,hp.primeFactors,Finset.singleton_union]
  have hcount : 3 ≤ (p*a).primeFactors.card := by
    rw [hpf,Finset.card_insert_of_notMem
      (show p ∉ a.primeFactors from fun h => hpd (Nat.dvd_of_mem_primeFactors h))]
    omega
  rw [ZetaRieszPrimeIntervals.largestPrime_mul p a hp ha.ne_zero hmax,
    single_prime_share A N hsf hcount (by rw [hpf]; exact Finset.mem_insert_self _ _) hpA,
    Nat.mul_div_cancel_left a hp.pos]

/-- The exact remaining allocation in the literal prime fibre varies by
at most 12 sqrt(N+1)/v, for ALL cofactor shares and ALL prime counts.
Membership in the original physical prime selection is retained at both ends. -/
theorem owner_fibre_variation (A : Finset ℕ) (N : ℕ) {a p q : ℕ}
    (ha : Squarefree a) (hc : 2 ≤ a.primeFactors.card) (hp : p.Prime) (hq : q.Prime)
    (hpmax : ∀ r ∈ a.primeFactors, r < p) (hqmax : ∀ r ∈ a.primeFactors, r < q)
    (hpA : p ∈ A) (hqA : q ∈ A) {v δ : ℝ} (hv : 100 ≤ v) (hδ : δ ≤ 1/16)
    (hpT : Real.log (p*a : ℕ) ∈ Set.Icc (v-δ) (v+δ))
    (hqT : Real.log (q*a : ℕ) ∈ Set.Icc (v-δ) (v+δ)) :
    |boundedShare (A ∩ {largestPrime (p*a)}) N (p*a) -
      boundedShare (A ∩ {largestPrime (q*a)}) N (q*a)| ≤
        (12*Real.sqrt (N+1 : ℕ)/v)*|Real.log p-Real.log q| := by
  have ha1 : 1 < a := by
    have hn0 := ha.ne_zero
    have hn1 : a ≠ 1 := by intro h; simp [h] at hc
    omega
  have hb : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha1)
  have hlp : Real.log (p*a : ℕ) = Real.log p+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hp.ne_zero) (by exact_mod_cast ha.ne_zero)]
  have hlq : Real.log (q*a : ℕ) = Real.log q+Real.log a := by
    rw [Nat.cast_mul,Real.log_mul (by exact_mod_cast hq.ne_zero) (by exact_mod_cast ha.ne_zero)]
  have hp2 : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num)
    (by exact_mod_cast hp.two_le)
  have hbefore : Real.log a < v-δ := by
    rw [hlp] at hpT
    linarith [hpT.2,Real.log_two_gt_d9]
  rw [owner_share_fibre A N ha hc hp hpmax hpA,owner_share_fibre A N ha hc hq hqmax hqA]
  have h := owner_mass_lipschitz N hb hv hδ hbefore hpT hqT
  simpa only [hlp,hlq,add_sub_add_right_eq_sub] using h

end
end RiemannGaussian.ZetaRieszOwnerVariation
