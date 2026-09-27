/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPhaseBudget

/-!
# Relative prime budgets on wide cofactor intervals

Exact unions of fixed logarithmic prime windows give near-sharp relative
Darboux budgets on windows whose widths grow with the moment. Up to four
outer prime legs cost less than one thousandth in population precision.
These are positive counting estimates for signed compensation. They are
not source-normalized absolute PNT errors and do not change the fixed
phase width of the cofactor-dependent last prime.
-/

namespace RiemannGaussian.ZetaRieszMacroPrimeWindows
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszAllowancePrimeBoxes

/-- The half-open logarithmic description includes all endpoint primes. -/
theorem mem_logPrimes_iff (p : ℕ) (a h : ℝ) :
    p ∈ logPrimes a h ↔ p.Prime ∧ a < Real.log p ∧ Real.log p ≤ a+h := by
  refine ⟨logPrimes_bounds,?_⟩
  rintro ⟨hp,hlo,hhi⟩
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨?_,?_⟩,hp⟩
  · apply (Nat.floor_lt (Real.exp_nonneg a)).mpr
    simpa only [Real.exp_log hpR] using Real.exp_lt_exp.mpr hlo
  · apply (Nat.le_floor_iff (mul_nonneg (Real.exp_nonneg h) (Real.exp_nonneg a))).mpr
    simpa only [Real.exp_add,Real.exp_log hpR,mul_comm] using Real.exp_le_exp.mpr hhi

/-- Adjacent windows partition literal primes, without an endpoint error. -/
theorem logPrimes_add (a : ℝ) {h k : ℝ} (hh : 0 ≤ h) (hk : 0 ≤ k) :
    logPrimes a (h+k) = logPrimes a h ∪ logPrimes (a+h) k := by
  ext p
  simp only [Finset.mem_union,mem_logPrimes_iff]
  constructor
  · rintro ⟨hp,hlo,hhi⟩
    by_cases hm : Real.log p ≤ a+h
    · exact Or.inl ⟨hp,hlo,hm⟩
    · exact Or.inr ⟨hp,lt_of_not_ge hm,by linarith⟩
  · rintro (⟨hp,hlo,hhi⟩ | ⟨hp,hlo,hhi⟩)
    · exact ⟨hp,hlo,by linarith⟩
    · exact ⟨hp,by linarith,by linarith⟩

/-- The shared endpoint belongs to only the first interval. -/
theorem logPrimes_adjacent_disjoint (a h k : ℝ) :
    Disjoint (logPrimes a h) (logPrimes (a+h) k) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact ((logPrimes_bounds hq).2.1).not_ge (logPrimes_bounds hp).2.2

/-- A long cofactor-prime interval is an exact sum of fixed-width
intervals. The number of intervals can grow with the moment order. -/
theorem reciprocal_grid (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (M : ℕ) :
    (∑ p ∈ logPrimes a (M*h), (p : ℝ)⁻¹) =
      ∑ i ∈ Finset.range M, ∑ p ∈ logPrimes (a+i*h) h, (p : ℝ)⁻¹ := by
  induction M with
  | zero =>
    have he : logPrimes a 0 = ∅ := by
      ext p
      simp only [mem_logPrimes_iff,Finset.notMem_empty,iff_false]
      rintro ⟨_,hl,hu⟩
      linarith
    simp [he]
  | succ M ih =>
    rw [Nat.cast_succ,add_mul,one_mul,logPrimes_add a (mul_nonneg (Nat.cast_nonneg _) hh) hh,
      Finset.sum_union (logPrimes_adjacent_disjoint a (M*h) h),Finset.sum_range_succ,ih]

/-- Uniform fixed-window estimates give lower and upper Darboux
population budgets on arbitrarily long cofactor-prime windows. -/
theorem eventually_grid_reciprocal_bounds {h α : ℝ}
    (hh : 0 < h) (hhu : h ≤ 1/100000) (hα : 0 < α) :
    ∀ᶠ N : ℕ in atTop, ∀ (a : ℝ) (M : ℕ), α*N ≤ a →
      (9999/10000 : ℝ)*(M*h)/(a+M*h) ≤
          ∑ p ∈ logPrimes a (M*h), (p : ℝ)⁻¹ ∧
      (∑ p ∈ logPrimes a (M*h), (p : ℝ)⁻¹) ≤ (10001/10000 : ℝ)*(M*h)/a := by
  filter_upwards [ZetaRieszPhaseBudget.eventually_phase_window_mass hh hhu hα,
    eventually_ge_atTop (1 : ℕ)] with N hN hN1 a M ha
  have ha0 : 0 < a := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    nlinarith
  have hi (i : ℕ) : α*N ≤ a+i*h :=
    ha.trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh.le))
  rw [reciprocal_grid a hh.le M]
  constructor
  · calc
      _ = ∑ _i ∈ Finset.range M, (9999/10000 : ℝ)*h/(a+M*h) := by simp; ring
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hiM
        have hib : (i : ℝ) ≤ M := by exact_mod_cast (Finset.mem_range.mp hiM).le
        exact (div_le_div_of_nonneg_left (by positivity)
          (by positivity : 0 < a+i*h)
          (by nlinarith : a+i*h ≤ a+M*h)).trans (hN (a+i*h) (hi i)).1
  · calc
      _ ≤ ∑ _i ∈ Finset.range M, (10001/10000 : ℝ)*h/a := by
        apply Finset.sum_le_sum
        intro i _
        exact (hN (a+i*h) (hi i)).2.trans
          (div_le_div_of_nonneg_left (by positivity) ha0
            (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh.le)))
      _ = _ := by simp; ring


/-- Enlarging a log interval includes its literal endpoint primes. -/
theorem logPrimes_mono_width (a : ℝ) {h k : ℝ} (hk : h ≤ k) :
    logPrimes a h ⊆ logPrimes a k := by
  intro p hp
  have hb := logPrimes_bounds hp
  exact (mem_logPrimes_iff p a k).mpr ⟨hb.1,hb.2.1,by linarith [hb.2.2]⟩

/-- Arbitrarily long outer prime windows have near-sharp relative
Darboux budgets. The last-prime phase interval need not be enlarged with
them: its center is adjusted to the exact cofactor elsewhere. -/
theorem eventually_macro_reciprocal_bounds {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∀ᶠ N : ℕ in atTop, ∀ a H : ℝ, α*N ≤ a → β*N ≤ H →
      (4999/5000 : ℝ)*H/(a+H) ≤ ∑ p ∈ logPrimes a H, (p : ℝ)⁻¹ ∧
      (∑ p ∈ logPrimes a H, (p : ℝ)⁻¹) ≤ (5001/5000 : ℝ)*H/a := by
  have hsize : ∀ᶠ N : ℕ in atTop, 1 ≤ β*(N : ℝ) :=
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hβ).eventually_ge_atTop 1
  filter_upwards [eventually_grid_reciprocal_bounds
    (by norm_num : (0 : ℝ) < 1/100000) (by norm_num) hα,
    hsize,eventually_ge_atTop (1 : ℕ)] with N hN hsize hN1 a H ha hH
  have ha0 : 0 < a := by
    have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    nlinarith
  have hH1 : 1 ≤ H := hsize.trans hH
  have hH0 : 0 ≤ H := by linarith
  let M := ⌊H/(1/100000 : ℝ)⌋₊
  have hlo : (M : ℝ)*(1/100000 : ℝ) ≤ H := by
    have hh := Nat.floor_le (div_nonneg hH0 (by norm_num : (0 : ℝ) ≤ 1/100000))
    change (M : ℝ) ≤ H/(1/100000 : ℝ) at hh
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 1/100000)).mp hh
  have hhi : H < ((M : ℝ)+1)*(1/100000 : ℝ) := by
    have hh := Nat.lt_floor_add_one (H/(1/100000 : ℝ))
    change H/(1/100000 : ℝ) < (M : ℝ)+1 at hh
    exact (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1/100000)).mp hh
  have hlow := (hN a M ha).1
  have hupp := (hN a (M+1) ha).2
  norm_num only [Nat.cast_add,Nat.cast_one] at hupp
  have hmasslo : (∑ p ∈ logPrimes a (M*(1/100000 : ℝ)), (p : ℝ)⁻¹) ≤
      ∑ p ∈ logPrimes a H, (p : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (logPrimes_mono_width a hlo)
    intro p _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg p)
  have hmasshi : (∑ p ∈ logPrimes a H, (p : ℝ)⁻¹) ≤
      ∑ p ∈ logPrimes a ((M+1)*(1/100000 : ℝ)), (p : ℝ)⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (logPrimes_mono_width a (by
      exact hhi.le))
    intro p _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg p)
  constructor
  · apply le_trans _ (hlow.trans hmasslo)
    calc
      (4999/5000 : ℝ)*H/(a+H) ≤
          (9999/10000 : ℝ)*(M*(1/100000 : ℝ))/(a+H) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        nlinarith
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
        (by linarith)
  · apply (hmasshi.trans hupp).trans
    apply div_le_div_of_nonneg_right _ ha0.le
    nlinarith


/-- Up to four wide cofactor-prime windows cost less than one thousandth
in population accuracy. Their widths may be proportional to the moment;
the moving last-prime construction retains the exact total phase. -/
theorem eventually_macro_tuple_bounds {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    {k : ℕ} (hk : k ≤ 4) :
    ∀ᶠ N : ℕ in atTop, ∀ a H : Fin k → ℝ,
      (∀ i, α*N ≤ a i) → (∀ i, β*N ≤ H i) →
      (999/1000 : ℝ)*(∏ i, H i/(a i+H i)) ≤
        ∑ p ∈ Fintype.piFinset (fun i => logPrimes (a i) (H i)), ∏ i, (p i : ℝ)⁻¹ ∧
      (∑ p ∈ Fintype.piFinset (fun i => logPrimes (a i) (H i)), ∏ i, (p i : ℝ)⁻¹) ≤
        (1001/1000 : ℝ)*(∏ i, H i/a i) := by
  have hlow : (999/1000 : ℝ) ≤ (4999/5000 : ℝ)^k := by
    interval_cases k <;> norm_num
  have hupp : (5001/5000 : ℝ)^k ≤ (1001/1000 : ℝ) := by
    interval_cases k <;> norm_num
  filter_upwards [eventually_macro_reciprocal_bounds hα hβ,eventually_ge_atTop (1 : ℕ)]
    with N hN hN1 a H ha hH
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have ha0 (i : Fin k) : 0 < a i := by nlinarith [ha i]
  have hH0 (i : Fin k) : 0 < H i := by nlinarith [hH i]
  have hlo : (∏ i, (4999/5000 : ℝ)*(H i/(a i+H i))) ≤
      ∏ i, ∑ p ∈ logPrimes (a i) (H i), (p : ℝ)⁻¹ := by
    apply Finset.prod_le_prod
    · intro i _
      exact mul_nonneg (by norm_num) (div_nonneg (hH0 i).le (by linarith [ha0 i,hH0 i]))
    · intro i _
      simpa only [mul_div_assoc] using (hN (a i) (H i) (ha i) (hH i)).1
  have hhi : (∏ i, ∑ p ∈ logPrimes (a i) (H i), (p : ℝ)⁻¹) ≤
      ∏ i, (5001/5000 : ℝ)*(H i/a i) := by
    apply Finset.prod_le_prod
    · intro i _
      exact Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
    · intro i _
      simpa only [mul_div_assoc] using (hN (a i) (H i) (ha i) (hH i)).2
  rw [Finset.prod_mul_distrib] at hlo hhi
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hlo hhi
  rw [← Finset.prod_univ_sum (fun i : Fin k => logPrimes (a i) (H i))
    (fun (_ : Fin k) (p : ℕ) => (p : ℝ)⁻¹)]
  refine ⟨(mul_le_mul_of_nonneg_right hlow ?_).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_right hupp ?_)⟩
  · exact Finset.prod_nonneg (fun i _ => div_nonneg (hH0 i).le (by linarith [ha0 i,hH0 i]))
  · exact Finset.prod_nonneg (fun i _ => div_nonneg (hH0 i).le (ha0 i).le)

/-- Ordered outer boxes with distinct widths still enumerate cofactors
exactly once. No factorial multiplicity can inflate the supplied credit. -/
theorem ordered_macro_product_injective {k : ℕ} {a H : Fin k → ℝ}
    (horder : ∀ i j, i < j → a i+H i ≤ a j) :
    Set.InjOn (fun p : Fin k → ℕ => ∏ i, p i)
      (Fintype.piFinset (fun i => logPrimes (a i) (H i)) : Set _) := by
  intro p hp q hq he
  dsimp only at he
  funext i
  have hpi := (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).1
  have hd : p i ∣ ∏ j, q j := by
    rw [← he]
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
  obtain ⟨j,_,hj⟩ := (hpi.prime.dvd_finsetProd_iff q).mp hd
  have heq := (Nat.prime_dvd_prime_iff_eq hpi
    (logPrimes_bounds (Fintype.mem_piFinset.mp hq j)).1).mp hj
  have hij : i = j := by
    have hl (x z : Fin k) (hx : x < z) (p q : Fin k → ℕ)
        (hp : p ∈ Fintype.piFinset (fun i => logPrimes (a i) (H i)))
        (hq : q ∈ Fintype.piFinset (fun i => logPrimes (a i) (H i))) : p x < q z := by
      have hb := logPrimes_bounds (Fintype.mem_piFinset.mp hp x)
      have hc := logPrimes_bounds (Fintype.mem_piFinset.mp hq z)
      exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hb.1.pos)
        (by exact_mod_cast hc.1.pos)).mp (hb.2.2.trans_lt ((horder x z hx).trans_lt hc.2.1))
    rcases lt_trichotomy i j with hij | hij | hij
    · exact False.elim ((hl i j hij p q hp hq).ne heq)
    · exact hij
    · exact False.elim ((hl j i hij q p hq hp).ne heq.symm)
  simpa only [← hij] using heq


/-- Ordered prime tuples with the same integer product agree coordinate
by coordinate, even when they come from different outer cells. -/
theorem ordered_prime_product_eq {k : ℕ} {p q : Fin k → ℕ}
    (hp : ∀ i, (p i).Prime) (hq : ∀ i, (q i).Prime)
    (hpm : StrictMono p) (hqm : StrictMono q)
    (he : (∏ i, p i) = ∏ i, q i) : p = q := by
  apply hpm.range_inj hqm |>.mp
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    have hd : p i ∣ ∏ j, q j := by
      rw [← he]
      exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)
    obtain ⟨j,_hj,hd⟩ := ((hp i).prime.dvd_finsetProd_iff q).mp hd
    exact ⟨j,((Nat.prime_dvd_prime_iff_eq (hp i) (hq j)).mp hd).symm⟩
  · rintro ⟨i,rfl⟩
    have hd : q i ∣ ∏ j, p j := by
      rw [he]
      exact Finset.dvd_prod_of_mem q (Finset.mem_univ i)
    obtain ⟨j,_hj,hd⟩ := ((hq i).prime.dvd_finsetProd_iff p).mp hd
    exact ⟨j,((Nat.prime_dvd_prime_iff_eq (hq i) (hp j)).mp hd).symm⟩

/-- A separated coordinate makes two ordered cofactor populations disjoint.
This pays supply aggregation by geometry, not by assuming independence. -/
theorem disjoint_ordered_macro_products {k : ℕ} {a H b G : Fin k → ℝ}
    (ha : ∀ i j, i < j → a i+H i ≤ a j)
    (hb : ∀ i j, i < j → b i+G i ≤ b j)
    (hsep : ∃ i, a i+H i ≤ b i ∨ b i+G i ≤ a i) :
    Disjoint ((Fintype.piFinset (fun i => logPrimes (a i) (H i))).image
      (fun p => (∏ i, p i : ℕ)))
      ((Fintype.piFinset (fun i => logPrimes (b i) (G i))).image
        (fun p => (∏ i, p i : ℕ))) := by
  apply Finset.disjoint_left.mpr
  intro m hm hn
  obtain ⟨p,hp,hpm⟩ := Finset.mem_image.mp hm
  obtain ⟨q,hq,hqm⟩ := Finset.mem_image.mp hn
  have hmono {a H : Fin k → ℝ} (hord : ∀ i j, i < j → a i+H i ≤ a j)
      {v : Fin k → ℕ} (hv : v ∈ Fintype.piFinset (fun i => logPrimes (a i) (H i))) :
      StrictMono v := by
    intro i j hij
    have hl := logPrimes_bounds (Fintype.mem_piFinset.mp hv i)
    have hu := logPrimes_bounds (Fintype.mem_piFinset.mp hv j)
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hl.1.pos)
      (by exact_mod_cast hu.1.pos)).mp (hl.2.2.trans_lt ((hord i j hij).trans_lt hu.2.1))
  have he := ordered_prime_product_eq
    (fun i => (logPrimes_bounds (Fintype.mem_piFinset.mp hp i)).1)
    (fun i => (logPrimes_bounds (Fintype.mem_piFinset.mp hq i)).1)
    (hmono ha hp) (hmono hb hq) (hpm.trans hqm.symm)
  subst q
  obtain ⟨i,hi⟩ := hsep
  have hpi := logPrimes_bounds (Fintype.mem_piFinset.mp hp i)
  have hqi := logPrimes_bounds (Fintype.mem_piFinset.mp hq i)
  rcases hi with hi | hi <;> linarith [hpi.2.1,hpi.2.2,hqi.2.1,hqi.2.2]

end
end RiemannGaussian.ZetaRieszMacroPrimeWindows
