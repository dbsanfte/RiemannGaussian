/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszAllowanceComplement
import RiemannGaussian.ZetaPrimeWindowLocalization

/-!
# Actual balanced three-prime boxes in the allowance complement

These are subsets of the existing carrier, used to audit the proposed
upper bound on its positive allowance. No coefficient or mask is replaced.
-/

namespace RiemannGaussian.ZetaRieszAllowancePrimeBoxes
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open PrimeWindow

/-- An ordinary-prime interval with its exact logarithmic endpoints. -/
def logPrimes (a h : ℝ) : Finset ℕ := primesInWindow (Real.exp a) (Real.exp h)

theorem logPrimes_bounds {a h : ℝ} {p : ℕ} (hp : p ∈ logPrimes a h) :
    p.Prime ∧ a < Real.log p ∧ Real.log p ≤ a + h := by
  have hb := mem_primesInWindow_bounds (Real.exp_pos a).le (Real.exp_pos h).le hp
  refine ⟨hb.2.2, ?_, ?_⟩
  · simpa using Real.log_lt_log (Real.exp_pos a) hb.1
  · simpa [← Real.exp_add, add_comm] using
      Real.log_le_log (by exact_mod_cast hb.2.2.pos) hb.2.1

/-- Consecutive half-open prime boxes are strictly ordered and hence disjoint. -/
theorem logPrimes_order {a b h : ℝ} (hab : a + h ≤ b) {p q : ℕ}
    (hp : p ∈ logPrimes a h) (hq : q ∈ logPrimes b h) : p < q := by
  have hpB := logPrimes_bounds hp
  have hqB := logPrimes_bounds hq
  exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hpB.1.pos)
    (by exact_mod_cast hqB.1.pos)).mp (hpB.2.2.trans_lt (hab.trans_lt hqB.2.1))

/-- Products count each integer once, using three ordered disjoint prime intervals. -/
def tripleProducts (a h : ℝ) : Finset ℕ :=
  (((logPrimes a h).product (logPrimes (a + h) h)).product
    (logPrimes (a + 2 * h) h)).image (fun v => v.1.1 * (v.1.2 * v.2))

theorem triple_product_injective {a h : ℝ} (hh : 0 ≤ h) :
    Set.InjOn (fun v : (ℕ × ℕ) × ℕ => v.1.1 * (v.1.2 * v.2))
      ((((logPrimes a h).product (logPrimes (a + h) h)).product
        (logPrimes (a + 2 * h) h)) : Set ((ℕ × ℕ) × ℕ)) := by
  rintro ⟨⟨p,q⟩,r⟩ hv ⟨⟨p',q'⟩,r'⟩ hv' he
  obtain ⟨hpq, hr⟩ := Finset.mem_product.mp hv
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
  obtain ⟨hpq', hr'⟩ := Finset.mem_product.mp hv'
  obtain ⟨hp', hq'⟩ := Finset.mem_product.mp hpq'
  have pp := (logPrimes_bounds hp).1
  have qp := (logPrimes_bounds hq).1
  have pp' := (logPrimes_bounds hp').1
  have qp' := (logPrimes_bounds hq').1
  have rp' := (logPrimes_bounds hr').1
  change p * (q*r) = p' * (q'*r') at he
  have hpD : p ∣ p' * (q'*r') := he ▸ dvd_mul_right p (q*r)
  have hpe : p = p' := by
    rcases pp.dvd_mul.mp hpD with h | h
    · exact ((pp'.dvd_iff_eq pp.ne_one).mp h).symm
    rcases pp.dvd_mul.mp h with h | h
    · have heq := (qp'.dvd_iff_eq pp.ne_one).mp h
      exact False.elim ((logPrimes_order (by linarith) hp hq').ne heq.symm)
    · have heq := (rp'.dvd_iff_eq pp.ne_one).mp h
      exact False.elim ((logPrimes_order (by linarith) hp hr').ne heq.symm)
  subst p'
  have hqr : q*r = q'*r' := Nat.eq_of_mul_eq_mul_left pp.pos he
  have hqD : q ∣ q'*r' := hqr ▸ dvd_mul_right q r
  have hqe : q = q' := by
    rcases qp.dvd_mul.mp hqD with h | h
    · exact ((qp'.dvd_iff_eq qp.ne_one).mp h).symm
    · have heq := (rp'.dvd_iff_eq qp.ne_one).mp h
      exact False.elim ((logPrimes_order (by linarith) hq hr').ne heq.symm)
  subst q'
  have hre : r = r' := Nat.eq_of_mul_eq_mul_left qp.pos hqr
  simp only [hre]

theorem tripleProducts_card {a h : ℝ} (hh : 0 ≤ h) :
    (tripleProducts a h).card =
      (logPrimes a h).card * (logPrimes (a + h) h).card *
        (logPrimes (a + 2*h) h).card := by
  rw [tripleProducts, Finset.card_image_of_injOn (triple_product_injective hh)]
  simp only [Finset.product_eq_sprod, Finset.card_product]

/-- Every box integer has exactly three distinct factors, with the full product window retained. -/
theorem tripleProducts_bounds {a h : ℝ} (_hh : 0 ≤ h) {n : ℕ}
    (hn : n ∈ tripleProducts a h) :
    Squarefree n ∧ n.primeFactors.card = 3 ∧
      3*a + 3*h < Real.log n ∧ Real.log n ≤ 3*a + 6*h ∧
      ∀ p ∈ n.primeFactors, Real.log p ≤ a + 3*h := by
  obtain ⟨⟨⟨p,q⟩,r⟩, hv, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hpq, hr⟩ := Finset.mem_product.mp hv
  obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
  have pB := logPrimes_bounds hp
  have qB := logPrimes_bounds hq
  have rB := logPrimes_bounds hr
  have hpq' := logPrimes_order (by linarith) hp hq
  have hpr' := logPrimes_order (by linarith) hp hr
  have hqr' := logPrimes_order (by linarith) hq hr
  have hcopqr : q.Coprime r := qB.1.coprime_iff_not_dvd.mpr
    (fun hd => hqr'.ne ((rB.1.dvd_iff_eq qB.1.ne_one).mp hd).symm)
  have hcop : p.Coprime (q*r) := pB.1.coprime_iff_not_dvd.mpr (by
    intro hd
    rcases pB.1.dvd_mul.mp hd with hd | hd
    · exact hpq'.ne ((qB.1.dvd_iff_eq pB.1.ne_one).mp hd).symm
    · exact hpr'.ne ((rB.1.dvd_iff_eq pB.1.ne_one).mp hd).symm)
  have hsf := Nat.squarefree_mul_iff.mpr ⟨hcop,pB.1.squarefree,
    Nat.squarefree_mul_iff.mpr ⟨hcopqr,qB.1.squarefree,rB.1.squarefree⟩⟩
  have hpf : (p*(q*r)).primeFactors = {p,q,r} := by
    simp [Nat.primeFactors_mul pB.1.ne_zero (Nat.mul_ne_zero qB.1.ne_zero rB.1.ne_zero),
      Nat.primeFactors_mul qB.1.ne_zero rB.1.ne_zero,
      pB.1.primeFactors,qB.1.primeFactors,rB.1.primeFactors, Finset.insert_comm]
  have hlog : Real.log (p*(q*r) : ℕ) = Real.log p + Real.log q + Real.log r := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast pB.1.ne_zero)
      (by exact_mod_cast Nat.mul_ne_zero qB.1.ne_zero rB.1.ne_zero), Nat.cast_mul,
      Real.log_mul (by exact_mod_cast qB.1.ne_zero) (by exact_mod_cast rB.1.ne_zero)]
    ring
  refine ⟨hsf, ?_, ?_, ?_, ?_⟩
  · simp [hpf, hpq'.ne, hpr'.ne, hqr'.ne]
  · dsimp only
    rw [hlog]
    linarith [pB.2.1,qB.2.1,rB.2.1]
  · dsimp only
    rw [hlog]
    linarith [pB.2.2,qB.2.2,rB.2.2]
  · intro s hs
    simp only [hpf, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl <;> linarith [pB.2.2,qB.2.2,rB.2.2]

/-- The PNT gives a uniform cardinality lower bound on every bounded translate of these boxes. -/
theorem eventually_logPrimes_card_lower {h C : ℝ} (hh : 0 < h) (hC : 0 ≤ C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop, ∀ a : ℝ,
      (2/3:ℝ)*N ≤ a → a ≤ (2/3:ℝ)*N+C →
      c * Real.exp ((2/3:ℝ)*N) / (N+1) ≤ ((logPrimes a h).card : ℝ) := by
  let d := (Real.exp h - 1) / 2
  let D := 1+C+h
  have hd : 0 < d := by dsimp [d]; linarith [Real.one_lt_exp_iff.mpr hh]
  have hD : 0 < D := by dsimp [D]; linarith
  refine ⟨d/D, div_pos hd hD, ?_⟩
  have hm := (theta_interval_div_tendsto (Real.exp_pos h)).eventually_const_lt
    (show d < Real.exp h-1 by dsimp [d]; linarith [Real.one_lt_exp_iff.mpr hh])
  obtain ⟨X,hX⟩ := eventually_atTop.mp hm
  have hx : Tendsto (fun N : ℕ => Real.exp ((2/3:ℝ)*N)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  filter_upwards [hx.eventually (eventually_ge_atTop X)] with N hN a ha hau
  have he : Real.exp ((2/3:ℝ)*N) ≤ Real.exp a := Real.exp_le_exp.mpr ha
  have hl := (lt_div_iff₀ (Real.exp_pos a)).mp (hX (Real.exp a) (hN.trans he))
  rw [← sum_log_primesInWindow (Real.exp_pos a).le (Real.one_le_exp_iff.mpr hh.le)] at hl
  have hs : (∑ p ∈ logPrimes a h, Real.log p) ≤ (logPrimes a h).card * (D*(N+1)) := by
    calc
      _ ≤ ∑ _p ∈ logPrimes a h, D*(N+1) := Finset.sum_le_sum (fun p hp => by
        have := (logPrimes_bounds hp).2.2
        dsimp only [D]
        nlinarith [Nat.cast_nonneg (α := ℝ) N, mul_nonneg hC (Nat.cast_nonneg (α := ℝ) N),
          mul_nonneg hh.le (Nat.cast_nonneg (α := ℝ) N)])
      _ = _ := by simp
  have hm0 := mul_le_mul_of_nonneg_left he hd.le
  apply (div_le_iff₀ (by positivity : (0:ℝ)<(N:ℝ)+1)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hD).mpr
  have hc0 : (0:ℝ) ≤ (logPrimes a h).card := Nat.cast_nonneg _
  dsimp only [logPrimes] at hs ⊢
  nlinarith

/-- Bounded shifts find a positive cosine box at every order, for each fixed real height. -/
theorem exists_positive_phase_boxes (y : ℝ) :
    ∃ h C : ℝ, 0 < h ∧ 0 ≤ C ∧ ∀ b : ℝ, ∃ a : ℝ,
      b ≤ a ∧ a ≤ b+C ∧ ∀ t : ℝ,
        3*a+3*h ≤ t → t ≤ 3*a+6*h → (1/2:ℝ) ≤ Real.cos (y*t) := by
  by_cases hy : y = 0
  · subst y
    exact ⟨1,0,by norm_num,by norm_num,fun b => ⟨b,le_rfl,by linarith,
      fun _ _ _ => by norm_num⟩⟩
  let z := |y|
  have hz : 0 < z := abs_pos.mpr hy
  let h := 1/(6*(z+1))
  let C := 2*Real.pi/(3*z)
  have hh : 0 < h := by dsimp [h]; positivity
  refine ⟨h,C,hh,by dsimp [C]; positivity,?_⟩
  intro b
  let k : ℤ := ⌈z*(3*b+3*h)/(2*Real.pi)⌉
  let a := ((k:ℝ)*(2*Real.pi)/z-3*h)/3
  have hlo : z*(3*b+3*h) ≤ (k:ℝ)*(2*Real.pi) :=
    (div_le_iff₀ (by positivity : (0:ℝ)<2*Real.pi)).mp (Int.le_ceil _)
  have hhi : (k:ℝ)*(2*Real.pi) < z*(3*b+3*h)+2*Real.pi := by
    have ht := (Int.ceil_lt_add_one (z*(3*b+3*h)/(2*Real.pi)))
    have ht' := mul_lt_mul_of_pos_right ht (by positivity : (0:ℝ)<2*Real.pi)
    simpa only [add_mul, div_mul_cancel₀ _ (by positivity : 2*Real.pi ≠ 0), one_mul] using ht'
  have ha : z*(3*a+3*h) = (k:ℝ)*(2*Real.pi) := by dsimp [a]; field_simp; ring
  have hb : b ≤ a := by nlinarith
  have hab : a ≤ b+C := by
    have hC : C*(3*z)=2*Real.pi := by dsimp [C]; field_simp
    nlinarith
  refine ⟨a,hb,hab,?_⟩
  intro t ht htu
  have he : Real.cos (z*(3*a+3*h))=1 := by rw [ha, Real.cos_int_mul_two_pi]
  have hd : |z*t-z*(3*a+3*h)| ≤ 1/2 := by
    rw [abs_of_nonneg (by nlinarith)]
    have hw : 3*z*h ≤ 1/2 := by
      dsimp [h]
      rw [mul_one_div]
      apply (div_le_iff₀ (by positivity : (0:ℝ)<6*(z+1))).mpr
      nlinarith
    nlinarith
  have hd' := Real.abs_cos_sub_cos_le (z*t) (z*(3*a+3*h))
  have hc : (1/2:ℝ) ≤ Real.cos (z*t) := by rw [he] at hd'; linarith [neg_le_abs (Real.cos (z*t)-1)]
  have hec : Real.cos (z*t) = Real.cos (y*t) := by
    dsimp [z]
    rcases le_total 0 y with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, neg_mul, Real.cos_neg]
  exact hec ▸ hc

end
end RiemannGaussian.ZetaRieszAllowancePrimeBoxes
