/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughDivisorCorrelation

/-!
# Linear cutoff cost for complete divisor correlations

Grouping the full least-common-multiple mass by the common divisor retains
its entire divisor correction and gives a linear cutoff bound. The ordinary
prime correction has exactly three entries per prime, so its complete cost
is also linear. This bounds the genuine nonunit correlation for every pair
of bounded complex divisor families, with no coefficient search.

At the actual zero-source normalization, every moving divisor cutoff through
D_N^3 has a uniformly geometric error. The exact unit interaction remains;
these estimates do not bound the surviving source or exclude another zero.
-/

open scoped Classical

namespace RiemannGaussian
noncomputable section

/-- The complete divisor correction is submultiplicative, including shared prime powers. -/
theorem lcmSqrtFactorMass_mul_le (P Q : ℕ) :
    lcmSqrtFactorMass (P * Q) ≤ lcmSqrtFactorMass P * lcmSqrtFactorMass Q := by
  have hsum : (∑ d ∈ (P * Q).divisors, 1 / Real.sqrt d) ≤
      (∑ d ∈ P.divisors, 1 / Real.sqrt d) * (∑ e ∈ Q.divisors, 1 / Real.sqrt e) := by
    rw [Nat.divisors_mul, Finset.mul_def]
    apply (Finset.sum_image_le_of_nonneg (fun _ _ ↦ by positivity)).trans_eq
    rw [Finset.sum_product]
    simp only [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), one_div, mul_inv,
      ← Finset.mul_sum, ← Finset.sum_mul]
  unfold lcmSqrtFactorMass
  calc
    _ ≤ (1 / Real.sqrt (P * Q : ℕ)) *
        ((∑ d ∈ P.divisors, 1 / Real.sqrt d) * (∑ e ∈ Q.divisors, 1 / Real.sqrt e)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg P)]; ring

/-- Retaining the common divisor bounds each intersection through its two reduced factors. -/
theorem lcmSqrtFactorMass_lcm_le_gcd {d e : ℕ} (hd : 0 < d) :
    lcmSqrtFactorMass (Nat.lcm d e) ≤
      lcmSqrtFactorMass (Nat.gcd d e) * lcmSqrtFactorMass (d / Nat.gcd d e) *
        lcmSqrtFactorMass (e / Nat.gcd d e) := by
  let g := Nat.gcd d e
  have hg : 0 < g := Nat.gcd_pos_of_pos_left e hd
  have hde : Nat.lcm d e = (g * (d / g)) * (e / g) := by
    have h : Nat.lcm (g * (d / g)) (g * (e / g)) = g * ((d / g) * (e / g)) := by
      rw [Nat.lcm_mul_left, (Nat.coprime_div_gcd_div_gcd hg).lcm_eq_mul]
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left d e),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right d e)] at h
    exact h.trans (by ring)
  rw [hde]
  exact (lcmSqrtFactorMass_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right (lcmSqrtFactorMass_mul_le _ _) (lcmSqrtFactorMass_nonneg _))

/-- All ordered pairs are bounded through their common divisors and exact divided cutoffs. -/
theorem sum_pair_lcmSqrtFactorMass_le_gcd (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, lcmSqrtFactorMass (Nat.lcm d e)) ≤
      ∑ g ∈ Finset.Icc 1 D, lcmSqrtFactorMass g *
        (∑ a ∈ Finset.Icc 1 (D / g), lcmSqrtFactorMass a) ^ 2 := by
  let s := Finset.Icc 1 D
  let w := fun g d ↦ if g ∣ d then lcmSqrtFactorMass (d / g) else 0
  have hw (g d : ℕ) : 0 ≤ w g d := by
    dsimp [w]
    split_ifs <;> simp only [lcmSqrtFactorMass_nonneg, le_refl]
  calc
    _ ≤ ∑ d ∈ s, ∑ e ∈ s, ∑ g ∈ s, lcmSqrtFactorMass g * w g d * w g e := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro e _
      have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
      have hg : Nat.gcd d e ∈ s := Finset.mem_Icc.mpr
        ⟨Nat.gcd_pos_of_pos_left e hd0,
          (Nat.le_of_dvd hd0 (Nat.gcd_dvd_left d e)).trans (Finset.mem_Icc.mp hd).2⟩
      have h := Finset.single_le_sum
        (f := fun g ↦ lcmSqrtFactorMass g * w g d * w g e)
        (fun g _ ↦ mul_nonneg (mul_nonneg (lcmSqrtFactorMass_nonneg g) (hw g d)) (hw g e)) hg
      simp only [w, if_pos (Nat.gcd_dvd_left d e), if_pos (Nat.gcd_dvd_right d e)] at h
      exact (lcmSqrtFactorMass_lcm_le_gcd hd0).trans h
    _ = ∑ d ∈ s, ∑ g ∈ s, ∑ e ∈ s, lcmSqrtFactorMass g * w g d * w g e := by
      apply Finset.sum_congr rfl
      intro d _
      rw [Finset.sum_comm]
    _ = ∑ g ∈ s, ∑ d ∈ s, ∑ e ∈ s, lcmSqrtFactorMass g * w g d * w g e := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      have hg0 : 0 < g := (Finset.mem_Icc.mp hg).1
      simp only [← Finset.mul_sum, ← Finset.sum_mul, w, s]
      rw [sum_Icc_dvd_eq hg0 D]
      simp only [Nat.mul_div_cancel_left _ hg0]
      ring

/-- The two reduced sums leave only a summable common-divisor weight and one power of the cutoff. -/
theorem sum_pair_lcmSqrtFactorMass_le_weighted (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, lcmSqrtFactorMass (Nat.lcm d e)) ≤
      4 * (∑' d, zetaPrimeExpWeight (3 / 2) d) ^ 2 * D *
        ∑ g ∈ Finset.Icc 1 D, lcmSqrtFactorMass g / g := by
  let Z := ∑' d, zetaPrimeExpWeight (3 / 2) d
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ ↦ (Real.exp_pos _).le)
  apply (sum_pair_lcmSqrtFactorMass_le_gcd D).trans
  calc
    _ ≤ ∑ g ∈ Finset.Icc 1 D, lcmSqrtFactorMass g * (2 * Real.sqrt (D / g : ℕ) * Z) ^ 2 := by
      apply Finset.sum_le_sum
      intro g _
      apply mul_le_mul_of_nonneg_left _ (lcmSqrtFactorMass_nonneg g)
      exact pow_le_pow_left₀ (Finset.sum_nonneg (fun a _ ↦ lcmSqrtFactorMass_nonneg a))
        (RoughDivisorIncidence.sum_lcmSqrtFactorMass_le (D / g)) 2
    _ ≤ ∑ g ∈ Finset.Icc 1 D, 4 * Z ^ 2 * D * (lcmSqrtFactorMass g / g) := by
      apply Finset.sum_le_sum
      intro g hg
      have hg0 : (0 : ℝ) < g := by exact_mod_cast (Finset.mem_Icc.mp hg).1
      have hf : 0 ≤ lcmSqrtFactorMass g := lcmSqrtFactorMass_nonneg g
      have hdiv : ((D / g : ℕ) : ℝ) ≤ (D : ℝ) / g := by
        apply (le_div_iff₀ hg0).mpr
        exact_mod_cast Nat.div_mul_le_self D g
      calc
        _ = (4 * Z ^ 2 * lcmSqrtFactorMass g) * (D / g : ℕ) := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg (D / g))]
          ring
        _ ≤ (4 * Z ^ 2 * lcmSqrtFactorMass g) * ((D : ℝ) / g) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = _ := by ring
    _ = _ := by rw [← Finset.mul_sum]

/-- The residual common-divisor weight is dominated by an explicit summable exponent. -/
theorem lcmSqrtFactorMass_div_le_expWeight {g : ℕ} (hg : 0 < g) :
    lcmSqrtFactorMass g / g ≤ 4 * zetaPrimeExpWeight (5 / 4) g := by
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hs : 0 < Real.sqrt (g : ℝ) := Real.sqrt_pos.mpr hgR
  have hq : 0 < Real.sqrt (Real.sqrt (g : ℝ)) := Real.sqrt_pos.mpr hs
  calc
    _ ≤ (4 / Real.sqrt (Real.sqrt g)) / g :=
      div_le_div_of_nonneg_right (lcmSqrtFactorMass_le_four_div_fourthRoot hg) hgR.le
    _ = 4 * Real.exp (-(Real.log g + Real.log (Real.sqrt (Real.sqrt g)))) := by
      rw [Real.exp_neg, Real.exp_add, Real.exp_log hgR, Real.exp_log hq]
      ring
    _ = _ := by
      rw [Real.log_sqrt hs.le, Real.log_sqrt hgR.le]
      unfold zetaPrimeExpWeight
      congr 2
      ring

/-- The complete ordered lcm mass has linear cutoff cost, including every divisor correction and pair multiplicity. -/
theorem sum_pair_lcmSqrtFactorMass_le_linear (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, lcmSqrtFactorMass (Nat.lcm d e)) ≤
      (16 * (∑' d, zetaPrimeExpWeight (3 / 2) d) ^ 2 *
        (∑' d, zetaPrimeExpWeight (5 / 4) d)) * D := by
  have hsum : (∑ g ∈ Finset.Icc 1 D, lcmSqrtFactorMass g / g) ≤
      4 * ∑' g, zetaPrimeExpWeight (5 / 4) g := by
    calc
      _ ≤ ∑ g ∈ Finset.Icc 1 D, 4 * zetaPrimeExpWeight (5 / 4) g :=
        Finset.sum_le_sum (fun g hg ↦ lcmSqrtFactorMass_div_le_expWeight (Finset.mem_Icc.mp hg).1)
      _ = 4 * ∑ g ∈ Finset.Icc 1 D, zetaPrimeExpWeight (5 / 4) g := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ) < 5 / 4)).sum_le_tsum _
          (fun _ _ ↦ (Real.exp_pos _).le)) (by norm_num)
  apply (sum_pair_lcmSqrtFactorMass_le_weighted D).trans
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)

/-- A prime lcm has exactly the unit-row, unit-column and diagonal contributions, with the unit case removed exactly. -/
theorem prime_lcm_eq_three_entries (f : ℕ → ℝ) (d e : ℕ) :
    (if (Nat.lcm d e).Prime then f (Nat.lcm d e) else 0) =
      (if e = 1 then (if d.Prime then f d else 0) else 0) +
      (if d = 1 then (if e.Prime then f e else 0) else 0) +
      (if d = e then (if d.Prime then f d else 0) else 0) := by
  by_cases hd : d = 1
  · subst d
    by_cases he : e = 1 <;> simp [he, Nat.not_prime_one, eq_comm]
  by_cases he : e = 1
  · subst e
    simp [hd]
  by_cases hde : d = e
  · subst e
    simp [hd]
  have hnp : ¬(Nat.lcm d e).Prime := by
    intro hp
    have hdP := (hp.eq_one_or_self_of_dvd d (Nat.dvd_lcm_left d e)).resolve_left hd
    have heP := (hp.eq_one_or_self_of_dvd e (Nat.dvd_lcm_right d e)).resolve_left he
    exact hde (hdP.trans heP.symm)
  simp [hd, he, hde, hnp]

/-- The complete prime-supported lcm matrix counts every prime exactly three times. -/
theorem sum_pair_prime_lcm_eq (f : ℕ → ℝ) (D : ℕ) :
    (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      if (Nat.lcm d e).Prime then f (Nat.lcm d e) else 0) =
        3 * ∑ a ∈ Finset.Icc 1 D, if a.Prime then f a else 0 := by
  by_cases hD : D = 0
  · simp [hD]
  have hD1 : 1 ≤ D := by omega
  have hrow (d : ℕ) (hd : d ∈ Finset.Icc 1 D) :
      (∑ e ∈ Finset.Icc 1 D, if (Nat.lcm d e).Prime then f (Nat.lcm d e) else 0) =
        2 * (if d.Prime then f d else 0) +
        (if d = 1 then ∑ e ∈ Finset.Icc 1 D, if e.Prime then f e else 0 else 0) := by
    simp_rw [prime_lcm_eq_three_entries, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_Icc, le_refl, true_and, hD1, Finset.mem_Icc.mp hd, if_true,
      Finset.sum_const_zero]
    ring
  rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_Icc, le_refl, true_and,
    hD1, if_true]
  ring

namespace RoughDivisorLinear
open Complex RoughPrimeIncidence RoughDivisorCorrelation

/-- Every nonunit arithmetic entry retains its actual lcm mass and full prime correction; ineligible marks vanish exactly. -/
theorem exists_entry_lcm_bound (y : ℝ) (hy : 1 < |y|) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (N R : ℕ) (S : Finset ℕ) (P : ℕ),
      (∀ a ∈ S, a.Prime ∧ a ≤ R) → P ≠ 1 →
      ‖fibre p 1 S N (3 / 2 + I * y) P‖ ≤
        C * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) * lcmSqrtFactorMass P +
          if P.Prime then Real.log P * ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) P‖ else 0 := by
  obtain ⟨C, hC, hb⟩ := RoughDivisorIncidence.exists_fibre_bound y hy hr hr1
  refine ⟨C, hC, ?_⟩
  intro p N R S P hS hP1
  by_cases hP : Squarefree P ∧ ∀ a ∈ P.primeFactors, a ∉ S
  · simpa only [Nat.cast_one, mul_one] using hb p 1 N R S P le_rfl hS hP.1 hP1 hP.2
  have hz (n : ℕ) : fibreCoefficient 1 S P n = 0 := by
    by_cases hd : P ∣ n
    · by_cases hsf : Squarefree n
      · have he : ∃ a ∈ S, a ∣ n := by
          by_contra he
          apply hP
          exact ⟨hsf.squarefree_of_dvd hd, fun a ha haS ↦
            he ⟨a, haS, (Nat.dvd_of_mem_primeFactors ha).trans hd⟩⟩
        simp [fibreCoefficient, zetaRoughSquarefreeCoefficient, he]
      · simp [fibreCoefficient, zetaRoughSquarefreeCoefficient, zetaSquarefreeCoefficient, hsf]
    · simp [fibreCoefficient, hd]
  simp only [fibre, hz, zero_mul, tsum_zero, norm_zero]
  have hm : 0 ≤ lcmSqrtFactorMass P := lcmSqrtFactorMass_nonneg P
  have hl : 0 ≤ Real.log P := Real.log_natCast_nonneg P
  positivity

/-- The genuine complete nonunit remainder has linear cutoff cost uniformly over both bounded complex weight families. -/
theorem exists_bounded_remainder_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S : Finset ℕ) (w v : ℕ → ℂ),
      1 ≤ D → (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      (∀ d ∈ Finset.Icc 1 D, ‖w d‖ ≤ 1) → (∀ e ∈ Finset.Icc 1 D, ‖v e‖ ≤ 1) →
      ‖remainder p D S w v N (3 / 2 + I * y)‖ ≤
        C * D * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_entry_lcm_bound y hy hr hr1
  let M := 16 * (∑' d, zetaPrimeExpWeight (3 / 2) d) ^ 2 *
    (∑' d, zetaPrimeExpWeight (5 / 4) d)
  have hM : 0 ≤ M := mul_nonneg (by positivity) (tsum_nonneg (fun _ ↦ (Real.exp_pos _).le))
  refine ⟨C * M + 12, by positivity, ?_⟩
  intro p D N R S w v hD hS hw hv
  let E := Real.exp (4 * Real.sqrt R)
  let B := r⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  let L := fun P : ℕ ↦ if P.Prime then Real.log P * ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) P‖ else 0
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (by positivity)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hL (P : ℕ) : 0 ≤ L P := by
    dsimp [L]
    split_ifs
    · exact mul_nonneg (Real.log_natCast_nonneg P) (norm_nonneg _)
    · exact le_rfl
  have hA (P : ℕ) : 0 ≤ (C * E * B) * lcmSqrtFactorMass P + L P :=
    add_nonneg (mul_nonneg (by positivity) (lcmSqrtFactorMass_nonneg P)) (hL P)
  have hpoint (a : ℕ × ℕ) (ha : a ∈ (pairs D).erase (1, 1)) :
      ‖-(w a.1 * star (v a.2)) * fibre p 1 S N (3 / 2 + I * y) (Nat.lcm a.1 a.2)‖ ≤
        (C * E * B) * lcmSqrtFactorMass (Nat.lcm a.1 a.2) + L (Nat.lcm a.1 a.2) := by
    obtain ⟨hne, hap⟩ := Finset.mem_erase.mp ha
    obtain ⟨hd, he⟩ := Finset.mem_product.mp hap
    have hP1 : Nat.lcm a.1 a.2 ≠ 1 := by
      intro h
      have hd1 : a.1 = 1 := Nat.eq_one_of_dvd_one (h ▸ Nat.dvd_lcm_left a.1 a.2)
      have he1 : a.2 = 1 := Nat.eq_one_of_dvd_one (h ▸ Nat.dvd_lcm_right a.1 a.2)
      exact hne (Prod.ext hd1 he1)
    have hmass : ‖w a.1‖ * ‖v a.2‖ ≤ 1 :=
      mul_le_one₀ (hw a.1 hd) (norm_nonneg _) (hv a.2 he)
    rw [norm_mul, norm_neg, norm_mul, norm_star]
    apply (mul_le_mul_of_nonneg_right hmass (norm_nonneg _)).trans
    simpa only [one_mul, E, B, L, mul_assoc] using hb p N R S (Nat.lcm a.1 a.2) hS hP1
  have hp := RoughPrimeIncidence.sum_primeKernel_norm_le p N D
    ((Finset.Icc 1 D).filter Nat.Prime)
    (fun a ha ↦ ⟨(Finset.mem_filter.mp ha).2, (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2⟩)
    y hr hr1
  rw [Finset.sum_filter] at hp
  have hD0 : (0 : ℝ) < D := by exact_mod_cast hD
  have hs : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr hD0
  have hlog : Real.log D ≤ 2 * Real.sqrt D := by
    have h := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hD0.le] at h
    linarith
  have hsl : Real.sqrt D * Real.log D ≤ 2 * D := by
    calc
      _ ≤ Real.sqrt D * (2 * Real.sqrt D) := mul_le_mul_of_nonneg_left hlog hs.le
      _ = _ := by nlinarith [Real.sq_sqrt hD0.le]
  have hprime : (∑ a ∈ Finset.Icc 1 D, L a) ≤ 4 * D * B := by
    apply hp.trans
    change 2 * Real.sqrt D * Real.log D * r⁻¹ ^ N *
      (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) ≤ _
    calc
      _ = (2 * (Real.sqrt D * Real.log D)) * B := by dsimp [B]; ring
      _ ≤ (2 * (2 * D)) * B := by gcongr
      _ = _ := by ring
  unfold remainder
  calc
    _ ≤ ∑ a ∈ (pairs D).erase (1, 1),
        ((C * E * B) * lcmSqrtFactorMass (Nat.lcm a.1 a.2) + L (Nat.lcm a.1 a.2)) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hpoint)
    _ ≤ ∑ a ∈ pairs D,
        ((C * E * B) * lcmSqrtFactorMass (Nat.lcm a.1 a.2) + L (Nat.lcm a.1 a.2)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun a _ _ ↦ hA _)
    _ = (C * E * B) * (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        lcmSqrtFactorMass (Nat.lcm d e)) +
        3 * ∑ a ∈ Finset.Icc 1 D, L a := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [pairs, Finset.product_eq_sprod, Finset.sum_product]
      dsimp only [L]
      rw [sum_pair_prime_lcm_eq
        (fun P : ℕ ↦ Real.log P * ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) P‖) D]
    _ ≤ (C * E * B) * (M * D) + 3 * (4 * D * B) :=
      add_le_add (mul_le_mul_of_nonneg_left (sum_pair_lcmSqrtFactorMass_le_linear D) (by positivity))
        (mul_le_mul_of_nonneg_left hprime (by norm_num))
    _ ≤ (C * E * B) * (M * D) + 3 * (4 * D * (E * B)) := by
      gcongr
      exact le_mul_of_one_le_left hB hE
    _ = _ := by dsimp [E, B]; ring

open Filter Topology

/-- The original source-normalized correlation at an arbitrary divisor cutoff, with the same prime sieve, polynomial and ordinate. -/
def normalizedResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (N D : ℕ) (w v : ℕ → ℂ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    response (zetaRightHalfPoleJetFilter rho hrho) D
      (zetaRightHalfPrimePatternPrimes rho N) w v N (3 / 2 + I * rho.1.im)

/-- At every positive cutoff the full source difference is exactly the normalized nonunit matrix, retaining all phases and cross terms. -/
theorem normalizedResponse_sub_unit_eq (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (N D : ℕ) (hD : 1 ≤ D) (w v : ℕ → ℂ) :
    normalizedResponse rho hrho N D w v - (w 1 * star (v 1)) * unitResponse rho hrho N =
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        remainder (zetaRightHalfPoleJetFilter rho hrho) D
          (zetaRightHalfPrimePatternPrimes rho N) w v N (3 / 2 + I * rho.1.im) := by
  rw [normalizedResponse, response_eq_unit_add_remainder _ D hD _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) w v N (by norm_num)]
  unfold unitResponse
  ring

/-- Every bounded complex family through the cube of the original divisor cutoff has one uniform geometric error allowance. -/
theorem exists_cubic_cutoff_error_bound (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N D : ℕ) (w v : ℕ → ℂ), 1 ≤ D →
      D ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 3 →
      (∀ d ∈ Finset.Icc 1 D, ‖w d‖ ≤ 1) → (∀ e ∈ Finset.Icc 1 D, ‖v e‖ ≤ 1) →
      ‖normalizedResponse rho hrho N D w v - (w 1 * star (v 1)) * unitResponse rho hrho N‖ ≤
        C * RoughPrimeIncidence.rate rho ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let r := RoughPrimeIncidence.radius rho
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq : 0 < q := zero_lt_one.trans (one_lt_zetaMoebiusHeadGrowth hu hu1)
  obtain ⟨hr, hr1, _⟩ := RoughPrimeIncidence.radius_bounds rho hrho
  have hB : 0 ≤ B := by dsimp [B, r]; positivity
  obtain ⟨C, hC, hb⟩ := exists_bounded_remainder_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hr hr1
  refine ⟨C * u * B + 1, by positivity, ?_⟩
  intro N D w v hD hcut hw hv
  have hfloor : (zetaMoebiusGeometricCutoff q N : ℝ) ≤ q ^ N :=
    Nat.floor_le (pow_nonneg hq.le N)
  have hcutR : (D : ℝ) ≤ (q ^ N) ^ 3 := by
    have hD' : (D : ℝ) ≤ (zetaMoebiusGeometricCutoff q N : ℝ) ^ 3 := by exact_mod_cast hcut
    exact hD'.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor 3)
  have hE := RoughPrimeIncidence.exp_sqrt_cutoff_bound rho hrho N
  have he := hb p D N (zetaRightHalfPrimePatternCutoff rho N)
    (zetaRightHalfPrimePatternPrimes rho N) w v hD
    (zetaRightHalfPrimePatternPrimes_eligible rho N) hw hv
  rw [normalizedResponse_sub_unit_eq rho hrho N D hD w v, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_of_nonneg hu.le]
  calc
    _ ≤ u ^ (N + 1) * (C * D *
        Real.exp (4 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) * r⁻¹ ^ N * B) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ u ^ (N + 1) * (C * (q ^ N) ^ 3 * (Real.sqrt q) ^ N * r⁻¹ ^ N * B) := by gcongr
    _ = (C * u * B) * ((u * Real.sqrt q * q ^ 3) / r) ^ N := by
      rw [div_pow, mul_pow, mul_pow, pow_succ,
        show (q ^ 3) ^ N = (q ^ N) ^ 3 by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      simp only [inv_pow, div_eq_mul_inv]
      ring
    _ = (C * u * B) * RoughPrimeIncidence.rate rho ^ N := by
      rw [zetaMoebiusHeadGrowth_sqrt_cubic_rate hu]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith)
      (pow_nonneg (RoughPrimeIncidence.rate_bounds rho hrho).1.le N)

/-- The full source-subtracted correlation tends to zero for arbitrary moving bounded families and cutoffs through D_N^3. -/
theorem tendsto_cubic_cutoff_error (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (D : ℕ → ℕ) (w v : ℕ → ℕ → ℂ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 3 ∧
      (∀ d ∈ Finset.Icc 1 (D N), ‖w N d‖ ≤ 1) ∧
      (∀ e ∈ Finset.Icc 1 (D N), ‖v N e‖ ≤ 1)) :
    Tendsto (fun N ↦ normalizedResponse rho hrho N (D N) (w N) (v N) -
      (w N 1 * star (v N 1)) * unitResponse rho hrho N) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_cubic_cutoff_error_bound rho hrho
  have hlim := (tendsto_const_nhds (x := C)).mul
    (tendsto_pow_atTop_nhds_zero_of_lt_one (RoughPrimeIncidence.rate_bounds rho hrho).1.le
      (RoughPrimeIncidence.rate_bounds rho hrho).2)
  simp only [mul_zero] at hlim
  exact squeeze_zero_norm' (hD.mono (fun N h ↦ hb N (D N) (w N) (v N) h.1 h.2.1 h.2.2.1 h.2.2.2)) hlim

/-- Throughout the enlarged cutoff range the complete correlation retains precisely the limiting unit interaction times the zero multiplicity. -/
theorem tendsto_cubic_cutoff_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (D : ℕ → ℕ) (w v : ℕ → ℕ → ℂ)
    (hD : ∀ᶠ N in atTop, 1 ≤ D N ∧
      D N ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 3 ∧
      (∀ d ∈ Finset.Icc 1 (D N), ‖w N d‖ ≤ 1) ∧
      (∀ e ∈ Finset.Icc 1 (D N), ‖v N e‖ ≤ 1))
    {c : ℂ} (hc : Tendsto (fun N ↦ w N 1 * star (v N 1)) atTop (𝓝 c)) :
    Tendsto (fun N ↦ normalizedResponse rho hrho N (D N) (w N) (v N)) atTop
      (𝓝 (c * (analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : Tendsto (unitResponse rho hrho) atTop (𝓝 (analyticZetaZeroMultiplicity rho : ℂ)) :=
    tendsto_zetaRightHalfRoughSquarefreeCompositeLogFilter rho hrho
  have h := (hc.mul hu).add (tendsto_cubic_cutoff_error rho hrho D w v hD)
  simp only [add_zero] at h
  convert h using 1
  funext N
  ring

end RoughDivisorLinear
end
end RiemannGaussian
