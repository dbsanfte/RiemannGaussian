/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSquarefreeCounting
import RiemannGaussian.ZetaSquarefreeEulerQuadratic

/-!
# Uniform centered counts for rough squarefree divisor families

The complete squarefree counting estimate passes through every actual
roughness intersection and lcm mark. The resulting bound is uniform over
the physical prefix and both complex divisor-weight families. The main
density is subtracted before any norm, and the common-prime corrections
retain a linear total divisor cost.

These estimates concern the complete squarefree arithmetic sequence. Its
ordinary-prime deletion still requires an independent signed estimate.
-/

namespace RiemannGaussian.RoughSquarefreeCounting
noncomputable section
open Complex Filter Topology
open scoped Classical

/-- The exact prefix of the original marked rough squarefree coefficient. -/
def markedCount (S : Finset ℕ) (P N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, RoughSquarefreeBare.coefficient S P n

/-- The canonical marked density retains every signed roughness
intersection of the complete squarefree densities. -/
def markedDensity (S : Finset ℕ) (P : ℕ) : ℂ :=
  if Squarefree P then ∑ W ∈ S.powerset,
    (-1 : ℂ) ^ W.card * (SquarefreeCounting.density (P.primeFactors ∪ W) : ℂ) else 0

private theorem count_cast (W : Finset ℕ) (N : ℕ) :
    (SquarefreeCounting.count W N : ℂ) = ∑ n ∈ Finset.Ioc 0 N,
      if Squarefree n ∧ (∏ p ∈ W, p) ∣ n then (1 : ℂ) else 0 := by
  rw [SquarefreeCounting.count, Complex.ofReal_sum]
  exact Finset.sum_congr rfl (fun n _ ↦ by split_ifs <;> simp)

/-- The arithmetic prefix and its full prime-intersection expansion
are equal before normalization or estimation. -/
theorem markedCount_eq_subsets (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    {P : ℕ} (hP : Squarefree P) (N : ℕ) :
    markedCount S P N = ∑ W ∈ S.powerset,
      (-1 : ℂ) ^ W.card * (SquarefreeCounting.count (P.primeFactors ∪ W) N : ℂ) := by
  simp only [markedCount, RoughSquarefreeBare.coefficient_eq_subsets S hS hP]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro W _
  rw [← Finset.mul_sum, count_cast]

/-- A nonsquarefree divisor mark has zero arithmetic support. -/
theorem markedCount_eq_zero_of_not_squarefree (S : Finset ℕ) {P : ℕ}
    (hP : ¬Squarefree P) (N : ℕ) : markedCount S P N = 0 := by
  apply Finset.sum_eq_zero
  intro n _
  apply if_neg
  rintro ⟨hn, _, hd⟩
  exact hP (hn.squarefree_of_dvd hd)

/-- An excluded prime dividing the mark kills the actual sequence. -/
theorem markedCount_eq_zero_of_sieve_hit (S : Finset ℕ) {P : ℕ}
    (hPS : ∃ a ∈ S, a ∣ P) (N : ℕ) : markedCount S P N = 0 := by
  apply Finset.sum_eq_zero
  intro n _
  apply if_neg
  rintro ⟨_, hn, hd⟩
  obtain ⟨a, ha, hap⟩ := hPS
  exact hn ⟨a, ha, hap.trans hd⟩

/-- The density is the limit of the original normalized arithmetic
prefix, including zero or ineligible marks. -/
theorem markedCount_div_tendsto (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) (P : ℕ) :
    Tendsto (fun N : ℕ ↦ markedCount S P N / (N : ℂ)) atTop (𝓝 (markedDensity S P)) := by
  by_cases hP : Squarefree P
  · have ht (W : Finset ℕ) (hW : W ∈ S.powerset) :
        Tendsto (fun N : ℕ ↦ (SquarefreeCounting.count (P.primeFactors ∪ W) N : ℂ) / N)
          atTop (𝓝 (SquarefreeCounting.density (P.primeFactors ∪ W) : ℂ)) := by
      have hp : ∀ a ∈ P.primeFactors ∪ W, a.Prime := by
        intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact Nat.prime_of_mem_primeFactors ha
        · exact hS a (Finset.mem_powerset.mp hW ha)
      have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
        (SquarefreeCounting.count_div_tendsto (P.primeFactors ∪ W) hp)
      simpa only [Function.comp_def, Complex.ofReal_div, Complex.ofReal_natCast] using h
    have h := tendsto_finsetSum S.powerset (fun W hW ↦ (ht W hW).const_mul ((-1 : ℂ) ^ W.card))
    simpa only [markedCount_eq_subsets S hS hP, markedDensity, if_pos hP,
      Finset.sum_div, mul_div_assoc] using h
  · simp only [markedCount_eq_zero_of_not_squarefree S hP, markedDensity, if_neg hP, zero_div]
    exact tendsto_const_nhds

/-- The signed density vanishes when the original sieve removes the
mark; this follows from its actual counting limit. -/
theorem markedDensity_eq_zero_of_sieve_hit (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    {P : ℕ} (hPS : ∃ a ∈ S, a ∣ P) : markedDensity S P = 0 := by
  have h := markedCount_div_tendsto S hS P
  simp only [markedCount_eq_zero_of_sieve_hit S hPS, zero_div] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- Every roughness subset is retained in the exact centered prefix. -/
theorem markedCount_centered_eq_subsets (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime)
    {P : ℕ} (hP : Squarefree P) (N : ℕ) :
    markedCount S P N - markedDensity S P * N = ∑ W ∈ S.powerset,
      (-1 : ℂ) ^ W.card *
        ((SquarefreeCounting.count (P.primeFactors ∪ W) N : ℂ) -
          (SquarefreeCounting.density (P.primeFactors ∪ W) : ℂ) * N) := by
  rw [markedCount_eq_subsets S hS hP, markedDensity, if_pos hP, Finset.sum_mul,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

/-- The fixed square-sieve cost is independent of the mark, physical
prefix, and first-power prime cutoff. -/
def countingCost (σ : ℝ) : ℝ := Real.exp (3 * primeSquareWeightMass σ)

/-- The counting cost is strictly positive. -/
theorem countingCost_pos (σ : ℝ) : 0 < countingCost σ := Real.exp_pos _

private theorem corrected_product_bound (S : Finset ℕ) (R : ℕ)
    (hS : ∀ a ∈ S, a.Prime ∧ a ≤ R) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∏ a ∈ S, (1 + primeSquareCorrectedWeight σ a)) ≤
      Real.exp (2 * primeSquareWeightMass σ) * Real.exp (4 * Real.sqrt R) := by
  apply le_trans _ (prod_one_add_primeSquareCorrectedWeight_le S R hS hσ)
  apply Finset.prod_le_prod
  · intro a _
    have := primeSquareCorrectedWeight_nonneg σ a
    positivity
  · intro a _
    linarith [primeSquareCorrectedWeight_nonneg σ a]

/-- Every valid marked rough squarefree prefix has an independent
centered power bound retaining the mark's full divisor correction. -/
theorem markedCount_centered_bound_of_eligible (S : Finset ℕ) (R : ℕ)
    (hS : ∀ a ∈ S, a.Prime ∧ a ≤ R) {P : ℕ} (hP : Squarefree P)
    (hPS : ∀ a ∈ P.primeFactors, a ∉ S)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (N : ℕ) :
    ‖markedCount S P N - markedDensity S P * N‖ ≤
      countingCost σ * Real.exp (4 * Real.sqrt R) * (N : ℝ) ^ σ * lcmSqrtFactorMass P := by
  let A : ℝ := Real.exp (primeSquareWeightMass σ) * (N : ℝ) ^ σ
  have hA : 0 ≤ A := by dsimp [A]; positivity
  rw [markedCount_centered_eq_subsets S (fun a ha ↦ (hS a ha).1) hP]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ W ∈ S.powerset, (A * lcmSqrtFactorMass P) *
      ∏ a ∈ W, primeSquareCorrectedWeight σ a := by
      apply Finset.sum_le_sum
      intro W hW
      have hWp : ∀ a ∈ P.primeFactors ∪ W, a.Prime := by
        intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact Nat.prime_of_mem_primeFactors ha
        · exact (hS a (Finset.mem_powerset.mp hW ha)).1
      have hdis : Disjoint P.primeFactors W := Finset.disjoint_left.mpr
        (fun a haP haW ↦ hPS a haP (Finset.mem_powerset.mp hW haW))
      have hb := SquarefreeCounting.count_centered_bound (P.primeFactors ∪ W) hWp hσ hσ1 N
      rw [Finset.prod_union hdis] at hb
      have he : (SquarefreeCounting.count (P.primeFactors ∪ W) N : ℂ) -
          (SquarefreeCounting.density (P.primeFactors ∪ W) : ℂ) * N =
          ((SquarefreeCounting.count (P.primeFactors ∪ W) N -
            SquarefreeCounting.density (P.primeFactors ∪ W) * N : ℝ) : ℂ) := by push_cast; rfl
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, he,
        Complex.norm_real, Real.norm_eq_abs]
      apply hb.trans
      have hf := RoughDivisorIncidence.prod_correctedWeight_le_lcmSqrtFactorMass hP hσ.le
      have hu := mul_le_mul_of_nonneg_right hf
        (Finset.prod_nonneg (s := W) (fun a _ ↦ primeSquareCorrectedWeight_nonneg σ a))
      exact (mul_le_mul_of_nonneg_left hu hA).trans_eq (by dsimp [A]; ring)
    _ = (A * lcmSqrtFactorMass P) * ∏ a ∈ S, (1 + primeSquareCorrectedWeight σ a) := by
      rw [Finset.prod_one_add, Finset.mul_sum]
    _ ≤ (A * lcmSqrtFactorMass P) *
      (Real.exp (2 * primeSquareWeightMass σ) * Real.exp (4 * Real.sqrt R)) :=
      mul_le_mul_of_nonneg_left (corrected_product_bound S R hS hσ)
        (mul_nonneg hA (lcmSqrtFactorMass_nonneg P))
    _ = _ := by
      have he : Real.exp (primeSquareWeightMass σ) * Real.exp (2 * primeSquareWeightMass σ) =
          countingCost σ := by rw [← Real.exp_add, countingCost]; congr 1; ring
      dsimp [A]
      calc
        _ = (Real.exp (primeSquareWeightMass σ) * Real.exp (2 * primeSquareWeightMass σ)) *
          Real.exp (4 * Real.sqrt R) * (N : ℝ) ^ σ * lcmSqrtFactorMass P := by ring
        _ = _ := by rw [he]

/-- The independent marked counting estimate holds for every natural
mark, with impossible marks and sieve intersections handled exactly. -/
theorem markedCount_centered_bound (S : Finset ℕ) (R : ℕ)
    (hS : ∀ a ∈ S, a.Prime ∧ a ≤ R) (P : ℕ)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (N : ℕ) :
    ‖markedCount S P N - markedDensity S P * N‖ ≤
      countingCost σ * Real.exp (4 * Real.sqrt R) * (N : ℝ) ^ σ * lcmSqrtFactorMass P := by
  by_cases hP : Squarefree P
  · by_cases hPS : ∀ a ∈ P.primeFactors, a ∉ S
    · exact markedCount_centered_bound_of_eligible S R hS hP hPS hσ hσ1 N
    · push Not at hPS
      obtain ⟨a, haP, haS⟩ := hPS
      have hh : ∃ a ∈ S, a ∣ P := ⟨a, haS, Nat.dvd_of_mem_primeFactors haP⟩
      rw [markedCount_eq_zero_of_sieve_hit S hh,
        markedDensity_eq_zero_of_sieve_hit S (fun a ha ↦ (hS a ha).1) hh]
      simp only [zero_mul, sub_self, norm_zero]
      exact mul_nonneg (by have := (countingCost_pos σ).le; positivity) (lcmSqrtFactorMass_nonneg P)
  · rw [markedCount_eq_zero_of_not_squarefree S hP, markedDensity, if_neg hP]
    simp only [zero_mul, sub_self, norm_zero]
    exact mul_nonneg (by have := (countingCost_pos σ).le; positivity) (lcmSqrtFactorMass_nonneg P)

/-- The literal prefix of the complete two-family divisor coefficient. -/
def familyCount (S T : Finset ℕ) (w v : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, SquarefreeEulerQuadratic.coefficient S T w v n

/-- The full density matrix keeps both complex coefficient families
and the density of each ordered lcm intersection. -/
def familyDensity (S T : Finset ℕ) (w v : ℕ → ℂ) : ℂ :=
  ∑ d ∈ T, ∑ e ∈ T, w d * v e * markedDensity S (Nat.lcm d e)

/-- The complete arithmetic prefix is its exact ordered lcm matrix. -/
theorem familyCount_eq_lcm_sum (S T : Finset ℕ) (w v : ℕ → ℂ) (N : ℕ) :
    familyCount S T w v N = ∑ d ∈ T, ∑ e ∈ T,
      w d * v e * markedCount S (Nat.lcm d e) N := by
  simp only [familyCount, SquarefreeEulerQuadratic.coefficient_eq_lcm_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [markedCount, Finset.mul_sum]

/-- Centering commutes with the entire signed matrix before a norm
is taken. No diagonal or shared-prime term has been dropped. -/
theorem familyCount_centered_eq (S T : Finset ℕ) (w v : ℕ → ℂ) (N : ℕ) :
    familyCount S T w v N - familyDensity S T w v * N =
      ∑ d ∈ T, ∑ e ∈ T, w d * v e *
        (markedCount S (Nat.lcm d e) N - markedDensity S (Nat.lcm d e) * N) := by
  rw [familyCount_eq_lcm_sum, familyDensity]
  simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_congr rfl (fun _ _ ↦ by ring))

/-- The counting bound keeps a complete weighted lcm budget for
arbitrary finite marks and arbitrary complex coefficient families. -/
theorem familyCount_centered_lcm_bound (S T : Finset ℕ) (R : ℕ)
    (hS : ∀ a ∈ S, a.Prime ∧ a ≤ R) (w v : ℕ → ℂ)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (N : ℕ) :
    ‖familyCount S T w v N - familyDensity S T w v * N‖ ≤
      countingCost σ * Real.exp (4 * Real.sqrt R) * (N : ℝ) ^ σ *
        ∑ d ∈ T, ∑ e ∈ T, ‖w d‖ * ‖v e‖ * lcmSqrtFactorMass (Nat.lcm d e) := by
  rw [familyCount_centered_eq]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ d ∈ T, ∑ e ∈ T,
      ‖w d‖ * ‖v e‖ * (countingCost σ * Real.exp (4 * Real.sqrt R) *
        (N : ℝ) ^ σ * lcmSqrtFactorMass (Nat.lcm d e)) := by
      apply Finset.sum_le_sum
      intro d _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro e _
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (markedCount_centered_bound S R hS _ hσ hσ1 N)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ ↦ Finset.sum_congr rfl (fun _ _ ↦ by ring))

/-- The coefficient-independent constant paying the entire linear
lcm budget and the complete square sieve. -/
def familyCountingCost (σ : ℝ) : ℝ :=
  countingCost σ * (16 * (∑' d, zetaPrimeExpWeight (3 / 2) d) ^ 2 *
    (∑' d, zetaPrimeExpWeight (5 / 4) d) + 1)

/-- The full family counting constant is strictly positive. -/
theorem familyCountingCost_pos (σ : ℝ) : 0 < familyCountingCost σ := by
  have h1 : 0 ≤ ∑' d, zetaPrimeExpWeight (3 / 2) d := tsum_nonneg (fun _ ↦ (Real.exp_pos _).le)
  have h2 : 0 ≤ ∑' d, zetaPrimeExpWeight (5 / 4) d := tsum_nonneg (fun _ ↦ (Real.exp_pos _).le)
  have hc := countingCost_pos σ
  unfold familyCountingCost
  positivity

/-- Every pair of bounded complex divisor families has a centered
arithmetic prefix estimate with linear, rather than quadratic, cutoff
cost. This is uniform over the physical prefix and the original sieve. -/
theorem familyCount_centered_bound (S : Finset ℕ) (R D : ℕ)
    (hS : ∀ a ∈ S, a.Prime ∧ a ≤ R) (w v : ℕ → ℂ)
    (hw : ∀ d ∈ Finset.Icc 1 D, ‖w d‖ ≤ 1)
    (hv : ∀ d ∈ Finset.Icc 1 D, ‖v d‖ ≤ 1)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) (N : ℕ) :
    ‖familyCount S (Finset.Icc 1 D) w v N - familyDensity S (Finset.Icc 1 D) w v * N‖ ≤
      familyCountingCost σ * D * Real.exp (4 * Real.sqrt R) * (N : ℝ) ^ σ := by
  let K : ℝ := 16 * (∑' d, zetaPrimeExpWeight (3 / 2) d) ^ 2 *
    (∑' d, zetaPrimeExpWeight (5 / 4) d)
  let A : ℝ := countingCost σ * Real.exp (4 * Real.sqrt R) * (N : ℝ) ^ σ
  have hA : 0 ≤ A := by have := (countingCost_pos σ).le; dsimp [A]; positivity
  have hm : (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      ‖w d‖ * ‖v e‖ * lcmSqrtFactorMass (Nat.lcm d e)) ≤ K * D := by
    apply le_trans _ (sum_pair_lcmSqrtFactorMass_le_linear D)
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro e he
    have hh : ‖w d‖ * ‖v e‖ ≤ 1 := by
      simpa using mul_le_mul (hw d hd) (hv e he) (norm_nonneg _) (by norm_num)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (lcmSqrtFactorMass_nonneg _)
  calc
    _ ≤ A * ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
      ‖w d‖ * ‖v e‖ * lcmSqrtFactorMass (Nat.lcm d e) :=
      familyCount_centered_lcm_bound S _ R hS w v hσ hσ1 N
    _ ≤ A * (K * D) := mul_le_mul_of_nonneg_left hm hA
    _ ≤ A * ((K + 1) * D) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg D)) hA
    _ = _ := by dsimp [A, K, familyCountingCost]; ring

/-- The actual two-family arithmetic sum on an arbitrary integer
interval, retaining its original coefficient. -/
def familyInterval (S T : Finset ℕ) (w v : ℕ → ℂ) (A B : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc A B, SquarefreeEulerQuadratic.coefficient S T w v n

/-- The interval is exactly the difference of the two original
prefixes, including their endpoints. -/
theorem familyInterval_eq_sub (S T : Finset ℕ) (w v : ℕ → ℂ)
    {A B : ℕ} (hAB : A ≤ B) :
    familyInterval S T w v A B = familyCount S T w v B - familyCount S T w v A := by
  have hsub : Finset.Ioc 0 A ⊆ Finset.Ioc 0 B := Finset.Ioc_subset_Ioc le_rfl hAB
  have hd : Finset.Ioc 0 B \ Finset.Ioc 0 A = Finset.Ioc A B := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Ioc]
    omega
  have h := Finset.sum_sdiff (f := SquarefreeEulerQuadratic.coefficient S T w v) hsub
  rw [hd] at h
  exact eq_sub_iff_add_eq.mpr h

/-- A uniform interval estimate for the complete centered arithmetic
matrix. Both endpoint powers and the exact density term remain visible. -/
theorem familyInterval_centered_bound (S : Finset ℕ) (R D : ℕ)
    (hS : ∀ a ∈ S, a.Prime ∧ a ≤ R) (w v : ℕ → ℂ)
    (hw : ∀ d ∈ Finset.Icc 1 D, ‖w d‖ ≤ 1)
    (hv : ∀ d ∈ Finset.Icc 1 D, ‖v d‖ ≤ 1)
    {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ ≤ 1) {A B : ℕ} (hAB : A ≤ B) :
    ‖familyInterval S (Finset.Icc 1 D) w v A B -
      familyDensity S (Finset.Icc 1 D) w v * ((B : ℂ) - A)‖ ≤
      familyCountingCost σ * D * Real.exp (4 * Real.sqrt R) *
        ((B : ℝ) ^ σ + (A : ℝ) ^ σ) := by
  have hA := familyCount_centered_bound S R D hS w v hw hv hσ hσ1 A
  have hB := familyCount_centered_bound S R D hS w v hw hv hσ hσ1 B
  rw [familyInterval_eq_sub S _ w v hAB]
  have he : familyCount S (Finset.Icc 1 D) w v B - familyCount S (Finset.Icc 1 D) w v A -
      familyDensity S (Finset.Icc 1 D) w v * ((B : ℂ) - A) =
      (familyCount S (Finset.Icc 1 D) w v B - familyDensity S (Finset.Icc 1 D) w v * B) -
        (familyCount S (Finset.Icc 1 D) w v A - familyDensity S (Finset.Icc 1 D) w v * A) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add hB hA).trans_eq (by ring))

end
end RiemannGaussian.RoughSquarefreeCounting
