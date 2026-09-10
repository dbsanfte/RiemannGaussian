/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughPrimeIncidence
import RiemannGaussian.NatLcmSqrtMass

/-!
# Complete squarefree-divisor incidences in the rough arithmetic carrier

The shared-prime correction is the same multiplicative divisor mass that
appears in the existing least-common-multiple estimate. Summing that mass
before taking a worst-case factor bound preserves the full square-root
scale. This supports complete bounded divisor-weight families, retaining
their higher prime intersections inside the original rough squarefree sum.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian.RoughDivisorIncidence
noncomputable section
open RoughPrimeIncidence

/-- Summing the full divisor correction retains a square-root cutoff
cost with one fixed convergent mass; there is no divisor-count loss. -/
theorem sum_lcmSqrtFactorMass_le (X : ℕ) :
    (∑ P ∈ Finset.Icc 1 X, lcmSqrtFactorMass P) ≤
      2 * Real.sqrt X * ∑' d, zetaPrimeExpWeight (3 / 2) d := by
  have hdiv (P : ℕ) (hP : P ∈ Finset.Icc 1 X) :
      (∑ d ∈ P.divisors, 1 / Real.sqrt d) =
        ∑ d ∈ Finset.Icc 1 X, if d ∣ P then 1 / Real.sqrt d else 0 := by
    have hP0 : P ≠ 0 := by have := (Finset.mem_Icc.mp hP).1; omega
    calc
      _ = ∑ d ∈ P.divisors, if d ∣ P then 1 / Real.sqrt d else 0 :=
        Finset.sum_congr rfl (fun d hd ↦ (if_pos (Nat.dvd_of_mem_divisors hd)).symm)
      _ = _ := Finset.sum_subset (fun d hd ↦ Finset.mem_Icc.mpr
        ⟨Nat.pos_of_mem_divisors hd, (Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)).trans
          (Finset.mem_Icc.mp hP).2⟩) (by
        intro d _ hd
        have hnot : ¬d ∣ P := fun h ↦ hd (Nat.mem_divisors.mpr ⟨h, hP0⟩)
        simp [hnot])
  have he : (∑ P ∈ Finset.Icc 1 X, lcmSqrtFactorMass P) =
      ∑ d ∈ Finset.Icc 1 X, (1 / Real.sqrt d) *
        ∑ P ∈ Finset.Icc 1 X, if d ∣ P then 1 / Real.sqrt P else 0 := by
    calc
      _ = ∑ P ∈ Finset.Icc 1 X, ∑ d ∈ Finset.Icc 1 X,
          (1 / Real.sqrt d) * (if d ∣ P then 1 / Real.sqrt P else 0) := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [lcmSqrtFactorMass, hdiv P hP, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        split_ifs <;> ring
      _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
  have hw (d : ℕ) (hd : d ∈ Finset.Icc 1 X) :
      (1 / Real.sqrt d) / d = zetaPrimeExpWeight (3 / 2) d := by
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hs0 : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hd0
    calc
      _ = Real.exp (-(Real.log d + Real.log (Real.sqrt d))) := by
        rw [Real.exp_neg, Real.exp_add, Real.exp_log hd0, Real.exp_log hs0]
        ring
      _ = _ := by rw [Real.log_sqrt hd0.le]; unfold zetaPrimeExpWeight; congr 1; ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 X, (1 / Real.sqrt d) * (2 * Real.sqrt X / d) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (sum_Icc_dvd_inv_sqrt_le (Finset.mem_Icc.mp hd).1 X) (by positivity)
    _ = 2 * Real.sqrt X * ∑ d ∈ Finset.Icc 1 X, zetaPrimeExpWeight (3 / 2) d := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← hw d hd]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((summable_zetaPrimeExpWeight (by norm_num : (1 : ℝ) < 3 / 2)).sum_le_tsum _
        (fun d _ ↦ (Real.exp_pos _).le)) (by positivity)

private theorem lcmSqrtFactorMass_prod (W : Finset ℕ) (hW : ∀ a ∈ W, a.Prime) :
    lcmSqrtFactorMass (∏ a ∈ W, a) = ∏ a ∈ W, lcmSqrtFactorMass a := by
  induction W using Finset.induction_on with
  | empty => simp [lcmSqrtFactorMass]
  | @insert a W ha ih =>
    have hap : a.Prime := hW a (Finset.mem_insert_self _ _)
    have hWp : ∀ b ∈ W, b.Prime := fun b hb ↦ hW b (Finset.mem_insert_of_mem hb)
    have hcop : a.Coprime (∏ b ∈ W, b) := by
      simpa only [Finset.prod_singleton] using
        coprime_prod_primes_of_disjoint (W := {a}) (V := W)
          (by intro b hb; simpa using (Finset.mem_singleton.mp hb) ▸ hap) hWp
          (by simpa using ha)
    rw [Finset.prod_insert ha, lcmSqrtFactorMass_mul hcop, ih hWp, Finset.prod_insert ha]

/-- The squarefree intersection cost is bounded by the exact lcm
divisor mass, retaining its physical factor weight and every shared prime. -/
theorem prod_correctedWeight_le_lcmSqrtFactorMass {P : ℕ} (hP : Squarefree P)
    {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    (∏ a ∈ P.primeFactors, primeSquareCorrectedWeight σ a) ≤ lcmSqrtFactorMass P := by
  have hp : ∀ a ∈ P.primeFactors, a.Prime := fun _ ha ↦ Nat.prime_of_mem_primeFactors ha
  calc
    _ ≤ ∏ a ∈ P.primeFactors, lcmSqrtFactorMass a := by
      apply Finset.prod_le_prod (fun a _ ↦ primeSquareCorrectedWeight_nonneg σ a)
      intro a ha
      have hw : zetaPrimeExpWeight σ a ≤ 1 / Real.sqrt a := by
        simpa only [norm_zetaPrimeFeature, Complex.ofReal_re] using
          norm_zetaPrimeFeature_le_inv_sqrt (s := (σ : ℂ)) hσ (hp a ha).pos
      rw [lcmSqrtFactorMass_prime (hp a ha), primeSquareCorrectedWeight]
      apply mul_le_mul hw (by linarith) (by unfold zetaPrimeExpWeight; positivity) (by positivity)
    _ = lcmSqrtFactorMass (∏ a ∈ P.primeFactors, a) := (lcmSqrtFactorMass_prod _ hp).symm
    _ = _ := by rw [Nat.prod_primeFactors_of_squarefree hP]

private theorem marked_prefix_eq (D : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {P : ℕ} (hP : Squarefree P) (n : ℕ) :
    (if P ∣ n then zetaRoughSquarefreePrefixCoefficient D S n else 0) =
      ∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card *
        zetaSquarefreeDivisibilityPrefixCoefficient D (P.primeFactors ∪ W) n := by
  have hPp : ∀ a ∈ P.primeFactors, a.Prime := fun _ ha ↦ Nat.prime_of_mem_primeFactors ha
  have he (W : Finset ℕ) (hW : W ∈ S.powerset) :
      zetaSquarefreeDivisibilityPrefixCoefficient D (P.primeFactors ∪ W) n =
        if P ∣ n then zetaSquarefreeDivisibilityPrefixCoefficient D W n else 0 := by
    have hWp : ∀ a ∈ W, a.Prime := fun a ha ↦ hS a (Finset.mem_powerset.mp hW ha)
    have hU : ∀ a ∈ P.primeFactors ∪ W, a.Prime := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · exact hPp a ha
      · exact hWp a ha
    rw [zetaSquarefreeDivisibilityPrefixCoefficient_eq_indicator D (P.primeFactors ∪ W) n,
      zetaSquarefreeDivisibilityPrefixCoefficient_eq_indicator D W n]
    have hd : (∏ a ∈ P.primeFactors ∪ W, a) ∣ n ↔ P ∣ n ∧ (∏ a ∈ W, a) ∣ n := by
      rw [prod_primes_dvd_iff _ hU]
      simp only [Finset.forall_mem_union]
      rw [← prod_primes_dvd_iff _ hPp, ← prod_primes_dvd_iff _ hWp,
        Nat.prod_primeFactors_of_squarefree hP]
    simp only [hd]
    by_cases hPn : P ∣ n <;> simp [hPn]
  have hsum := Finset.sum_congr rfl (fun W hW ↦
    congrArg (fun z : ℂ ↦ (-1 : ℂ) ^ W.card * z) (he W hW))
  rw [hsum]
  by_cases hPn : P ∣ n
  · simp only [hPn, if_true]
    exact zetaRoughSquarefreePrefixCoefficient_eq_subsets D S hS n
  · simp [hPn]

/-- Every nontrivial squarefree divisor mark keeps all prime
intersections in its exact completion. Only an ordinary-prime mark has
an ordinary-prime correction, and that correction is explicit. -/
theorem fibreCoefficient_eq (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {P : ℕ} (hP : Squarefree P) (hP1 : P ≠ 1)
    (hPS : ∀ a ∈ P.primeFactors, a ∉ S) (n : ℕ) :
    RoughPrimeIncidence.fibreCoefficient D S P n =
      (∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card *
        zetaSquarefreeDivisibilityPrefixCoefficient D (P.primeFactors ∪ W) n) +
      if P.Prime then (if n = P then (Real.log P : ℂ) else 0) else 0 := by
  have hp : (if P ∣ n then zetaRoughPrimeCoefficient S n else 0) =
      if P.Prime then (if n = P then (Real.log P : ℂ) else 0) else 0 := by
    by_cases hn : n = P
    · subst n
      by_cases hprime : P.Prime
      · have hnot : P ∉ S := hPS P (by simp [hprime.primeFactors])
        simp [zetaRoughPrimeCoefficient, hprime, hnot]
      · simp [zetaRoughPrimeCoefficient, hprime]
    · have hno : ¬(P ∣ n ∧ n.Prime) := by
        rintro ⟨hd, hprime⟩
        exact hn ((hprime.eq_one_or_self_of_dvd P hd).resolve_left hP1).symm
      by_cases hd : P ∣ n
      · have hnp : ¬n.Prime := fun h ↦ hno ⟨hd, h⟩
        simp [hd, hn, zetaRoughPrimeCoefficient, hnp]
      · simp [hd, hn]
  rw [← marked_prefix_eq D S hS hP n, ← hp]
  unfold RoughPrimeIncidence.fibreCoefficient
  rw [zetaRoughSquarefreeCoefficient_eq_prefix_add_prime D hD S hS n]
  split_ifs <;> simp

/-- The complete divisor-marked series genuinely sums to its exact
signed squarefree intersections and its possible single prime correction. -/
theorem hasSum_fibre (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {P : ℕ} (hP : Squarefree P) (hP1 : P ≠ 1)
    (hPS : ∀ a ∈ P.primeFactors, a ∉ S) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ RoughPrimeIncidence.fibreCoefficient D S P n * zetaPrimeFilterKernel p N s n)
      ((∑ W ∈ S.powerset, (-1 : ℂ) ^ W.card *
        zetaSquarefreeDivisibilityPrefixFilter p D (P.primeFactors ∪ W) N s) +
        if P.Prime then (Real.log P : ℂ) * zetaPrimeFilterKernel p N s P else 0) := by
  have h := hasSum_sum (s := S.powerset) (fun W hW ↦
    (summable_zetaSquarefreeDivisibilityPrefixFilter p D N (P.primeFactors ∪ W)
      (by
        intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact Nat.prime_of_mem_primeFactors ha
        · exact hS a (Finset.mem_powerset.mp hW ha)) hs).hasSum.mul_left ((-1 : ℂ) ^ W.card))
  have hp : HasSum (fun n ↦ if P.Prime then
      (if n = P then (Real.log P : ℂ) * zetaPrimeFilterKernel p N s P else 0) else 0)
      (if P.Prime then (Real.log P : ℂ) * zetaPrimeFilterKernel p N s P else 0) := by
    by_cases hprime : P.Prime
    · simpa only [if_pos hprime] using hasSum_ite_eq P ((Real.log P : ℂ) * zetaPrimeFilterKernel p N s P)
    · simp [hprime]
  apply (h.add hp).congr_fun
  intro n
  rw [fibreCoefficient_eq D hD S hS hP hP1 hPS n, add_mul, Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl (fun W _ ↦ by ring)
  · by_cases hprime : P.Prime <;> by_cases hn : n = P <;> simp [hprime, hn]

/-- All squarefree divisor marks retain the complete lcm divisor
mass in their bound. This includes arbitrarily many distinct prime factors. -/
theorem exists_fibre_bound (y : ℝ) (hy : 1 < |y|) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R : ℕ) (S : Finset ℕ) (P : ℕ),
      1 ≤ D → (∀ a ∈ S, a.Prime ∧ a ≤ R) → Squarefree P → P ≠ 1 →
      (∀ a ∈ P.primeFactors, a ∉ S) →
      ‖RoughPrimeIncidence.fibre p D S N (3 / 2 + I * y) P‖ ≤
        C * D * Real.exp (4 * Real.sqrt R) * r⁻¹ ^ N *
          (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k) * lcmSqrtFactorMass P +
        if P.Prime then Real.log P * ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) P‖ else 0 := by
  obtain ⟨C, hC, hb⟩ := exists_zetaSquarefreeDivisibilityPrefixFilter_bound y hy hr hr1
  let τ := zetaSquareSieveExponent r
  let w := primeSquareCorrectedWeight τ
  refine ⟨C * Real.exp (2 * primeSquareWeightMass τ), by positivity, ?_⟩
  intro p D N R S P hD hS hP hP1 hPS
  let A := C * D * r⁻¹ ^ N * (∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hw : ∀ a, 0 ≤ w a := primeSquareCorrectedWeight_nonneg τ
  have hM : 0 ≤ lcmSqrtFactorMass P := lcmSqrtFactorMass_nonneg P
  rw [RoughPrimeIncidence.fibre,
    (hasSum_fibre p D N hD S (fun a ha ↦ (hS a ha).1) hP hP1 hPS (by norm_num)).tsum_eq]
  apply (norm_add_le _ _).trans
  have hp : ‖(if P.Prime then (Real.log P : ℂ) * zetaPrimeFilterKernel p N (3 / 2 + I * y) P else 0)‖ =
      if P.Prime then Real.log P * ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) P‖ else 0 := by
    by_cases hprime : P.Prime
    · simp only [if_pos hprime, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.log_natCast_nonneg P)]
    · simp only [if_neg hprime, norm_zero]
  rw [hp]
  apply add_le_add _ le_rfl
  calc
    _ ≤ ∑ W ∈ S.powerset, A * (lcmSqrtFactorMass P * ∏ a ∈ W, w a) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro W hW
      have hdis : Disjoint P.primeFactors W := Finset.disjoint_left.mpr
        (fun a haP haW ↦ hPS a haP (Finset.mem_powerset.mp hW haW))
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      have h := hb p D N (P.primeFactors ∪ W) (by
        intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · exact Nat.prime_of_mem_primeFactors ha
        · exact (hS a (Finset.mem_powerset.mp hW ha)).1)
      rw [Finset.prod_union hdis] at h
      apply h.trans
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (prod_correctedWeight_le_lcmSqrtFactorMass hP (zetaSquareSieveExponent_gt_half hr1).le)
          (Finset.prod_nonneg (fun a _ ↦ hw a))) hA
    _ = (A * lcmSqrtFactorMass P) * ∏ a ∈ S, (1 + w a) := by
      rw [Finset.prod_one_add, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun W _ ↦ by ring)
    _ ≤ (A * lcmSqrtFactorMass P) * ∏ a ∈ S, (1 + 2 * w a) := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod (fun a _ ↦ by linarith [hw a])
        (fun a _ ↦ by linarith [hw a])) (mul_nonneg hA hM)
    _ ≤ (A * lcmSqrtFactorMass P) *
        (Real.exp (2 * primeSquareWeightMass τ) * Real.exp (4 * Real.sqrt R)) :=
      mul_le_mul_of_nonneg_left
        (prod_one_add_primeSquareCorrectedWeight_le S R hS (zetaSquareSieveExponent_gt_half hr1))
        (mul_nonneg hA hM)
    _ = _ := by dsimp [A, τ]; ring

/-- The total variation of every finite squarefree-divisor family
has the same square-root cutoff scale as the prime-only bound. Every
shared-prime correction and the complete prime leakage are included. -/
theorem exists_sum_norm_fibre_bound (y : ℝ) (hy : 1 < |y|)
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Polynomial ℂ) (D N R X : ℕ) (S T : Finset ℕ),
      1 ≤ D → (∀ a ∈ S, a.Prime ∧ a ≤ R) →
      (∀ P ∈ T, Squarefree P ∧ P ≠ 1 ∧ P ≤ X ∧ (∀ a ∈ P.primeFactors, a ∉ S)) →
      (∑ P ∈ T, ‖RoughPrimeIncidence.fibre p D S N (3 / 2 + I * y) P‖) ≤
        C * D * Real.exp (4 * Real.sqrt R) * Real.sqrt X * (1 + Real.log X) * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k := by
  obtain ⟨C, hC, hb⟩ := exists_fibre_bound y hy hr hr1
  let Z := ∑' d, zetaPrimeExpWeight (3 / 2) d
  have hZ : 0 ≤ Z := tsum_nonneg (fun _ ↦ (Real.exp_pos _).le)
  refine ⟨2 * C * Z + 2, by positivity, ?_⟩
  intro p D N R X S T hD hS hT
  let E : ℝ := D * Real.exp (4 * Real.sqrt R)
  let B := r⁻¹ ^ N * ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hE : 1 ≤ E := one_le_mul_of_one_le_of_one_le (by exact_mod_cast hD)
    (Real.one_le_exp_iff.mpr (by positivity))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsub : T ⊆ Finset.Icc 1 X := fun P hP ↦ Finset.mem_Icc.mpr
    ⟨Nat.pos_of_ne_zero (hT P hP).1.ne_zero, (hT P hP).2.2.1⟩
  have hmass : (∑ P ∈ T, lcmSqrtFactorMass P) ≤ 2 * Real.sqrt X * Z :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun P _ _ ↦ lcmSqrtFactorMass_nonneg P)).trans
      (sum_lcmSqrtFactorMass_le X)
  have hprime := RoughPrimeIncidence.sum_primeKernel_norm_le p N X (T.filter Nat.Prime)
    (fun a ha ↦ ⟨(Finset.mem_filter.mp ha).2, (hT a (Finset.mem_filter.mp ha).1).2.2.1⟩) y hr hr1
  rw [Finset.sum_filter] at hprime
  have hsum := Finset.sum_le_sum (fun P hP ↦
    hb p D N R S P hD hS (hT P hP).1 (hT P hP).2.1 (hT P hP).2.2.2)
  calc
    _ ≤ (C * E * B) * (∑ P ∈ T, lcmSqrtFactorMass P) +
        ∑ P ∈ T, if P.Prime then Real.log P * ‖zetaPrimeFilterKernel p N (3 / 2 + I * y) P‖ else 0 := by
      apply hsum.trans_eq
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      dsimp only [E, B]
      ring
    _ ≤ (C * E * B) * (2 * Real.sqrt X * Z) +
        2 * Real.sqrt X * Real.log X * r⁻¹ ^ N *
          ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k :=
      add_le_add (mul_le_mul_of_nonneg_left hmass (by positivity)) hprime
    _ = (2 * C * Z * E + 2 * Real.log X) * Real.sqrt X * B := by dsimp [B]; ring
    _ ≤ ((2 * C * Z + 2) * E * (1 + Real.log X)) * Real.sqrt X * B := by
      have hl := Real.log_natCast_nonneg X
      have hLE : Real.log X ≤ E * Real.log X := by nlinarith
      have hCZE : 0 ≤ C * Z * E := by positivity
      have hstep : 2 * C * Z * E + 2 * Real.log X ≤ (2 * C * Z + 2) * E * (1 + Real.log X) := by
        nlinarith [mul_nonneg hCZE hl]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hstep (Real.sqrt_nonneg X)) hB
    _ = _ := by dsimp [E, B]; ring

/-- All nontrivial squarefree-divisor marks through `D_N^4` have a
uniform independently vanishing total variation at the original source
normalization. No bound on the number of prime factors is needed. -/
theorem exists_actual_sum_norm_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (T : Finset ℕ),
      (∀ P ∈ T, Squarefree P ∧ P ≠ 1 ∧
        P ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4 ∧
        (∀ a ∈ P.primeFactors, a ∉ zetaRightHalfPrimePatternPrimes rho N)) →
      (∑ P ∈ T, ‖actualFibre rho hrho N P‖) ≤ C * (1 + (N : ℝ)) * rate rho ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let r := radius rho
  let p := zetaRightHalfPoleJetFilter rho hrho
  let B : ℝ := ∑ k ∈ p.support, ‖p.coeff k‖ * r⁻¹ ^ k
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq1 : 1 < q := one_lt_zetaMoebiusHeadGrowth hu hu1
  have hq : 0 < q := zero_lt_one.trans hq1
  have hlq : 0 < Real.log q := Real.log_pos hq1
  have hrate : 0 ≤ rate rho := (rate_bounds rho hrho).1.le
  obtain ⟨hr, hr1, _⟩ := radius_bounds rho hrho
  have hB : 0 ≤ B := by dsimp [B, r]; positivity
  obtain ⟨C, hC, hb⟩ := exists_sum_norm_fibre_bound rho.1.im
    (nontrivialZetaZero_one_lt_abs_im rho) hr hr1
  refine ⟨C * u * B * (1 + 4 * Real.log q) + 1, by positivity, ?_⟩
  intro N T hT
  let D := zetaMoebiusGeometricCutoff q N
  have hDpos : 1 ≤ D := zetaRightHalfPoleJetCutoff_pos rho hrho N
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg hq.le N)
  have he := exp_sqrt_cutoff_bound rho hrho N
  have hsqrt : Real.sqrt ((D ^ 4 : ℕ) : ℝ) = (D : ℝ) ^ 2 := by
    rw [Nat.cast_pow, show (D : ℝ) ^ 4 = ((D : ℝ) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg (D : ℝ))]
  have hlog : Real.log ((D ^ 4 : ℕ) : ℝ) ≤ 4 * (N : ℝ) * Real.log q := by
    rw [Nat.cast_pow, Real.log_pow]
    have h := Real.log_le_log (show (0 : ℝ) < D by exact_mod_cast hDpos) hD
    rw [Real.log_pow] at h
    norm_num
    linarith
  have hbound := hb p D N (zetaRightHalfPrimePatternCutoff rho N) (D ^ 4)
    (zetaRightHalfPrimePatternPrimes rho N) T hDpos (zetaRightHalfPrimePatternPrimes_eligible rho N) hT
  have hnorm : ‖(3 / 2 - rho.1.re : ℝ)‖ = u := Real.norm_of_nonneg hu.le
  simp only [actualFibre, norm_mul, norm_pow, Complex.norm_real, hnorm]
  rw [← Finset.mul_sum]
  calc
    _ ≤ u ^ (N + 1) * (C * D * Real.exp (4 * Real.sqrt (zetaRightHalfPrimePatternCutoff rho N)) *
        Real.sqrt ((D ^ 4 : ℕ) : ℝ) * (1 + Real.log ((D ^ 4 : ℕ) : ℝ)) * r⁻¹ ^ N * B) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ ≤ u ^ (N + 1) * (C * q ^ N * (Real.sqrt q) ^ N * (q ^ N) ^ 2 *
        (1 + 4 * (N : ℝ) * Real.log q) * r⁻¹ ^ N * B) := by
      rw [hsqrt]
      gcongr
    _ = (C * u * B) * (1 + 4 * (N : ℝ) * Real.log q) *
        ((u * Real.sqrt q * q ^ 3) / r) ^ N := by
      rw [div_pow, mul_pow, mul_pow, pow_succ,
        show (q ^ 3) ^ N = (q ^ N) ^ 3 by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      simp only [inv_pow, div_eq_mul_inv]
      ring
    _ = (C * u * B) * (1 + 4 * (N : ℝ) * Real.log q) * rate rho ^ N := by
      rw [zetaMoebiusHeadGrowth_sqrt_cubic_rate hu]
      rfl
    _ ≤ (C * u * B) * ((1 + 4 * Real.log q) * (1 + (N : ℝ))) * rate rho ^ N := by
      gcongr
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    _ ≤ _ := by
      have h0 : 0 ≤ (1 + (N : ℝ)) * rate rho ^ N := by positivity
      calc
        _ = (C * u * B * (1 + 4 * Real.log q)) * ((1 + (N : ℝ)) * rate rho ^ N) := by ring
        _ ≤ (C * u * B * (1 + 4 * Real.log q) + 1) * ((1 + (N : ℝ)) * rate rho ^ N) :=
          mul_le_mul_of_nonneg_right (by linarith) h0
        _ = _ := by ring

/-- Every moving eligible squarefree-divisor family has vanishing
total variation, including all orders of prime intersection together. -/
theorem tendsto_actual_sum_norm (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (T : ℕ → Finset ℕ)
    (hT : ∀ᶠ N in atTop, ∀ P ∈ T N, Squarefree P ∧ P ≠ 1 ∧
      P ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4 ∧
      (∀ a ∈ P.primeFactors, a ∉ zetaRightHalfPrimePatternPrimes rho N)) :
    Tendsto (fun N ↦ ∑ P ∈ T N, ‖actualFibre rho hrho N P‖) atTop (𝓝 0) := by
  obtain ⟨C, _, hb⟩ := exists_actual_sum_norm_bound rho hrho
  exact squeeze_zero' (Eventually.of_forall (fun N ↦ Finset.sum_nonneg (fun P _ ↦ norm_nonneg _)))
    (hT.mono (fun N h ↦ hb N (T N) h)) (tendsto_allowance rho hrho C)

/-- The full class of bounded complex divisor weights is controlled
at once, with arbitrary motion of its finite support and coefficients. -/
theorem tendsto_actual_weighted_fibres (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (T : ℕ → Finset ℕ) (w : ℕ → ℕ → ℂ)
    (hT : ∀ᶠ N in atTop, ∀ P ∈ T N, Squarefree P ∧ P ≠ 1 ∧
      P ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4 ∧
      (∀ a ∈ P.primeFactors, a ∉ zetaRightHalfPrimePatternPrimes rho N))
    (hw : ∀ᶠ N in atTop, ∀ P ∈ T N, ‖w N P‖ ≤ 1) :
    Tendsto (fun N ↦ ∑ P ∈ T N, w N P * actualFibre rho hrho N P) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_actual_sum_norm rho hrho T hT)
  filter_upwards [hw] with N hN
  apply (norm_sum_le _ _).trans
  exact Finset.sum_le_sum (fun P hP ↦ by
    rw [norm_mul]
    simpa using mul_le_mul_of_nonneg_right (hN P hP) (norm_nonneg _))

/-- All bounded divisor-incidence weights act on the literal original
rough squarefree series, keeping every higher prime intersection and
complex phase through the exact arithmetic sum interchange. -/
theorem tendsto_actual_incidence (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (T : ℕ → Finset ℕ) (w : ℕ → ℕ → ℂ)
    (hT : ∀ᶠ N in atTop, ∀ P ∈ T N, Squarefree P ∧ P ≠ 1 ∧
      P ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4 ∧
      (∀ a ∈ P.primeFactors, a ∉ zetaRightHalfPrimePatternPrimes rho N))
    (hw : ∀ᶠ N in atTop, ∀ P ∈ T N, ‖w N P‖ ≤ 1) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑' n,
      weight (T N) (w N) n *
        zetaRoughSquarefreeCoefficient
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          (zetaRightHalfPrimePatternPrimes rho N) n *
        zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n)
      atTop (𝓝 0) := by
  apply (tendsto_actual_weighted_fibres rho hrho T w hT hw).congr'
  filter_upwards [] with N
  rw [(hasSum_weight _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (T N) (w N)
      (by norm_num)).tsum_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun P _ ↦ by unfold actualFibre; ring)

end
end RiemannGaussian.RoughDivisorIncidence
