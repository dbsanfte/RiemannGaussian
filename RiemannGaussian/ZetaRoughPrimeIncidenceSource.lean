/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRoughPrimeIncidence
import RiemannGaussian.ZetaRoughSquarefreeFactorGeometry
import RiemannGaussian.ZetaArithmeticSmallProduct

/-!
# Removing the unbalanced semiprime arm by an exact incidence subtraction

Subtract the independently negligible incidence sum over all retained
primes through the original divisor cutoff. Every unbalanced semiprime
then vanishes coefficientwise. The remaining weight is exactly one minus
the number of marked prime factors; it is retained on every intersection.
Small products have a separate geometric bound, leaving the full source
on integers admitting two factors beyond the original cutoff.
-/

open Complex Filter Topology
open scoped Classical

namespace RiemannGaussian.RoughPrimeIncidence
noncomputable section

/-- All primes through the divisor cutoff which have not already
been excluded from the original rough carrier. -/
def cutoffPrimes (D : ℕ) (S : Finset ℕ) : Finset ℕ := zetaSquarePrimesThrough D \ S

/-- The marked family contains exactly the retained primes through
the original divisor cutoff. -/
theorem mem_cutoffPrimes {D a : ℕ} {S : Finset ℕ} :
    a ∈ cutoffPrimes D S ↔ a.Prime ∧ a ≤ D ∧ a ∉ S := by
  simp only [cutoffPrimes, Finset.mem_sdiff, zetaSquarePrimesThrough, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨_, haD⟩, ha⟩, haS⟩
    exact ⟨ha, haD, haS⟩
  · rintro ⟨ha, haD, haS⟩
    exact ⟨⟨⟨ha.pos, haD⟩, ha⟩, haS⟩

/-- The complete family has at most one mark per positive integer
through the cutoff; no prime-counting estimate is needed. -/
theorem card_cutoffPrimes_le (D : ℕ) (S : Finset ℕ) : (cutoffPrimes D S).card ≤ D := by
  have hsub : cutoffPrimes D S ⊆ Finset.Icc 1 D := fun a ha ↦
    Finset.mem_Icc.mpr ⟨(mem_cutoffPrimes.mp ha).1.pos, (mem_cutoffPrimes.mp ha).2.1⟩
  simpa using Finset.card_le_card hsub

/-- The exact retained coefficient after subtracting all single
prime incidences. A term with `k` marked primes keeps weight `1-k`. -/
def compensatedCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  (1 - weight (cutoffPrimes D S) (fun _ ↦ 1) n) * zetaRoughSquarefreeCoefficient D S n

/-- Incidence subtraction is an exact coefficient identity, keeping
every multiple mark rather than replacing the sum by a union indicator. -/
theorem compensatedCoefficient_eq_sub (D : ℕ) (S : Finset ℕ) (n : ℕ) :
    compensatedCoefficient D S n = zetaRoughSquarefreeCoefficient D S n -
      ∑ a ∈ cutoffPrimes D S, fibreCoefficient D S a n := by
  unfold compensatedCoefficient weight
  rw [sub_mul, one_mul, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl (fun a _ ↦ by
    by_cases ha : a ∣ n <;> simp [fibreCoefficient, ha])

/-- On an unbalanced semiprime the smaller prime is the unique
marked prime. This is an exact divisibility statement, independent of phases. -/
theorem weight_unbalanced_semiprime {D p q : ℕ} (S : Finset ℕ)
    (hp : p.Prime) (hq : q.Prime) (hDp : D < p) (hqD : q ≤ D) (hqS : q ∉ S) :
    weight (cutoffPrimes D S) (fun _ ↦ 1) (p * q) = 1 := by
  have hqT : q ∈ cutoffPrimes D S := mem_cutoffPrimes.mpr ⟨hq, hqD, hqS⟩
  unfold weight
  rw [Finset.sum_eq_single q]
  · simp
  · intro a ha haq
    have haspec := mem_cutoffPrimes.mp ha
    have hnot : ¬a ∣ p * q := by
      intro hd
      rcases haspec.1.dvd_mul.mp hd with hap | haq'
      · have he := (Nat.prime_dvd_prime_iff_eq haspec.1 hp).mp hap
        omega
      · exact haq ((Nat.prime_dvd_prime_iff_eq haspec.1 hq).mp haq')
    simp [hnot]
  · exact fun h ↦ (h hqT).elim

/-- The entire unbalanced semiprime arm vanishes after the exact
incidence subtraction, with no estimate for its separate signed sum. -/
theorem compensatedCoefficient_unbalanced_semiprime_zero {D p q : ℕ} (S : Finset ℕ)
    (hp : p.Prime) (hq : q.Prime) (hDp : D < p) (hqD : q ≤ D) :
    compensatedCoefficient D S (p * q) = 0 := by
  by_cases hqS : q ∈ S
  · have he : ∃ a ∈ S, a ∣ p * q := ⟨q, hqS, dvd_mul_left q p⟩
    simp [compensatedCoefficient, zetaRoughSquarefreeCoefficient, he]
  · simp [compensatedCoefficient, weight_unbalanced_semiprime S hp hq hDp hqD hqS]

/-- Above the cubic cutoff, every nonzero compensated coefficient
admits two factors strictly beyond the original divisor cutoff. -/
theorem compensatedCoefficient_balanced (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) {n : ℕ} (hn : D ^ 3 < n)
    (hc : compensatedCoefficient D S n ≠ 0) : zetaBalancedFactorization D n := by
  have hA : zetaRoughSquarefreeCoefficient D S n ≠ 0 := by
    intro h
    exact hc (by simp [compensatedCoefficient, h])
  have hrough : ¬∃ a ∈ S, a ∣ n := by
    intro h
    exact hA (by simp [zetaRoughSquarefreeCoefficient, h])
  have hsf : Squarefree n := by
    by_contra h
    exact hA (by simp [zetaRoughSquarefreeCoefficient, hrough, zetaSquarefreeCoefficient, h])
  have hcomp : ¬n.Prime := by
    intro hp
    exact hA (by simp [zetaRoughSquarefreeCoefficient, hrough, zetaSquarefreeCoefficient, hsf,
      zetaMoebiusSievedPrimeCoefficient, zetaMoebiusDistinctPrimeCoefficient, hp.primeFactors])
  rcases zetaRoughSquarefreeCoefficient_balanced_or_semiprime D hD S hS hn hsf hcomp hA with h | h
  · exact h
  · obtain ⟨p, q, hp, hq, hqD, hDp, rfl, _⟩ := h
    exact (hc (compensatedCoefficient_unbalanced_semiprime_zero S hp hq hDp hqD)).elim

/-- The compensated coefficient has a genuine convergent series,
equal to the original source minus the complete marked-prime responses. -/
theorem hasSum_compensated (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ compensatedCoefficient D S n * zetaPrimeFilterKernel p N s n)
      (zetaRoughSquarefreeFilter p D S N s -
        ∑ a ∈ cutoffPrimes D S, fibre p D S N s a) := by
  have h := (summable_zetaRoughSquarefreeFilter p D N hD S hS hs).hasSum.sub
    (hasSum_weight p D N hD S hS (cutoffPrimes D S) (fun _ ↦ 1) hs)
  simp only [one_mul] at h
  apply h.congr_fun
  intro n
  unfold compensatedCoefficient
  ring

private theorem cutoffPrimes_eligible (rho : NontrivialZetaZero)
    (N : ℕ) :
    ∀ a ∈ cutoffPrimes
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N), a.Prime ∧
      a ≤ (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N) ^ 4 ∧
      a ∉ zetaRightHalfPrimePatternPrimes rho N := by
  intro a ha
  obtain ⟨hap, haD, haS⟩ := mem_cutoffPrimes.mp ha
  refine ⟨hap, haD.trans ?_, haS⟩
  exact Nat.le_self_pow (by omega) _

/-- Subtracting the entire cutoff-prime incidence family retains
the original negative-multiplicity source, with no new arithmetic premise. -/
theorem tendsto_compensated_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (fun N ↦ ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑' n,
      compensatedCoefficient
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfPrimePatternPrimes rho N) n *
        zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n)
      atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  let T := fun N ↦ cutoffPrimes
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (zetaRightHalfPrimePatternPrimes rho N)
  have hi := tendsto_actual_incidence rho hrho T (fun _ _ ↦ 1)
    (Eventually.of_forall (cutoffPrimes_eligible rho)) (by simp)
  have h := (tendsto_zetaRightHalfRoughSquarefreeFilter rho hrho).sub hi
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [(hasSum_compensated _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (by norm_num)).tsum_eq,
    (hasSum_weight _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
      (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (T N) (fun _ ↦ 1)
      (by norm_num)).tsum_eq]
  simp only [one_mul]
  ring

/-- Incidence subtraction also commutes with every finite integer
window, with all marked-prime intersections counted exactly. -/
theorem sum_compensated_eq (D : ℕ) (S T : Finset ℕ) (F : ℕ → ℂ) :
    (∑ n ∈ T, compensatedCoefficient D S n * F n) =
      (∑ n ∈ T, zetaRoughSquarefreeCoefficient D S n * F n) -
        ∑ a ∈ cutoffPrimes D S, ∑ n ∈ T, fibreCoefficient D S a n * F n := by
  simp only [compensatedCoefficient_eq_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The complete compensated contribution through the cubic product
cutoff, with the original complex kernel and normalization. -/
def smallPart (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    ∑ n ∈ Finset.Iic (zetaMoebiusGeometricCutoff
      (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N ^ 3),
      compensatedCoefficient
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfPrimePatternPrimes rho N) n *
        zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n

private theorem headGrowth_le {u : ℝ} (hu : 1 / 2 < u) : zetaMoebiusHeadGrowth u ≤ 6 / 5 := by
  have hu0 : 0 < u := by linarith
  have hs : 25 / 36 < Real.sqrt u := by
    nlinarith [Real.sq_sqrt hu0.le, Real.sqrt_nonneg u]
  have ht : 5 / 6 < Real.sqrt (Real.sqrt u) := by
    nlinarith [Real.sq_sqrt (Real.sqrt_nonneg u), Real.sqrt_nonneg (Real.sqrt u)]
  unfold zetaMoebiusHeadGrowth
  rw [← one_div]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hu0))).mpr
  linarith

/-- The extra incidence multiplicity on small products has a fully
paid geometric allowance. All original terms through `D_N^3` are covered. -/
theorem norm_smallPart_le (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    ‖smallPart rho hrho N‖ ≤
      2 * zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho) * (9 / 10 : ℝ) ^ N := by
  let u : ℝ := 3 / 2 - rho.1.re
  let q := zetaMoebiusHeadGrowth u
  let D := zetaMoebiusGeometricCutoff q N
  let S := zetaRightHalfPrimePatternPrimes rho N
  let p := zetaRightHalfPoleJetFilter rho hrho
  let C := zetaArithmeticSmallProductConstant p
  have hu : 1 / 2 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have hq1 : 1 ≤ q := (one_lt_zetaMoebiusHeadGrowth (by linarith) hu1).le
  have hq0 : 0 ≤ q := zero_le_one.trans hq1
  have hq6 : q ≤ 6 / 5 := headGrowth_le hu
  have hC : 0 ≤ C := zetaArithmeticSmallProductConstant_nonneg p
  have hD : (D : ℝ) ≤ q ^ N := Nat.floor_le (pow_nonneg hq0 N)
  have hD' : 1 + (D : ℝ) ≤ 2 * q ^ N := by nlinarith [one_le_pow₀ hq1 (n := N)]
  have hcard : ((cutoffPrimes D S).card : ℝ) ≤ D := by exact_mod_cast card_cutoffPrimes_le D S
  have hbase := norm_normalized_sum_zetaArithmetic_cubic_product_le
    (zetaRoughSquarefreeCoefficient D S) (norm_zetaRoughSquarefreeCoefficient_le D S)
    p N rho.1.im hu hu1 (Finset.Iic (D ^ 3)) (fun _ hn ↦ Finset.mem_Iic.mp hn)
  have hmark (a : ℕ) := norm_normalized_sum_zetaArithmetic_cubic_product_le
    (fibreCoefficient D S a) (fun n ↦ by
      by_cases hn : a ∣ n
      · simpa only [fibreCoefficient, if_pos hn] using norm_zetaRoughSquarefreeCoefficient_le D S n
      · simpa only [fibreCoefficient, if_neg hn, norm_zero] using zetaMoebiusLogMajorant_nonneg n)
    p N rho.1.im hu hu1 (Finset.Iic (D ^ 3)) (fun _ hn ↦ Finset.mem_Iic.mp hn)
  rw [smallPart, sum_compensated_eq, mul_sub, Finset.mul_sum (cutoffPrimes D S)]
  apply (norm_sub_le _ _).trans
  calc
    _ ≤ C * (3 / 4 : ℝ) ^ N + ∑ _a ∈ cutoffPrimes D S, C * (3 / 4 : ℝ) ^ N :=
      add_le_add hbase ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ ↦ hmark a)))
    _ = (1 + ((cutoffPrimes D S).card : ℝ)) * C * (3 / 4 : ℝ) ^ N := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (1 + (D : ℝ)) * C * (3 / 4 : ℝ) ^ N := by gcongr
    _ ≤ (2 * q ^ N) * C * (3 / 4 : ℝ) ^ N := by gcongr
    _ = (2 * C) * (q * (3 / 4)) ^ N := by rw [mul_pow]; ring
    _ ≤ (2 * C) * (9 / 10 : ℝ) ^ N := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply pow_le_pow_left₀ (by positivity)
      nlinarith

/-- The complete small-product allowance vanishes independently of
the zero-source limit, despite the extra prime-incidence multiplicity. -/
theorem tendsto_smallPart (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (smallPart rho hrho) atTop (𝓝 0) := by
  apply squeeze_zero_norm (norm_smallPart_le rho hrho)
  simpa only [mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 9 / 10)
      (by norm_num : (9 / 10 : ℝ) < 1)).const_mul
        (2 * zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho))

/-- The remaining coefficient is supported on large products with
two factors beyond the original cutoff, with weight `1-k` unchanged. -/
def balancedCoefficient (D : ℕ) (S : Finset ℕ) (n : ℕ) : ℂ :=
  if D ^ 3 < n ∧ zetaBalancedFactorization D n then compensatedCoefficient D S n else 0

/-- The compensated carrier partitions exactly into its finite
small-product part and its balanced remainder. -/
theorem compensatedCoefficient_partition (D : ℕ) (hD : 1 ≤ D) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a.Prime) (n : ℕ) :
    compensatedCoefficient D S n =
      (if n ≤ D ^ 3 then compensatedCoefficient D S n else 0) + balancedCoefficient D S n := by
  by_cases hn : n ≤ D ^ 3
  · simp [balancedCoefficient, hn, Nat.not_lt.mpr hn]
  · have hn' := Nat.lt_of_not_ge hn
    by_cases hbal : zetaBalancedFactorization D n
    · simp [balancedCoefficient, hn, hn', hbal]
    · have hc : compensatedCoefficient D S n = 0 := by
        by_contra hc
        exact hbal (compensatedCoefficient_balanced D hD S hS hn' hc)
      simp [balancedCoefficient, hn, hbal, hc]

/-- The complete balanced series converges and equals the original
carrier minus the full incidence subtraction and the finite small head. -/
theorem hasSum_balanced (p : Polynomial ℂ) (D N : ℕ) (hD : 1 ≤ D)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a.Prime) {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n ↦ balancedCoefficient D S n * zetaPrimeFilterKernel p N s n)
      ((zetaRoughSquarefreeFilter p D S N s - ∑ a ∈ cutoffPrimes D S, fibre p D S N s a) -
        ∑ n ∈ Finset.Iic (D ^ 3), compensatedCoefficient D S n * zetaPrimeFilterKernel p N s n) := by
  have hsmall : HasSum (fun n : ℕ ↦ if n ≤ D ^ 3 then
      compensatedCoefficient D S n * zetaPrimeFilterKernel p N s n else 0)
      (∑ n ∈ Finset.Iic (D ^ 3), if n ≤ D ^ 3 then
        compensatedCoefficient D S n * zetaPrimeFilterKernel p N s n else 0) :=
    hasSum_sum_of_ne_finset_zero (s := Finset.Iic (D ^ 3)) (by
      intro n hn
      have hn' : ¬n ≤ D ^ 3 := fun h ↦ hn (Finset.mem_Iic.mpr h)
      simp [hn'])
  have he : (∑ n ∈ Finset.Iic (D ^ 3), if n ≤ D ^ 3 then
      compensatedCoefficient D S n * zetaPrimeFilterKernel p N s n else 0) =
        ∑ n ∈ Finset.Iic (D ^ 3), compensatedCoefficient D S n * zetaPrimeFilterKernel p N s n :=
    Finset.sum_congr rfl (fun n hn ↦ if_pos (Finset.mem_Iic.mp hn))
  rw [he] at hsmall
  apply ((hasSum_compensated p D N hD S hS hs).sub hsmall).congr_fun
  intro n
  by_cases hn : n ≤ D ^ 3
  · simp [hn, balancedCoefficient, Nat.not_lt.mpr hn]
  · have hp := compensatedCoefficient_partition D hD S hS n
    simp only [if_neg hn, zero_add] at hp
    simp [hn, hp]

/-- The actual source-normalized balanced response. It keeps the
exact incidence correction on every surviving multiple-prime intersection. -/
def balancedPart (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) * ∑' n,
    balancedCoefficient
      (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
      (zetaRightHalfPrimePatternPrimes rho N) n *
      zetaPrimeFilterKernel (zetaRightHalfPoleJetFilter rho hrho) N (3 / 2 + I * rho.1.im) n

/-- The complete complex source is retained before taking real parts:
the new balanced response is exactly the old rough carrier minus its
marked-prime response and the complete compensated small-product head. -/
theorem balancedPart_eq_source_sub_corrections (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) (N : ℕ) :
    balancedPart rho hrho N =
      ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
        zetaRoughSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
          (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
          (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im) -
      (∑ a ∈ cutoffPrimes
        (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
        (zetaRightHalfPrimePatternPrimes rho N), actualFibre rho hrho N a) - smallPart rho hrho N := by
  rw [balancedPart, (hasSum_balanced _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (by norm_num)).tsum_eq,
    mul_sub, mul_sub, Finset.mul_sum (cutoffPrimes _ _)]
  rfl

/-- Both subtraction errors have independent explicit geometric
allowances at every moment order. The identity above retains their signs. -/
theorem exists_balanced_error_bound (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ‖balancedPart rho hrho N -
        ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
          zetaRoughSquarefreeFilter (zetaRightHalfPoleJetFilter rho hrho)
            (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
            (zetaRightHalfPrimePatternPrimes rho N) N (3 / 2 + I * rho.1.im)‖ ≤
        C * (1 + (N : ℝ)) * rate rho ^ N +
          2 * zetaArithmeticSmallProductConstant (zetaRightHalfPoleJetFilter rho hrho) * (9 / 10 : ℝ) ^ N := by
  obtain ⟨C, hC, hb⟩ := exists_actual_sum_norm_bound rho hrho
  refine ⟨C, hC, fun N ↦ ?_⟩
  let T := cutoffPrimes
    (zetaMoebiusGeometricCutoff (zetaMoebiusHeadGrowth (3 / 2 - rho.1.re)) N)
    (zetaRightHalfPrimePatternPrimes rho N)
  rw [balancedPart_eq_source_sub_corrections]
  calc
    _ = ‖-(∑ a ∈ T, actualFibre rho hrho N a) - smallPart rho hrho N‖ := by congr 1; ring
    _ ≤ ‖∑ a ∈ T, actualFibre rho hrho N a‖ + ‖smallPart rho hrho N‖ := by
      simpa only [norm_neg] using norm_sub_le (-(∑ a ∈ T, actualFibre rho hrho N a)) (smallPart rho hrho N)
    _ ≤ _ := add_le_add ((norm_sum_le _ _).trans (hb N T (cutoffPrimes_eligible rho N)))
      (norm_smallPart_le rho hrho N)

/-- The full negative-multiplicity source is retained on the balanced
arm alone after a proved negligible subtraction and small-product error.
This does not assert decay of the old unbalanced arm by itself. -/
theorem tendsto_balanced_source (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (balancedPart rho hrho) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have h := (tendsto_compensated_source rho hrho).sub (tendsto_smallPart rho hrho)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  rw [balancedPart, (hasSum_balanced _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
    (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (by norm_num)).tsum_eq,
    (hasSum_compensated _ _ N (zetaRightHalfPoleJetCutoff_pos rho hrho N) _
      (fun a ha ↦ (zetaRightHalfPrimePatternPrimes_eligible rho N a ha).1) (by norm_num)).tsum_eq]
  unfold smallPart
  ring

/-- Only a fixed strict signed margin on a cofinal subsequence of
the compensated balanced response remains sufficient. The arithmetic
inequality in the last premise is the open goal, not an established bound. -/
theorem false_of_cofinal_balanced_bound (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∃ᶠ N in atTop, -1 + ε ≤ (balancedPart rho hrho N).re) : False := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_balanced_source rho hrho)
  have hb := ge_of_tendsto_of_frequently h hbound
  simp only [Complex.neg_re, Complex.natCast_re] at hb
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

end
end RiemannGaussian.RoughPrimeIncidence
