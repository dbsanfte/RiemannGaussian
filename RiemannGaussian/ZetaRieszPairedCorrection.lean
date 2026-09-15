/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRemainingPrefix

/-!
# The whole carrier with its explicit clipped prime-pair correction

Every earlier support cut is discharged for the intermediate-prime
products above the physical cutoff; lower products have original coefficient
zero. The whole refined carrier equals the completed head, unchanged
unpaired subcutoff response and the exact clipped pair sum. Its joint
phase cancellation remains an independent open arithmetic obligation.
-/

namespace RiemannGaussian.ZetaRieszPairedCorrection
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszCrossCompletion ZetaRieszCrossSupport ZetaRieszAnnulusJoint
open ZetaRieszMixedPrefix ZetaRieszMixedPrefixTransport
open ZetaRieszRemainingPrefix ZetaRieszPrefixCorrelation

/-- Every prime divisor of a selected-pair integer is one of its two
intermediate primes, hence is strictly below the physical cutoff. -/
theorem pairedLabels_all_prime_below (u : ℝ) (N : ℕ) {n : ℕ}
    (hn : n ∈ pairedLabels (intermediatePrimes u N)) :
    ∀ r ∈ n.primeFactors, r < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
  obtain ⟨⟨a, p⟩, hap, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hap, _hne⟩ := Finset.mem_filter.mp hap
  obtain ⟨ha, hp⟩ := Finset.mem_product.mp hap
  have ha' := (mem_intermediatePrimes u N a).mp ha
  have hp' := (mem_intermediatePrimes u N p).mp hp
  intro r hr
  have hrp := Nat.prime_of_mem_primeFactors hr
  rcases hrp.dvd_mul.mp (Nat.dvd_of_mem_primeFactors hr) with hd | hd
  · exact ((Nat.prime_dvd_prime_iff_eq hrp ha'.1).mp hd) ▸ ha'.2.2
  · exact ((Nat.prime_dvd_prime_iff_eq hrp hp'.1).mp hd) ▸ hp'.2.2

/-- Every selected distinct-prime product above X_N eventually satisfies
ALL inherited annular cuts. This discharges the original support masks
before the two coefficient incidences are combined. -/
theorem eventually_paired_above_mem_annulus {u : ℝ} (hu : 1 / 2 ≤ u)
    (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, ∀ n ∈ pairedLabels (intermediatePrimes u N),
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < n →
      n ∈ ZetaRieszPhysicalAnnulus.annulusBand u N := by
  filter_upwards [eventually_physical_window hu huh] with N hwindow
  intro n hn hnX
  have hsub := pairedLabels_subset_remaining u N hn
  have hnXX := Finset.mem_range.mp (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hsub).1).1
  obtain ⟨hb, hlo, hhi⟩ := hwindow n hnX hnXX
  have hsmall := pairedLabels_all_prime_below u N hn
  have hext : ZetaRieszExtremePrimeCount.extremePrimes u N n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    obtain ⟨hr, hXr⟩ := Finset.mem_filter.mp hr
    exact (hsmall r hr).not_ge hXr
  obtain ⟨⟨a, p⟩, hap, he⟩ := Finset.mem_image.mp hn
  obtain ⟨hap, hne⟩ := Finset.mem_filter.mp hap
  obtain ⟨ha, hp⟩ := Finset.mem_product.mp hap
  have ha' := (mem_intermediatePrimes u N a).mp ha
  have hp' := (mem_intermediatePrimes u N p).mp hp
  have hna : ¬ a ∣ p := fun hd => hne ((Nat.prime_dvd_prime_iff_eq ha'.1 hp'.1).mp hd)
  have hres := rough_semiprime_mem_residual (u := u) hp'.1 ha'.1 hp'.2.1 ha'.2.1 hna
    (show a * p ∈ zetaPrimeLogBand N by simpa only [he] using hb)
  rw [he] at hres
  have hnarrow := ZetaRieszNarrowCarrier.mem_residualBand.mpr ⟨hres, hlo, hhi⟩
  have hfour : n ∈ ZetaRieszFourExtremeDeletion.fourResidualBand u N := by
    unfold ZetaRieszFourExtremeDeletion.fourResidualBand
    split_ifs
    · exact Finset.mem_filter.mpr ⟨hnarrow, by simp [hext]⟩
    · exact hnarrow
  apply (ZetaRieszPhysicalAnnulus.mem_annulusBand huh).mpr
  refine ⟨?_, hnX, hnXX⟩
  rw [ZetaRieszLowerDegreeDeletion.degreeResidualBand, if_pos huh]
  exact Finset.mem_filter.mpr ⟨hfour, by simp [hext]⟩

/-- The original all-subcutoff carrier with just the selected distinct-prime
products removed. Every older arithmetic mask is preserved. -/
def unpairedSubcutoffResponse (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ ((ZetaRieszPhysicalAnnulus.annulusBand u N).filter (fun n =>
      ∀ p ∈ n.primeFactors, p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)) \
        pairedLabels (intermediatePrimes u N),
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The actual all-subcutoff response splits into its unpaired part and
the complete selected-pair coefficient sum. Missing lower-cutoff labels
have coefficient exactly zero; no phase or mask is assumed away. -/
theorem eventually_subcutoff_eq_unpaired_add_pairs (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, subcutoffResponse P u y N =
      unpairedSubcutoffResponse P u y N +
        ∑ n ∈ pairedLabels (intermediatePrimes u N),
          SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
            zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  filter_upwards [eventually_paired_above_mem_annulus hu huh] with N hmem
  let B := (ZetaRieszPhysicalAnnulus.annulusBand u N).filter (fun n =>
    ∀ p ∈ n.primeFactors, p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
  let f := fun n => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n
  have he : ∑ n ∈ B ∩ pairedLabels (intermediatePrimes u N), f n =
      ∑ n ∈ pairedLabels (intermediatePrimes u N), f n := by
    apply Finset.sum_subset Finset.inter_subset_right
    intro n hn hnot
    have hle : n ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
      by_contra hh
      exact hnot (Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr
        ⟨hmem n hn (lt_of_not_ge hh), pairedLabels_all_prime_below u N hn⟩, hn⟩)
    dsimp only [f]
    rw [ZetaRieszPhysicalProductBounds.coefficient_eq_zero_below_physical hle, zero_mul]
  have hs := Finset.sum_inter_add_sum_sdiff B (pairedLabels (intermediatePrimes u N)) f
  rw [he] at hs
  exact hs.symm.trans (add_comm _ _)

/-- The exact combined two-prime correction at every selected integer
label is a clipped logarithm, including products below X_N. -/
theorem paired_coefficient_correction (u : ℝ) (N : ℕ) {n : ℕ}
    (hn : n ∈ pairedLabels (intermediatePrimes u N)) :
    SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n -
      prefixCoefficient (intermediatePrimes u N) u N n =
      ((Real.log n * min 1 (Real.log n / SquarefreeVaughanLogSource.length u N) : ℝ) : ℂ) := by
  obtain ⟨⟨a, p⟩, hap, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hap, hne⟩ := Finset.mem_filter.mp hap
  obtain ⟨ha, hp⟩ := Finset.mem_product.mp hap
  have ha' := (mem_intermediatePrimes u N a).mp ha
  have hp' := (mem_intermediatePrimes u N p).mp hp
  exact coefficient_sub_prefix_eq_clipped_log (intermediatePrimes u N) u N
    (fun b hb => ((mem_intermediatePrimes u N b).mp hb).1)
    hp'.1 ha'.1 (fun hd => hne ((Nat.prime_dvd_prime_iff_eq ha'.1 hp'.1).mp hd))
    hp ha hp'.2.2 ha'.2.2

/-- The full two-prime correction retains every product phase after
combining both prefix incidences with the original Riesz coefficient. -/
def clippedPairResponse (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ pairedLabels (intermediatePrimes u N),
    ((Real.log n * min 1 (Real.log n / SquarefreeVaughanLogSource.length u N) : ℝ) : ℂ) *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The WHOLE refined carrier is now the completed head, unchanged
unpaired subcutoff part, and one explicit clipped two-prime response.
This equality keeps the sign correlations between all three components. -/
theorem eventually_refinedJoint_eq_clipped_split (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 ≤ u) (huh : u < Real.exp (-(2 / 3 : ℝ))) :
    ∀ᶠ N : ℕ in atTop, refinedJoint P u y N =
      unpairedSubcutoffResponse P u y N +
        ZetaPrimeCofactorCompletion.completedCofactorHead (intermediatePrimes u N) P N
          (3 / 2 + Complex.I * y) (SquarefreeVaughanLogSource.length u N) +
        clippedPairResponse P u y N := by
  filter_upwards [eventually_subcutoff_eq_unpaired_add_pairs P y hu huh] with N hs
  have hpair : (∑ n ∈ pairedLabels (intermediatePrimes u N),
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) -
      remainingPrefix (intermediatePrimes u N) P u y N = clippedPairResponse P u y N := by
    rw [remainingPrefix_eq_paired_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← sub_mul, paired_coefficient_correction u N hn]
  unfold refinedJoint
  rw [hs, ← hpair]
  ring

end

end RiemannGaussian.ZetaRieszPairedCorrection
