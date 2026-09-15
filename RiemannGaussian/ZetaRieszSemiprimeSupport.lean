/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSemiprimeBand

/-!
# Semiprime overlap with every earlier arithmetic deletion

Above the physical prime cutoff, a small-prime/large-prime semiprime
survives all earlier adaptive cuts. Its overlap with earlier deletions
therefore lies in the physical prefix and vanishes independently.
This supplies the support-sensitive transfer needed to combine whole
semiprime cancellation with earlier component estimates without assuming
cancellation for arbitrary masks on an infinite prime sum.
-/

namespace RiemannGaussian.ZetaRieszSemiprimeSupport
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedZero
open ZetaExposedPrimeMoments
open ZetaPrimeCofactorCompletion
open ZetaRieszCompletedCofactor
open ZetaRieszSemiprimePrefix
open ZetaRieszSemiprimePrefixDecay
open ZetaRieszSemiprimeCompletion
open ZetaRieszSemiprimeBand

/-- Literal integer support of the current all-scale adaptive response. -/
def adaptiveBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  if 2 * u ^ 2 < 1 then ZetaRieszLargeSmoothDeletion.largeSmoothResidualBand u N
  else ZetaRieszLargeSmoothDeletion.previousBand u N

/-- The adaptive response is exactly the unchanged signed sum on this support. -/
theorem sum_adaptiveBand_eq_response (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) :
    (∑ n ∈ adaptiveBand u N, SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      ZetaRieszLargeSmoothDeletion.adaptiveSmoothResponse P N y L u := by
  by_cases h : 2 * u ^ 2 < 1
  · simp only [adaptiveBand, ZetaRieszLargeSmoothDeletion.adaptiveSmoothResponse, if_pos h,
      ZetaRieszLargeSmoothDeletion.largeSmoothResidualResponse]
  · simp only [adaptiveBand, ZetaRieszLargeSmoothDeletion.adaptiveSmoothResponse, if_neg h]
    exact ZetaRieszLargeSmoothDeletion.sum_previousBand_eq_response P N y L u

/-- Every retained adaptive label lies in the original band. -/
theorem adaptiveBand_subset (u : ℝ) (N : ℕ) : adaptiveBand u N ⊆ zetaPrimeLogBand N := by
  intro n hn
  by_cases h : 2 * u ^ 2 < 1
  · rw [adaptiveBand, if_pos h] at hn
    exact ZetaRieszLargeSmoothDeletion.previousBand_subset u N (Finset.mem_sdiff.mp hn).1
  · rw [adaptiveBand, if_neg h] at hn
    exact ZetaRieszLargeSmoothDeletion.previousBand_subset u N hn

/-- Removing a prime from a product of two primes leaves a prime. -/
theorem prime_cofactor_of_semiprime {a p b r : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hr : r.Prime) (he : p * a = r * b) : b.Prime := by
  have hd : r ∣ p * a := by rw [he]; exact dvd_mul_right r b
  rcases hr.dvd_mul.mp hd with hdp | hda
  · have hrp := (Nat.prime_dvd_prime_iff_eq hr hp).mp hdp
    subst r
    have hab : a = b := mul_left_cancel₀ hp.ne_zero he
    rwa [← hab]
  · have hra := (Nat.prime_dvd_prime_iff_eq hr ha).mp hda
    subst r
    rw [mul_comm p a] at he
    have hpb : p = b := mul_left_cancel₀ ha.ne_zero he
    rwa [← hpb]

/-- Semiprimes are never removed by the optimized composite-cofactor cut. -/
theorem semiprime_mem_optimizedReducedBand {a p N : ℕ} (ha : a.Prime) (hp : p.Prime)
    (hb : p * a ∈ zetaPrimeLogBand N) (u : ℝ) :
    p * a ∈ ZetaRieszGeneralCofactorTilt.optimizedReducedBand u N := by
  by_cases h : u = Real.exp (-(1 / 2 : ℝ))
  · rw [ZetaRieszGeneralCofactorTilt.optimizedReducedBand, if_pos h]
    apply Finset.mem_filter.mpr
    refine ⟨hb, ?_⟩
    rintro ⟨b, r, _hb1, _hbound, _hsf, hnp, hr, _hcop, he⟩
    exact hnp (prime_cofactor_of_semiprime ha hp hr he)
  · rw [ZetaRieszGeneralCofactorTilt.optimizedReducedBand, if_neg h]
    apply Finset.mem_filter.mpr
    refine ⟨hb, ?_⟩
    rintro ⟨b, r, _hb1, _hbound, _hsf, hnp, hr, _hcop, he⟩
    exact hnp (prime_cofactor_of_semiprime ha hp hr he)

/-- A small-prime/large-prime semiprime satisfies every earlier rough support cut. -/
theorem semiprime_mem_optimizedRoughBand {a p N : ℕ} (ha : a.Prime) (hp : p.Prime)
    (haN : a ≤ N ^ 2) (hNp : N ^ 2 < p) (hb : p * a ∈ zetaPrimeLogBand N) (u : ℝ) :
    p * a ∈ ZetaRieszSmoothCofactor.optimizedRoughBand u N := by
  have hpa : ¬ p ∣ a := by
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq hp ha).mp hd
    omega
  have hsf : Squarefree (p * a) := Nat.squarefree_mul_iff.mpr
    ⟨hp.coprime_iff_not_dvd.mpr hpa, hp.squarefree, ha.squarefree⟩
  exact Finset.mem_filter.mpr ⟨semiprime_mem_optimizedReducedBand ha hp hb u, hsf, p,
    Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_right p a, hsf.ne_zero⟩, hNp⟩

/-- Above the physical prime cutoff a semiprime survives the complete
composite-smooth deletion. Its prime factor cannot be confused with a
different large prime in an alternative factorization. -/
theorem semiprime_mem_compositeResidualBand {a p N : ℕ} {u : ℝ}
    (ha : a.Prime) (hp : p.Prime) (haN : a ≤ N ^ 2) (hNp : N ^ 2 < p)
    (hb : p * a ∈ zetaPrimeLogBand N)
    (hXp : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p) :
    p * a ∈ ZetaRieszCompositeDeletion.compositeResidualBand u N := by
  have hold := semiprime_mem_optimizedRoughBand ha hp haN hNp hb u
  have hprefix : p * a ∈ ZetaRieszPhysicalPrefixDeletion.prefixResidualBand u N := by
    apply Finset.mem_sdiff.mpr
    refine ⟨hold, ?_⟩
    intro hm
    obtain ⟨_hband, b, r, _hsf, _hsmall, hr, hNr, hrX, he⟩ :=
      (ZetaRieszSmoothPrimePrefix.mem_actualProductBand_iff _ u N (p * a)).mp hm
    have hrd : r ∣ p * a := by rw [he]; exact dvd_mul_right r b
    have hrp : r = p := by
      rcases hr.dvd_mul.mp hrd with hrd | hrd
      · exact (Nat.prime_dvd_prime_iff_eq hr hp).mp hrd
      · have hra := (Nat.prime_dvd_prime_iff_eq hr ha).mp hrd
        omega
    omega
  apply Finset.mem_sdiff.mpr
  refine ⟨hprefix, ?_⟩
  intro hm
  obtain ⟨_hband, b, r, _hsf, _hb1, hnp, _hsmall, hr, _hNr, he⟩ :=
    (ZetaRieszCompositeSmooth.mem_compositeSmoothBand_iff _ N (p * a)).mp hm
  exact hnp (prime_cofactor_of_semiprime ha hp hr he)

/-- The smooth factor of a small-prime/large-prime semiprime divides its
small prime. This retains the disjoint prime supports, without a size bound
on the candidate smooth factor. -/
theorem smooth_factor_dvd_small_prime {a p b c N : ℕ} (hp : p.Prime)
    (hNp : N ^ 2 < p) (hb : Squarefree b)
    (hsmall : ∀ r ∈ b.primeFactors, r ≤ N ^ 2) (he : p * a = c * b) : b ∣ a := by
  have hpb : ¬ p ∣ b := by
    intro hd
    exact hNp.not_ge (hsmall p (Nat.mem_primeFactors.mpr ⟨hp, hd, hb.ne_zero⟩))
  have hc : b.Coprime p := (hp.coprime_iff_not_dvd.mpr hpb).symm
  apply hc.dvd_mul_left.mp
  rw [he]
  exact dvd_mul_left b c

/-- Every above-cutoff semiprime survives the entire adaptive carrier once
the quadratic head is below the physical cutoff. All earlier interval
fallbacks are retained, rather than extending their estimates. -/
theorem semiprime_mem_adaptiveBand_above {a p N : ℕ} {u : ℝ}
    (ha : a.Prime) (hp : p.Prime) (haN : a ≤ N ^ 2) (hNp : N ^ 2 < p)
    (hb : p * a ∈ zetaPrimeLogBand N)
    (hNX : N ^ 2 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hXp : (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p) :
    p * a ∈ adaptiveBand u N := by
  have hprev : p * a ∈ ZetaRieszLargeSmoothDeletion.previousBand u N := by
    by_cases h : u < Real.exp (-(1 / 2 : ℝ))
    · rw [ZetaRieszLargeSmoothDeletion.previousBand, if_pos h]
      exact semiprime_mem_compositeResidualBand ha hp haN hNp hb hXp
    · rw [ZetaRieszLargeSmoothDeletion.previousBand, if_neg h]
      exact semiprime_mem_optimizedRoughBand ha hp haN hNp hb u
  by_cases h : 2 * u ^ 2 < 1
  · rw [adaptiveBand, if_pos h]
    apply Finset.mem_sdiff.mpr
    refine ⟨hprev, ?_⟩
    intro hm
    obtain ⟨_hband, b, c, hbs, hsmall, hXb, _hcs, _hrough, he⟩ :=
      (ZetaRieszLargeSmoothClass.mem_largeSmoothFactorBand_iff _ u N (p * a)).mp hm
    have hba := Nat.le_of_dvd ha.pos (smooth_factor_dvd_small_prime hp hNp hbs hsmall he)
    omega
  · simpa only [adaptiveBand, if_neg h] using hprev

/-- The exact damped physical cutoff eventually exceeds the quadratic head. -/
theorem eventually_quadratic_head_lt_physical {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    ∀ᶠ N : ℕ in atTop, N ^ 2 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
  filter_upwards [ZetaRieszExponentialCofactor.eventually_pow_le_cutoff hu hu1 2] with N hN
  nlinarith

/-- Every selected semiprime integer subband has its exact, uniquely
counted prime-pair expansion. The mask is retained before taking any norm. -/
theorem sum_semiprime_filter_eq_pairs (A : Finset ℕ) (P : Polynomial ℂ)
    (N : ℕ) (y L : ℝ) (keep : ℕ → Prop)
    (hA : ∀ a ∈ A, a.Prime ∧ a ≤ N ^ 2) :
    (∑ n ∈ (semiprimeBand A N).filter keep,
      SquarefreeVaughanLogSource.coefficient L n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      ∑ a ∈ A, ∑ p ∈ (Nat.primesLE (2 ^ (32 * N))).filter (fun p => N ^ 2 < p),
        if a * p ∈ zetaPrimeLogBand N ∧ keep (a * p) then
          SquarefreeVaughanLogSource.coefficient L (a * p) *
            zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ) else 0 := by
  have hsets : (semiprimeBand A N).filter keep =
      ZetaRieszSmoothPrimePrefix.productBand keep A
        ((Nat.primesLE (2 ^ (32 * N))).filter (fun p => N ^ 2 < p)) N := by
    ext n
    simp only [semiprimeBand, ZetaRieszSmoothPrimePrefix.productBand,
      Finset.mem_filter, and_true, and_assoc]
  rw [hsets]
  have h := ZetaRieszSmoothPrimePrefix.productBand_sum_eq_pairResponse keep
    A ((Nat.primesLE (2 ^ (32 * N))).filter (fun p => N ^ 2 < p)) P N (N ^ 2) y L
    (fun a ha => (hA a ha).1.squarefree) (fun a ha p hp => by
      have he : p = a := by simpa only [(hA a ha).1.primeFactors, Finset.mem_singleton] using hp
      simpa only [he] using (hA a ha).2)
    (fun p hp => ⟨(Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2,
      (Finset.mem_filter.mp hp).2⟩)
  simpa only [ZetaRieszSmoothPrimeProduct.pairResponse, Nat.mul_comm] using h

/-- The overlap with all earlier deletions is confined to the physical
prime prefix. In particular, no arbitrary mask is imposed on a completed
infinite prime sum to obtain cancellation. -/
theorem semiprime_outside_adaptive_eq_prefix (A : Finset ℕ) (P : Polynomial ℂ)
    (N : ℕ) (y L u : ℝ) (hA : ∀ a ∈ A, a.Prime ∧ a ≤ N ^ 2)
    (hNX : N ^ 2 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) :
    (∑ n ∈ (semiprimeBand A N).filter (fun n => n ∉ adaptiveBand u N),
      SquarefreeVaughanLogSource.coefficient L n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      ∑ a ∈ A, ∑ p ∈ (Nat.primesLE (2 ^ (32 * N))).filter
        (fun p => N ^ 2 < p ∧ p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2),
        (if a * p ∈ zetaPrimeLogBand N ∧ a * p ∉ adaptiveBand u N then
          SquarefreeVaughanLogSource.coefficient L (a * p) else 0) *
            zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) (a * p : ℕ) := by
  convert! (sum_semiprime_filter_eq_pairs A P N y L
    (fun n => n ∉ adaptiveBand u N) hA).trans ?_ using 1
  · congr!
  · apply Finset.sum_congr rfl
    intro a ha
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hNp : N ^ 2 < p
    · by_cases hXp : p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2
      · simp only [hNp, hXp, and_self, if_true, ite_mul, zero_mul]
        congr!
      · have hnot : ¬ (a * p ∈ zetaPrimeLogBand N ∧ a * p ∉ adaptiveBand u N) := by
          rintro ⟨hb, ho⟩
          apply ho
          simpa only [Nat.mul_comm] using semiprime_mem_adaptiveBand_above
            (hA a ha).1 (Nat.mem_primesLE.mp hp).2 (hA a ha).2 hNp
            (by simpa only [Nat.mul_comm] using hb) hNX (lt_of_not_ge hXp)
        simp only [hNp, hXp, and_false, if_true, if_false, if_neg hnot]
    · simp only [hNp, false_and, if_false]

/-- The semiprime overlap with previous deletions vanishes independently
at every source scale below one, even with arbitrary selected small primes. -/
theorem tendsto_semiprime_outside_adaptive (A : ℕ → Finset ℕ) (P : Polynomial ℂ)
    (y : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u < 1)
    (hA : ∀ N a, a ∈ A N → a.Prime ∧ a ≤ N ^ 2) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ (semiprimeBand (A N) N).filter (fun n => n ∉ adaptiveBand u N),
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (𝓝 0) := by
  let Q (N : ℕ) := (Nat.primesLE (2 ^ (32 * N))).filter
    (fun p => N ^ 2 < p ∧ p ≤ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
  have h := tendsto_actual_semiprime_prefix A Q P y hu hu1 hA
    (fun _N _p hp => ⟨(Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2,
      (Finset.mem_filter.mp hp).2.2⟩)
    (fun N a p => a * p ∈ zetaPrimeLogBand N ∧ a * p ∉ adaptiveBand u N)
  apply h.congr'
  filter_upwards [eventually_quadratic_head_lt_physical hu hu1] with N hNX
  rw [semiprime_outside_adaptive_eq_prefix (A N) P N y _ u (hA N) hNX]
  dsimp only [Q]
  congr!

end
end RiemannGaussian.ZetaRieszSemiprimeSupport
