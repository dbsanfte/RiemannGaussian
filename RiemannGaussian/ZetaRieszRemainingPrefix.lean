/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMixedPrefixTransport
import RiemannGaussian.ZetaRieszPrefixCorrelation

/-!
# The exact surviving distinct-intermediate-prime prefix

Every nonzero prefix label after both paid deletions is a product of
two distinct intermediate primes. Conversely every such product survives.
Unique integer labels retain both cofactor incidences, giving exactly
-log(n)^2/L without a missing diagonal or unordered-pair factor.
-/

namespace RiemannGaussian.ZetaRieszRemainingPrefix
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszCrossCompletion ZetaRieszAnnulusJoint ZetaRieszSemiprimeCompletion
open ZetaRieszMixedPrefix ZetaRieszMixedPrefixTransport
open ZetaRieszPrefixCorrelation

/-- Products of two distinct selected primes, counted by their integer
label once even though the symmetric pair has two cofactor incidences. -/
def pairedLabels (A : Finset ℕ) : Finset ℕ :=
  ((A ×ˢ A).filter (fun ap => ap.1 ≠ ap.2)).image (fun ap => ap.1 * ap.2)

/-- Every nonzero coefficient left after the two proved prefix deletions
is a product of two distinct intermediate primes. This identifies the
actual support rather than imposing another unproved completion mask. -/
theorem remaining_nonzero_mem_paired (u : ℝ) (N n : ℕ)
    (hdiag : n ∉ (intermediatePrimes u N).image (fun p => p ^ 2))
    (hmixed : n ∉ mixedLabels (intermediatePrimes u N) N)
    (hc : prefixCoefficient (intermediatePrimes u N) u N n ≠ 0) :
    n ∈ pairedLabels (intermediatePrimes u N) := by
  obtain ⟨a, ha, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have ha' := (mem_intermediatePrimes u N a).mp ha
  have hpX : n / a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
    by_contra h
    exact hterm (if_neg h)
  rw [if_pos hpX] at hterm
  have hd : a ∣ n ∧ (n / a).Prime := by
    by_contra h
    exact hterm (if_neg h)
  have he : a * (n / a) = n := Nat.mul_div_cancel' hd.1
  have hpN : N ^ 2 < n / a := by
    by_contra h
    apply hmixed
    exact Finset.mem_image.mpr ⟨(a, n / a),
      Finset.mem_product.mpr ⟨ha, Nat.mem_primesLE.mpr ⟨le_of_not_gt h, hd.2⟩⟩, he⟩
  have hpa : a ≠ n / a := by
    intro h
    apply hdiag
    exact Finset.mem_image.mpr ⟨a, ha, by simpa only [← h, pow_two] using he⟩
  exact Finset.mem_image.mpr ⟨(a, n / a), Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨ha, (mem_intermediatePrimes u N (n / a)).mpr ⟨hd.2, hpN, hpX⟩⟩,
      hpa⟩, he⟩

/-- Every distinct selected-prime product belongs to the physical prefix
and avoids both paid classes. Repeated pair incidences remain in its coefficient. -/
theorem pairedLabels_subset_remaining (u : ℝ) (N : ℕ) :
    pairedLabels (intermediatePrimes u N) ⊆
      (Finset.range (((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2) \
        (intermediatePrimes u N).image (fun p => p ^ 2)) \
          mixedLabels (intermediatePrimes u N) N := by
  intro n hn
  obtain ⟨⟨a, p⟩, hap, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hap, hne⟩ := Finset.mem_filter.mp hap
  obtain ⟨ha, hp⟩ := Finset.mem_product.mp hap
  have ha' := (mem_intermediatePrimes u N a).mp ha
  have hp' := (mem_intermediatePrimes u N p).mp hp
  have hX0 : 0 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by positivity
  have hprod := (Nat.mul_lt_mul_of_pos_left hp'.2.2 ha'.1.pos).trans
    (Nat.mul_lt_mul_of_pos_right ha'.2.2 hX0)
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (by simpa only [pow_two] using hprod), ?_⟩, ?_⟩
  · intro hd
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hd
    have hb' := (mem_intermediatePrimes u N b).mp hb
    have had : a ∣ b ^ 2 := he.symm ▸ dvd_mul_right a p
    have hpd : p ∣ b ^ 2 := he.symm ▸ dvd_mul_left p a
    have hab := (Nat.prime_dvd_prime_iff_eq ha'.1 hb'.1).mp (ha'.1.dvd_of_dvd_pow had)
    have hpb := (Nat.prime_dvd_prime_iff_eq hp'.1 hb'.1).mp (hp'.1.dvd_of_dvd_pow hpd)
    exact hne (hab.trans hpb.symm)
  · intro hm
    obtain ⟨⟨b, r⟩, hbr, he⟩ := Finset.mem_image.mp hm
    obtain ⟨_hb, hr⟩ := Finset.mem_product.mp hbr
    obtain ⟨hrN, hr⟩ := Nat.mem_primesLE.mp hr
    apply ZetaRieszCrossSupport.no_small_prime_divisor hp'.1 ha'.1 hp'.2.1 ha'.2.1 hr hrN
    rw [← he]
    exact dvd_mul_left r b

/-- The full remaining physical prefix is exactly its distinct-prime
integer support. All zero labels disappear by proved coefficient identities. -/
theorem remainingPrefix_eq_paired_sum (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    remainingPrefix (intermediatePrimes u N) P u y N =
      ∑ n ∈ pairedLabels (intermediatePrimes u N),
        prefixCoefficient (intermediatePrimes u N) u N n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  symm
  apply Finset.sum_subset (pairedLabels_subset_remaining u N)
  intro n hn hnot
  have hparts := Finset.mem_sdiff.mp hn
  have hdiag := (Finset.mem_sdiff.mp hparts.1).2
  have hz : prefixCoefficient (intermediatePrimes u N) u N n = 0 := by
    by_contra hc
    exact hnot (remaining_nonzero_mem_paired u N n hdiag hparts.2 hc)
  rw [hz, zero_mul]

/-- After paying both deletions, the remaining prefix has the exact
coefficient -log(n)^2/L_N on distinct intermediate-prime products. This
retains the sum of both incidences and does not imply a signed phase bound. -/
theorem remainingPrefix_eq_log_square_sum (P : Polynomial ℂ) (u y : ℝ) (N : ℕ) :
    remainingPrefix (intermediatePrimes u N) P u y N =
      ∑ n ∈ pairedLabels (intermediatePrimes u N),
        ((-(Real.log n) ^ 2 / SquarefreeVaughanLogSource.length u N : ℝ) : ℂ) *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  rw [remainingPrefix_eq_paired_sum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨⟨a, p⟩, hap, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hap, hne⟩ := Finset.mem_filter.mp hap
  obtain ⟨ha, hp⟩ := Finset.mem_product.mp hap
  have ha' := (mem_intermediatePrimes u N a).mp ha
  have hp' := (mem_intermediatePrimes u N p).mp hp
  have hna : ¬ a ∣ p := fun hd => hne ((Nat.prime_dvd_prime_iff_eq ha'.1 hp'.1).mp hd)
  rw [prefixCoefficient_prime_pair_eq_log_square (intermediatePrimes u N) u N
    (fun b hb => ((mem_intermediatePrimes u N b).mp hb).1)
      hp'.1 ha'.1 hna hp ha hp'.2.2 ha'.2.2]

end

end RiemannGaussian.ZetaRieszRemainingPrefix
