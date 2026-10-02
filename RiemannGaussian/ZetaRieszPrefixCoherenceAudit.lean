/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRejoinedPhaseFloor

/-!
# The coherent channel in the existing signed prefix energy

These are lower bounds on the EXISTING energy and one-sided cost, not a
new carrier or a bound for the arithmetic floor. Every actual label has
sharp prefix one at cutoff one. A rough population has the same prefix
through every cutoff below its least prime. Thus bin occupancy cannot
justify replacing this common signed moment by a diagonal label norm.

The weight may include the exact phase, allocation, masks and funding.
No claim is made that its common moment is large for the actual carrier.
The one-sided cost is only a sufficient floor criterion; a lower bound
on this cost does not refute the independent floor itself.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ArithmeticFunction.Moebius
namespace RiemannGaussian.ZetaRieszPrefixCoherenceAudit
open Real ZetaRieszCofactorPhaseEnergy ZetaRieszRejoinedPhaseFloor

/-- Cutoff one is coherent on actual integers, including every masked
squarefree population. No squarefreeness assumption is needed here. -/
theorem sharp_one (n : ℕ) : sharp 1 n = 1 := by
  simp [sharp]

/-- The phase remains in one signed total-label moment. -/
theorem correlation_one (S : Finset ℕ) (w : ℕ → ℝ) :
    correlation S w 1 = ∑ n ∈ S, w n := by
  simp [correlation, sharp_one]

/-- Before the least prime, the only divisor in the literal prefix is one. -/
theorem sharp_eq_one_of_lt_minFac {k n : ℕ} (hk : 0 < k)
    (hrough : k < n.minFac) : sharp k n = 1 := by
  have hterm (d : ℕ) (hd : d ∈ Finset.Icc 1 k) :
      (if d ∣ n then (μ d : ℝ) else 0) = if d = 1 then 1 else 0 := by
    by_cases hd1 : d = 1
    · simp [hd1]
    · have hnot : ¬d ∣ n := by
        intro hdn
        have hlow : 2 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
        have hmin := Nat.minFac_le_of_dvd hlow hdn
        have := (Finset.mem_Icc.mp hd).2
        omega
      simp [hd1, hnot]
  rw [sharp, Finset.sum_congr rfl hterm]
  simp [Finset.mem_Icc, Nat.ne_of_gt hk]

/-- This is the same signed weight sum on every rough-prefix cutoff,
not an average or a completed cofactor model. -/
theorem correlation_eq_of_rough (S : Finset ℕ) (w : ℕ → ℝ) {k : ℕ}
    (hk : 0 < k) (hrough : ∀ n ∈ S, k < n.minFac) :
    correlation S w k = ∑ n ∈ S, w n := by
  unfold correlation
  apply Finset.sum_congr rfl
  intro n hn
  rw [sharp_eq_one_of_lt_minFac hk (hrough n hn), mul_one]

/-- The original energy contains the full coherent prefix channel.
All phases and cross-population signs remain inside the common moment. -/
theorem phaseEnergy_coherent_lower (R Q : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (hrough : ∀ n ∈ S, Q < n.minFac) :
    (∑ n ∈ S, w n)^2 *
        (∑ k ∈ (activeCutoffs R f).filter (fun k => k ≤ Q), 1/(k : ℝ)) ≤
      phaseEnergy R S w f := by
  calc
    _ = ∑ k ∈ (activeCutoffs R f).filter (fun k => k ≤ Q),
          correlation S w k^2/(k : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hact := (Finset.mem_filter.mp hk).1
      have hk0 := (Finset.mem_Icc.mp (Finset.mem_filter.mp hact).1).1
      have hkQ := (Finset.mem_filter.mp hk).2
      rw [correlation_eq_of_rough S w hk0
        (fun n hn => lt_of_le_of_lt hkQ (hrough n hn))]
      ring
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun _ _ _ =>
        div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

/-- Even without a common roughness threshold, the actual first prefix
must be retained whenever the chosen profile is active there. -/
theorem phaseEnergy_one_lower (R : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (hactive : 1 ∈ activeCutoffs R f) :
    (∑ n ∈ S, w n)^2 ≤ phaseEnergy R S w f := by
  have h := Finset.single_le_sum
    (fun k (_ : k ∈ activeCutoffs R f) =>
      div_nonneg (sq_nonneg (correlation S w k)) (Nat.cast_nonneg k)) hactive
  simpa only [correlation_one, Nat.cast_one, div_one, phaseEnergy] using h

/-- A diagonal label-energy estimate valid for every weight already
needs coefficient at least the population size on this coherent channel.
This does NOT assert coherence of the carrier's specific arithmetic weights. -/
theorem diagonal_coefficient_lower (R : ℕ) (S : Finset ℕ) (f : ℕ → ℝ)
    (hS : S.Nonempty) (hactive : 1 ∈ activeCutoffs R f) (C : ℝ)
    (hbound : ∀ w : ℕ → ℝ,
      phaseEnergy R S w f ≤ C * (∑ n ∈ S, w n^2)) :
    (S.card : ℝ) ≤ C := by
  have h := (phaseEnergy_one_lower R S (fun _ => 1) f hactive).trans
    (hbound (fun _ => 1))
  simp only [Finset.sum_const, one_pow, nsmul_eq_mul, mul_one] at h
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  exact (mul_le_mul_iff_right₀ hcard).mp (by nlinarith only [h])

/-- If the complete first increment is adverse, the existing one-sided
cost must pay that full signed moment. No label or bin is clipped separately. -/
theorem negativeCost_one_lower (R : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (hactive : 1 ∈ activeCutoffs R f)
    (hadverse : (∑ n ∈ S, w n) * (f 1 - f 2) < 0) :
    -(∑ n ∈ S, w n) * (f 1 - f 2) ≤ negativeCost R S w f := by
  have hmem : 1 ∈ negativeCutoffs R S w f := by
    exact Finset.mem_filter.mpr ⟨hactive, by simpa only [correlation_one] using hadverse⟩
  have hE := Finset.single_le_sum
    (fun k (_ : k ∈ negativeCutoffs R S w f) =>
      div_nonneg (sq_nonneg (correlation S w k)) (Nat.cast_nonneg k)) hmem
  have hP := Finset.single_le_sum
    (fun k (_ : k ∈ negativeCutoffs R S w f) =>
      mul_nonneg (Nat.cast_nonneg k) (sq_nonneg (f k - f (k+1)))) hmem
  simp only [correlation_one, Nat.cast_one, div_one, one_mul] at hE hP
  have hsq := mul_le_mul hE hP (sq_nonneg (f 1 - f 2))
    (Finset.sum_nonneg (fun k _ =>
      div_nonneg (sq_nonneg (correlation S w k)) (Nat.cast_nonneg k)))
  unfold negativeCost
  apply (sq_le_sq₀ (by nlinarith only [hadverse]) (sqrt_nonneg _)).mp
  rw [sq_sqrt (by positivity)]
  nlinarith only [hsq]

/-- The coherent channel also retains the actual funding debit inside
the same signed prefix. Overlapping populations are not double credited. -/
theorem funded_correlation_one (H P T Y : Finset ℕ) (a b debit : ℝ)
    (g : ℕ → ℝ) :
    correlation (H ∪ P ∪ T ∪ Y)
        (fun n => rejoinedWeights H P T Y a b debit n * g n) 1 =
      (∑ n ∈ H, g n) + a*(∑ n ∈ P, g n) + b*(∑ n ∈ T, g n) -
        debit*(∑ n ∈ Y, g n) := by
  rw [correlation_one, rejoined_weight_sum]

/-- Coherence is not an impossibility theorem for all energy methods.
With equal profile endpoints, subtracting a constant prefix component is
EXACT and leaves the full signed carrier pairing unchanged. The optional
probe tests this projection; it supplies no asymptotic arithmetic rate. -/
theorem constant_projection_pairing (R : ℕ) (S : Finset ℕ) (w f : ℕ → ℝ)
    (c : ℝ) (hend : f 1 = f (R+1)) :
    (∑ k ∈ activeCutoffs R f,
      (correlation S w k - c) * (f k - f (k+1))) =
      ∑ k ∈ activeCutoffs R f, correlation S w k * (f k - f (k+1)) := by
  have ht : (∑ k ∈ Finset.Icc 1 R, (f k - f (k+1))) = 0 := by
    rw [← Finset.Ico_add_one_right_eq_Icc]
    calc
      _ = -(∑ k ∈ Finset.Ico 1 (R+1), (f (k+1)-f k)) := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = 0 := by rw [Finset.sum_Ico_sub f (by omega : 1 ≤ R+1), ← hend]; ring
  have ha : (∑ k ∈ activeCutoffs R f, (f k-f (k+1))) = 0 := by
    have he : (∑ k ∈ activeCutoffs R f, (f k-f (k+1))) =
        ∑ k ∈ Finset.Icc 1 R, (f k-f (k+1)) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro k hk hn
      have heq : f k = f (k+1) := by
        by_contra heq
        exact hn (Finset.mem_filter.mpr ⟨hk, heq⟩)
      simp [heq]
    exact he.trans ht
  calc
    _ = (∑ k ∈ activeCutoffs R f, correlation S w k * (f k-f (k+1))) -
          (∑ k ∈ activeCutoffs R f, c * (f k-f (k+1))) := by
      simp only [sub_mul, Finset.sum_sub_distrib]
    _ = _ := by rw [← Finset.mul_sum, ha, mul_zero, sub_zero]

end RiemannGaussian.ZetaRieszPrefixCoherenceAudit
