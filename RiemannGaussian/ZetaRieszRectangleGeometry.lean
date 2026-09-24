/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszRectangle
import RiemannGaussian.ZetaRieszPrimeIntervals

/-!
# Concrete prime-log geometry inside the rectangle's literal masks

The five individual cuts and the original narrow total window suffice for
the actual second incidence. Paying their factorial tails is a separate
quantitative obligation; no hard cutoff is inferred from an order alone.
-/

namespace RiemannGaussian.ZetaRieszSkewAllocation
noncomputable section
open scoped BigOperators Classical
open ZetaRieszWideOwnerAudit ZetaRieszJointAllocation ZetaRieszPrimeEndpoint
open ZetaRieszPrimeCountFrequency ZetaRieszAnnulusJoint ZetaRieszMaskSupport
open ZetaRieszDominantAllocation ZetaRieszTypeII ZetaRieszPrimeIntervals

/-- The concrete five leg cuts used to check the literal masks. -/
def rectangleLogBox (N p q r : ℕ) : Prop :=
  (N : ℝ) < Real.log p ∧ Real.log p ≤ (5 / 4 : ℝ) * N ∧
    (7 / 10 : ℝ) * N < Real.log q ∧ Real.log q ≤ N ∧ Real.log r ≤ (N : ℝ) / 10

/-- On the original schedule, physical squarefree triples in the narrow
window with all prime shares below the displayed cap satisfy every old
integer mask. Neither old deletion sector contains such a label. -/
theorem rectangle_mem_tripleBand (t : ℕ) (ht : 32 ≤ t) {u : ℝ}
    (hu : 1 / 2 < u) (huU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hL : (11 / 8 : ℝ) * dyadicMomentOrder t ≤
      SquarefreeVaughanLogSource.length u (dyadicMomentOrder t))
    {n : ℕ} (hn : Squarefree n) (hc : n.primeFactors.card = 3)
    (hwindow : (39 / 20 : ℝ) * dyadicMomentOrder t < Real.log n ∧
      Real.log n ≤ (41 / 20 : ℝ) * dyadicMomentOrder t)
    (hpA : ∀ p ∈ n.primeFactors, p ∈ intermediatePrimes u (dyadicMomentOrder t))
    (hpCap : ∀ p ∈ n.primeFactors, Real.log p ≤ (5 / 4 : ℝ) * dyadicMomentOrder t) :
    n ∈ tripleBand u (dyadicMomentOrder t) (dyadicPrimeCount t) := by
  let N := dyadicMomentOrder t
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hln : 0 < Real.log n := by nlinarith [hwindow.1]
  have hdom (p : ℕ) (hp : p ∈ n.primeFactors) :
      Real.log p < (13 / 20 : ℝ) * Real.log n := by
    nlinarith [hpCap p hp, hwindow.1]
  have hmem := window_mem_originalMask t ht hu
    (huU.trans radius_lt_source.le) (by nlinarith [hL])
    ((mem_literalWindow N n).mpr (by constructor <;> nlinarith [hwindow.1, hwindow.2]))
    hn (by omega) (by rw [hc]; exact four_le_dyadicPrimeCount t)
    (fun p hp => ((mem_intermediatePrimes u N p).mp (hpA p hp)).2.2)
  have hcancel : n ∉ cancellingSector u N (dyadicPrimeCount t) := by
    intro hcanc
    obtain ⟨_, _, _, _, _, p, hp, _, _, _, hhi⟩ := Finset.mem_filter.mp hcanc
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hlogs : Real.log (n / p : ℕ) = Real.log n - Real.log p := by
      rw [Nat.cast_div (Nat.dvd_of_mem_primeFactors hp) (by exact_mod_cast hpp.ne_zero),
        Real.log_div (by exact_mod_cast hn.ne_zero) (by exact_mod_cast hpp.ne_zero)]
    have hh := (div_le_iff₀ hln).mp hhi
    rw [hlogs] at hh
    nlinarith [hdom p hp]
  have hret : n ∈ retainedBand u N (dyadicPrimeCount t) :=
    Finset.mem_sdiff.mpr ⟨hmem, hcancel⟩
  have hnot : n ∉ dominantSector u N (dyadicPrimeCount t) := by
    intro hd
    obtain ⟨_, _, _, _, p, hp, _, _, hpdom⟩ := Finset.mem_filter.mp hd
    exact (hdom p hp).not_ge hpdom
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_sdiff.mpr ⟨hret, hnot⟩, hwindow⟩, hn, hc⟩

/-- The actual ordered triple has its literal prime support and
squarefreeness; no prime incidence is averaged or duplicated. -/
theorem ordered_triple_data {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hqp : q < p) (hrq : r < q) :
    Squarefree (p * (q * r)) ∧ (p * (q * r)).primeFactors = {p, q, r} ∧
      (p * (q * r)).primeFactors.card = 3 ∧ largestPrime (p * (q * r)) = p ∧
        smallPrime (p * (q * r)) q = r := by
  have hpq : p ≠ q := ne_of_gt hqp
  have hpr : p ≠ r := ne_of_gt (hrq.trans hqp)
  have hqr : q ≠ r := ne_of_gt hrq
  have hpqc : p.Coprime q := hp.coprime_iff_not_dvd.mpr
    (fun hd => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd))
  have hprc : p.Coprime r := hp.coprime_iff_not_dvd.mpr
    (fun hd => hpr ((Nat.prime_dvd_prime_iff_eq hp hr).mp hd))
  have hqrc : q.Coprime r := hq.coprime_iff_not_dvd.mpr
    (fun hd => hqr ((Nat.prime_dvd_prime_iff_eq hq hr).mp hd))
  have hs : Squarefree (p * (q * r)) := Nat.squarefree_mul_iff.mpr
    ⟨hpqc.mul_right hprc, hp.squarefree,
      Nat.squarefree_mul_iff.mpr ⟨hqrc, hq.squarefree, hr.squarefree⟩⟩
  have hf : (p * (q * r)).primeFactors = {p, q, r} := by
    simp [Nat.primeFactors_mul hp.ne_zero (mul_ne_zero hq.ne_zero hr.ne_zero),
      Nat.primeFactors_mul hq.ne_zero hr.ne_zero, hp.primeFactors, hq.primeFactors,
      hr.primeFactors, Finset.insert_comm]
  have hmax : largestPrime (p * (q * r)) = p := by
    apply largestPrime_eq_of_max
    · rw [hf]; simp
    · intro a ha
      rw [hf] at ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl
      · rfl
      · exact hqp.le
      · exact (hrq.trans hqp).le
  refine ⟨hs, hf, ?_, hmax, ?_⟩
  · rw [hf]
    simp [hpq, hpr, hqr]
  · rw [smallPrime, hmax, ← mul_assoc]
    exact Nat.mul_div_cancel_left r (mul_pos hp.pos hq.pos)

/-- The concrete leg and total windows force precisely the requested
second-largest reflected incidence and all three physical prime masks. -/
theorem rectangle_good_incidence {u : ℝ} {N p q r : ℕ} (hN : 0 < N)
    (hpA : p ∈ intermediatePrimes u N) (hqA : q ∈ intermediatePrimes u N)
    (hrA : r ∈ intermediatePrimes u N) (hbox : rectangleLogBox N p q r)
    (hwindow : (39 / 20 : ℝ) * N < Real.log (p * (q * r) : ℕ) ∧
      Real.log (p * (q * r) : ℕ) ≤ (41 / 20 : ℝ) * N)
    (hLlo : (11 / 8 : ℝ) * N ≤ SquarefreeVaughanLogSource.length u N)
    (hLhi : SquarefreeVaughanLogSource.length u N ≤ (139 / 100 : ℝ) * N) :
    q ∈ rectangleIncidences u N (p * (q * r)) := by
  have hp := ((mem_intermediatePrimes u N p).mp hpA).1
  have hq := ((mem_intermediatePrimes u N q).mp hqA).1
  have hr := ((mem_intermediatePrimes u N r).mp hrA).1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hplo, hphi, hqlo, hqhi, hrhi⟩ := hbox
  have hqp : q < p := by
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hq.pos)
      (by exact_mod_cast hp.pos)).mp (by linarith : Real.log (q : ℝ) < Real.log p)
  have hrq : r < q := by
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hr.pos)
      (by exact_mod_cast hq.pos)).mp (by nlinarith : Real.log (r : ℝ) < Real.log q)
  obtain ⟨_, hf, _, hmax, hsmall⟩ := ordered_triple_data hp hq hr hqp hrq
  have hreflect : ReflectedOuterPair (SquarefreeVaughanLogSource.length u N)
      (p * (q * r)) (p, q) := by
    constructor
    · simp only [primePairs, Finset.mem_offDiag, hf, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨Or.inl trivial, Or.inr (Or.inl trivial), ne_of_gt hqp⟩
    · rw [hf]
      ext a
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl | rfl, h⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exfalso
          nlinarith [hwindow.1]
      · rintro (rfl | rfl)
        · exact ⟨Or.inl rfl, by nlinarith [hwindow.2]⟩
        · exact ⟨Or.inr (Or.inl rfl), by nlinarith [hwindow.2]⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, by simpa only [hsmall] using hrA⟩
  apply Finset.mem_filter.mpr
  constructor
  · rw [hmax, hf]
    exact Finset.mem_erase.mpr ⟨ne_of_lt hqp, by simp⟩
  · simpa only [hmax, hsmall] using And.intro hqA (And.intro hr (And.intro hrq hreflect))

end
end RiemannGaussian.ZetaRieszSkewAllocation
