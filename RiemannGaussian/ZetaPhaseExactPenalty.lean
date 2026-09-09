/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseContactRoot

/-!
# Every frequency constraint at the exact four-contact root

The exact contact equations impose equality at the selected nine
frequencies. Rational center calculations, controlled perturbations, and
the growing linear height cost prove a uniform strict penalty at every
other natural frequency. These are the actual four-contact root's
constraints, independent of the earlier five-contact rational certificate.
-/

open scoped Classical

namespace RiemannGaussian

noncomputable section

/-- The full coefficient constraint for a four-contact configuration,
retaining the signed source and every contact contribution. -/
def phaseContactPolynomialPenalty (u : Fin 9 → ℝ) (n : ℕ) : ℝ :=
  u 8 * phaseContactCost n - phaseContactSourceCoeff n -
    ∑ j : Fin 4, u (phaseContactMassCoordinate j) *
      phaseChebyshevValue n (u (phaseContactCosineCoordinate j))

/-- The exact coefficient penalty at the constructed contact solution. -/
def phaseContactExactPenalty (n : ℕ) : ℝ := phaseContactPolynomialPenalty phaseContactExactRoot n

/-- The exact four contact angles, available in the original phase coordinate. -/
def phaseContactExactAngle (j : Fin 4) : ℝ :=
  Real.arccos (phaseContactExactRoot (phaseContactCosineCoordinate j))

private theorem phaseContactCost_nonneg (n : ℕ) : 0 ≤ phaseContactCost n := by
  unfold phaseContactCost
  split_ifs <;> positivity

private theorem phaseChebyshevValue_eq_cos_arccos (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    phaseChebyshevValue n x = Real.cos ((n : ℝ) * Real.arccos x) := by
  have h := phaseChebyshevValue_cos n (Real.arccos x)
  rw [Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2] at h
  exact h

/-- The polynomial penalty is the actual Fourier constraint of the positive
contact measure, at every natural frequency. -/
theorem phaseContactExactPenalty_eq_cos (n : ℕ) :
    phaseContactExactPenalty n = phaseContactExactRoot 8 * phaseContactCost n - phaseContactSourceCoeff n -
      ∑ j : Fin 4, phaseContactExactRoot (phaseContactMassCoordinate j) *
        Real.cos ((n : ℝ) * phaseContactExactAngle j) := by
  unfold phaseContactExactPenalty phaseContactPolynomialPenalty phaseContactExactAngle
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [phaseChebyshevValue_eq_cos_arccos n (abs_phaseContactExactRoot_cosine_lt_one j).le]

/-- All four cosine--mass cross terms are controlled when transporting a
coefficient constraint from a rational center to an exact nearby root. -/
theorem abs_phaseContactPolynomialPenalty_sub_le {u c : Fin 9 → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hc : ∀ k, |c k| ≤ 1)
    (hu : ∀ j : Fin 4, |u (phaseContactCosineCoordinate j)| ≤ 1)
    (huc : ∀ k, |u k - c k| ≤ r) (n : ℕ) :
    |phaseContactPolynomialPenalty u n - phaseContactPolynomialPenalty c n| ≤
      (phaseContactCost n + 8 * (6 : ℝ) ^ n) * r := by
  have hW : 0 ≤ (6 : ℝ) ^ n := by positivity
  have hterm (j : Fin 4) :
      |u (phaseContactMassCoordinate j) * phaseChebyshevValue n (u (phaseContactCosineCoordinate j)) -
        c (phaseContactMassCoordinate j) * phaseChebyshevValue n (c (phaseContactCosineCoordinate j))| ≤
        2 * (6 : ℝ) ^ n * r := by
    let m := phaseContactMassCoordinate j
    let q := phaseContactCosineCoordinate j
    have ht := abs_phaseChebyshevValue_le n (hu j)
    have hd := (abs_phaseChebyshevValue_sub_le n (hu j) (hc q)).trans
      (mul_le_mul_of_nonneg_left (huc q) hW)
    have h1 : |(u m - c m) * phaseChebyshevValue n (u q)| ≤ r * (6 : ℝ) ^ n := by
      rw [abs_mul]
      exact mul_le_mul (huc m) ht (abs_nonneg _) hr
    have h2 : |c m * (phaseChebyshevValue n (u q) - phaseChebyshevValue n (c q))| ≤ (6 : ℝ) ^ n * r := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right (hc m) (abs_nonneg _)).trans (by simpa using hd)
    have he : u m * phaseChebyshevValue n (u q) - c m * phaseChebyshevValue n (c q) =
        (u m - c m) * phaseChebyshevValue n (u q) +
          c m * (phaseChebyshevValue n (u q) - phaseChebyshevValue n (c q)) := by ring
    change |u m * phaseChebyshevValue n (u q) - c m * phaseChebyshevValue n (c q)| ≤ _
    rw [he]
    linarith [abs_add_le ((u m - c m) * phaseChebyshevValue n (u q))
      (c m * (phaseChebyshevValue n (u q) - phaseChebyshevValue n (c q)))]
  have hsum : |∑ j : Fin 4,
      (u (phaseContactMassCoordinate j) * phaseChebyshevValue n (u (phaseContactCosineCoordinate j)) -
        c (phaseContactMassCoordinate j) * phaseChebyshevValue n (c (phaseContactCosineCoordinate j)))| ≤
        8 * (6 : ℝ) ^ n * r := by
    calc
      _ ≤ ∑ j : Fin 4, |u (phaseContactMassCoordinate j) *
          phaseChebyshevValue n (u (phaseContactCosineCoordinate j)) -
          c (phaseContactMassCoordinate j) * phaseChebyshevValue n (c (phaseContactCosineCoordinate j))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin 4, 2 * (6 : ℝ) ^ n * r := Finset.sum_le_sum (fun j _ ↦ hterm j)
      _ = _ := by simp; ring
  have hl : |(u 8 - c 8) * phaseContactCost n| ≤ r * phaseContactCost n := by
    rw [abs_mul, abs_of_nonneg (phaseContactCost_nonneg n)]
    exact mul_le_mul_of_nonneg_right (huc 8) (phaseContactCost_nonneg n)
  have he : phaseContactPolynomialPenalty u n - phaseContactPolynomialPenalty c n =
      (u 8 - c 8) * phaseContactCost n - ∑ j : Fin 4,
        (u (phaseContactMassCoordinate j) * phaseChebyshevValue n (u (phaseContactCosineCoordinate j)) -
          c (phaseContactMassCoordinate j) * phaseChebyshevValue n (c (phaseContactCosineCoordinate j))) := by
    unfold phaseContactPolynomialPenalty
    rw [Finset.sum_sub_distrib]
    ring
  rw [he]
  have ht := abs_sub ((u 8 - c 8) * phaseContactCost n)
    (∑ j : Fin 4, (u (phaseContactMassCoordinate j) * phaseChebyshevValue n (u (phaseContactCosineCoordinate j)) -
      c (phaseContactMassCoordinate j) * phaseChebyshevValue n (c (phaseContactCosineCoordinate j))))
  nlinarith only [ht, hl, hsum]

private def phaseContactCenterPenaltyQ (n : ℕ) : ℚ :=
  phaseContactRootCenterQ 8 * (if n = 0 then 1 else ((n : ℚ) + 1) / 2) -
    (if n = 0 then -4 / 13 else if n = 1 then 4 / 17 else 0) -
    ∑ j : Fin 4, phaseContactRootCenterQ (phaseContactMassCoordinate j) *
      (phaseContactJetQ (phaseContactRootCenterQ (phaseContactCosineCoordinate j)) n).1.1

private theorem phaseContactCenterPenaltyQ_cast (n : ℕ) :
    (phaseContactCenterPenaltyQ n : ℝ) = phaseContactPolynomialPenalty phaseContactRootCenter n := by
  unfold phaseContactCenterPenaltyQ phaseContactPolynomialPenalty phaseContactCost phaseContactSourceCoeff
  push_cast
  simp only [(phaseContactJetQ_cast _ _).1]
  split_ifs <;> norm_num [phaseContactRootCenter]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
private theorem phaseContactCenterPenaltyQ_small (n : ℕ) (hn : n < 36)
    (hs : n ∉ phaseContactFrequencies) :
    (1 / 10000 : ℚ) + ((if n = 0 then 1 else ((n : ℚ) + 1) / 2) + 8 * (6 : ℚ) ^ n) * (1 / 10 ^ 30) ≤
      phaseContactCenterPenaltyQ n := by
  interval_cases n <;> norm_num [phaseContactFrequencies] at hs <;>
    norm_num [phaseContactCenterPenaltyQ, phaseContactJetQ, phaseContactRootCenterQ,
      phaseContactMassCoordinate, phaseContactCosineCoordinate, Fin.sum_univ_succ]

private theorem exactPenalty_sub_center (n : ℕ) :
    |phaseContactExactPenalty n - phaseContactPolynomialPenalty phaseContactRootCenter n| ≤
      (phaseContactCost n + 8 * (6 : ℝ) ^ n) * (1 / 10 ^ 30) := by
  apply abs_phaseContactPolynomialPenalty_sub_le (by norm_num)
  · intro k
    have h : |phaseContactRootCenter k| ≤ (999999 / 1000000 : ℝ) := by
      simpa only [phaseContactRootCenter, Rat.cast_abs, Rat.cast_div, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr (abs_phaseContactRootCenterQ_le k)
    linarith
  · intro j
    exact (abs_phaseContactExactRoot_cosine_lt_one j).le
  · intro k
    exact (norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter) k).trans phaseContactExactRoot_dist_le

private theorem exactPenalty_small {n : ℕ} (hn : n < 36) (hs : n ∉ phaseContactFrequencies) :
    (1 / 10000 : ℝ) ≤ phaseContactExactPenalty n := by
  have h := (Rat.cast_le (K := ℝ)).mpr (phaseContactCenterPenaltyQ_small n hn hs)
  push_cast at h
  rw [phaseContactCenterPenaltyQ_cast] at h
  have hcost : ((if n = 0 then 1 else ((n : ℚ) + 1) / 2 : ℚ) : ℝ) = phaseContactCost n := by
    unfold phaseContactCost
    split_ifs <;> norm_num
  rw [hcost] at h
  have hd := (abs_le.mp (exactPenalty_sub_center n)).1
  linarith

private theorem exactRoot_efficiency_lower : (11 / 625 : ℝ) ≤ phaseContactExactRoot 8 := by
  have hc : (11 / 625 : ℝ) + 1 / 10 ^ 30 ≤ phaseContactRootCenter 8 := by
    norm_num [phaseContactRootCenter, phaseContactRootCenterQ]
  have hd := (abs_le.mp ((norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter) 8).trans
    phaseContactExactRoot_dist_le)).1
  change -(1 / 10 ^ 30 : ℝ) ≤ phaseContactExactRoot 8 - phaseContactRootCenter 8 at hd
  linarith

private theorem exactRoot_mass_upper :
    (∑ j : Fin 4, phaseContactExactRoot (phaseContactMassCoordinate j)) ≤ (3253 / 10000 : ℝ) := by
  have hj (j : Fin 4) : phaseContactExactRoot (phaseContactMassCoordinate j) ≤
      phaseContactRootCenter (phaseContactMassCoordinate j) + (1 / 10 ^ 30 : ℝ) := by
    have hd := (abs_le.mp ((norm_le_pi_norm (phaseContactExactRoot - phaseContactRootCenter)
      (phaseContactMassCoordinate j)).trans phaseContactExactRoot_dist_le)).2
    change phaseContactExactRoot (phaseContactMassCoordinate j) - phaseContactRootCenter (phaseContactMassCoordinate j) ≤
      (1 / 10 ^ 30 : ℝ) at hd
    linarith
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hj j)
  norm_num [Fin.sum_univ_succ, phaseContactRootCenter, phaseContactRootCenterQ, phaseContactMassCoordinate] at h ⊢
  linarith

private theorem exactPenalty_large {n : ℕ} (hn : 36 ≤ n) :
    (1 / 10000 : ℝ) ≤ phaseContactExactPenalty n := by
  have hm : (∑ j : Fin 4, phaseContactExactRoot (phaseContactMassCoordinate j) *
      phaseChebyshevValue n (phaseContactExactRoot (phaseContactCosineCoordinate j))) ≤ (3253 / 10000 : ℝ) := by
    refine (Finset.sum_le_sum (fun j _ ↦ ?_)).trans exactRoot_mass_upper
    rw [phaseChebyshevValue_eq_cos_arccos n (abs_phaseContactExactRoot_cosine_lt_one j).le]
    exact mul_le_of_le_one_right (phaseContactExactRoot_mass_pos j).le (Real.cos_le_one _)
  have hnR : (36 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (37 / 2 : ℝ) ≤ phaseContactCost n := by
    have h0 : n ≠ 0 := by omega
    simp only [phaseContactCost, if_neg h0]
    linarith
  have hp := mul_le_mul exactRoot_efficiency_lower hc (by norm_num : (0 : ℝ) ≤ 37 / 2)
    ((show (0 : ℝ) ≤ 11 / 625 by norm_num).trans exactRoot_efficiency_lower)
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  unfold phaseContactExactPenalty phaseContactPolynomialPenalty
  simp only [phaseContactSourceCoeff, if_neg h0, if_neg h1, sub_zero]
  linarith

private theorem phaseContactFrequency_exists {n : ℕ} (hn : n ∈ phaseContactFrequencies) :
    ∃ i : Fin 9, phaseContactFrequency i = n := by
  simp only [phaseContactFrequencies, Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩ |
      exact ⟨4, rfl⟩ | exact ⟨5, rfl⟩ | exact ⟨6, rfl⟩ | exact ⟨7, rfl⟩ | exact ⟨8, rfl⟩

/-- The coefficient constraints are exact equalities at every selected frequency. -/
theorem phaseContactExactPenalty_eq_zero_of_mem {n : ℕ} (hn : n ∈ phaseContactFrequencies) :
    phaseContactExactPenalty n = 0 := by
  obtain ⟨i, rfl⟩ := phaseContactFrequency_exists hn
  exact congrFun phaseContactExactRoot_system i

/-- Every unused frequency pays a uniform strictly positive penalty,
including all arbitrarily high frequencies. -/
theorem one_div_tenThousand_le_phaseContactExactPenalty {n : ℕ} (hn : n ∉ phaseContactFrequencies) :
    (1 / 10000 : ℝ) ≤ phaseContactExactPenalty n := by
  by_cases hsmall : n < 36
  · exact exactPenalty_small hsmall hn
  · exact exactPenalty_large (by omega)

/-- The exact contact root satisfies every dual coefficient inequality. -/
theorem phaseContactExactPenalty_nonneg (n : ℕ) : 0 ≤ phaseContactExactPenalty n := by
  by_cases hn : n ∈ phaseContactFrequencies
  · rw [phaseContactExactPenalty_eq_zero_of_mem hn]
  · linarith [one_div_tenThousand_le_phaseContactExactPenalty hn]

/-- The dual constraints vanish precisely on the selected nine frequencies.
This identifies the exact equality set without assuming primal feasibility. -/
theorem phaseContactExactPenalty_eq_zero_iff (n : ℕ) :
    phaseContactExactPenalty n = 0 ↔ n ∈ phaseContactFrequencies := by
  refine ⟨?_, phaseContactExactPenalty_eq_zero_of_mem⟩
  intro h
  by_contra hn
  have hp := one_div_tenThousand_le_phaseContactExactPenalty hn
  rw [h] at hp
  norm_num at hp

end

end RiemannGaussian
