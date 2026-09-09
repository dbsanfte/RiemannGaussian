/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaSignedFiveHeight

/-!
# A contact certificate for sparse phase weights

The phase search uses a proved linear allowance for the logarithmic height
cost. Five exact contact angles give a rational certificate for this
optimization problem at real shift ratio `13/4`. The certificate explains
sparsity through nonnegative contact values and nonnegative coefficient
penalties, rather than assuming that a numerically optimized kernel is
everywhere nonnegative.

The frequency set is specific to this cost and shift. It is not asserted
to be an intrinsic pattern of zeta zeros or an exact optimal support.
-/

open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The cost used to bound the common logarithmic height of frequency `n`. -/
def phaseContactCost (n : ℕ) : ℝ := if n = 0 then 1 else ((n : ℝ) + 1) / 2

/-- This optimization cost bounds the actual local logarithmic height
appearing in the checked signed zeta estimate. -/
theorem phaseContactCost_controls_logHeight (n : ℕ) (y : ℝ) :
    localZetaLogHeight ((n : ℝ) * y) ≤ phaseContactCost n * localZetaLogHeight y := by
  by_cases hn : n = 0
  · subst n
    simpa [phaseContactCost] using localZetaLogHeight_zero_le y
  · have hk : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have h := localZetaLogHeight_mul_le_add_log hk y
    have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by linarith)
    have hp := mul_nonneg (show (0 : ℝ) ≤ n - 1 by linarith)
      (show 0 ≤ localZetaLogHeight y - 2 by linarith [two_lt_localZetaLogHeight y])
    simp only [phaseContactCost, if_neg hn]
    nlinarith

/-- The exact cosines of five contact angles, chosen from the numerical
search and then checked independently by rational arithmetic. -/
def phaseContactCosine : Fin 5 → ℚ :=
  ![-26857 / 100000, -1471 / 2000, -95037 / 100000, -24989 / 25000, -1]

/-- Positive rational weights on the five contact angles. -/
def phaseContactWeight : Fin 5 → ℚ :=
  ![2795979 / 25000000, 102063 / 1250000, 4226537 / 50000000,
    586919 / 50000000, 1776699 / 50000000]

/-- The angles themselves remain available, with their exact cosine values. -/
def phaseContactAngle (i : Fin 5) : ℝ := Real.arccos (phaseContactCosine i : ℝ)

/-- The sparse set identified by the exact coefficient penalty certificate. -/
def phaseContactFrequencies : Finset ℕ := {0, 1, 2, 3, 4, 7, 10, 13, 24}

private theorem phaseContactCosine_abs_le_one (i : Fin 5) :
    |(phaseContactCosine i : ℝ)| ≤ 1 := by
  fin_cases i <;> norm_num [phaseContactCosine]

/-- Every exact contact has nonnegative weight. -/
theorem phaseContactWeight_nonneg (i : Fin 5) : 0 ≤ (phaseContactWeight i : ℝ) := by
  fin_cases i <;> norm_num [phaseContactWeight]

private def phaseContactCosPair (q : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, q)
  | n + 1 => let p := phaseContactCosPair q n; (p.2, 2 * q * p.2 - p.1)

private theorem phaseContactCosPair_eq_cos (q : ℚ) (hq : |(q : ℝ)| ≤ 1) (n : ℕ) :
    ((phaseContactCosPair q n).1 : ℝ) = Real.cos ((n : ℝ) * Real.arccos (q : ℝ)) ∧
      ((phaseContactCosPair q n).2 : ℝ) = Real.cos (((n : ℝ) + 1) * Real.arccos (q : ℝ)) := by
  have hcos := Real.cos_arccos (abs_le.mp hq).1 (abs_le.mp hq).2
  induction n with
  | zero => simp [phaseContactCosPair, hcos]
  | succ n ih =>
    constructor
    · simpa [phaseContactCosPair] using ih.2
    · simp only [phaseContactCosPair, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat,
        Nat.cast_add, Nat.cast_one]
      rw [ih.1, ih.2]
      have h := Real.cos_add_cos (((n : ℝ) + 2) * Real.arccos (q : ℝ))
        ((n : ℝ) * Real.arccos (q : ℝ))
      rw [show ((((n : ℝ) + 2) * Real.arccos (q : ℝ) +
        (n : ℝ) * Real.arccos (q : ℝ)) / 2) =
        ((n : ℝ) + 1) * Real.arccos (q : ℝ) by ring,
        show ((((n : ℝ) + 2) * Real.arccos (q : ℝ) -
          (n : ℝ) * Real.arccos (q : ℝ)) / 2) = Real.arccos (q : ℝ) by ring,
        hcos] at h
      convert (show 2 * (q : ℝ) * Real.cos (((n : ℝ) + 1) * Real.arccos (q : ℝ)) -
        Real.cos ((n : ℝ) * Real.arccos (q : ℝ)) =
        Real.cos (((n : ℝ) + 2) * Real.arccos (q : ℝ)) by nlinarith only [h]) using 1
      congr 1
      ring

/-- The selected-zero source minus the real-axis pole cost at shift `13/4`. -/
def phaseContactSourceCoeff (n : ℕ) : ℝ :=
  if n = 0 then -4 / 13 else if n = 1 then 4 / 17 else 0

/-- The exact Fourier moment of the positive contact measure. -/
def phaseContactMoment (n : ℕ) : ℝ :=
  ∑ i : Fin 5, (phaseContactWeight i : ℝ) * Real.cos ((n : ℝ) * phaseContactAngle i)

/-- The coefficient penalty left after subtracting the contact measure
from the cost and selected-zero source. -/
def phaseContactPenalty (n : ℕ) : ℝ :=
  (8801 / 500000 : ℝ) * phaseContactCost n - phaseContactSourceCoeff n - phaseContactMoment n

private def phaseContactPenaltyQ (n : ℕ) : ℚ :=
  (8801 / 500000 : ℚ) * (if n = 0 then 1 else ((n : ℚ) + 1) / 2) -
    (if n = 0 then -4 / 13 else if n = 1 then 4 / 17 else 0) -
      ∑ i : Fin 5, phaseContactWeight i * (phaseContactCosPair (phaseContactCosine i) n).1

private theorem phaseContactPenaltyQ_cast (n : ℕ) :
    (phaseContactPenaltyQ n : ℝ) = phaseContactPenalty n := by
  unfold phaseContactPenaltyQ phaseContactPenalty phaseContactCost phaseContactSourceCoeff
    phaseContactMoment phaseContactAngle
  push_cast
  congr 1
  · split_ifs <;> norm_num
  · apply Finset.sum_congr rfl
    intro i _
    rw [(phaseContactCosPair_eq_cos _ (phaseContactCosine_abs_le_one i) n).1]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem phaseContactPenaltyQ_small (n : ℕ) (hn : n < 38) :
    if n ∈ phaseContactFrequencies then 0 ≤ phaseContactPenaltyQ n
    else (1 / 64 : ℚ) ≤ phaseContactPenaltyQ n := by
  interval_cases n <;>
    norm_num [phaseContactPenaltyQ, phaseContactCosPair, phaseContactWeight,
      phaseContactCosine, phaseContactFrequencies, Fin.sum_univ_succ]

private theorem phaseContactMoment_le_mass (n : ℕ) :
    phaseContactMoment n ≤ (16264633 / 50000000 : ℝ) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦
    mul_le_of_le_one_right (phaseContactWeight_nonneg i)
      (Real.cos_le_one ((n : ℝ) * phaseContactAngle i)))
  change phaseContactMoment n ≤ ∑ i : Fin 5, (phaseContactWeight i : ℝ) at h
  norm_num [phaseContactWeight, Fin.sum_univ_succ] at h
  exact h

private theorem phaseContactPenalty_large {n : ℕ} (hn : 38 ≤ n) :
    (1 / 64 : ℝ) ≤ phaseContactPenalty n := by
  have hm := phaseContactMoment_le_mass n
  have hnreal : (38 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : n ≠ 0 := by omega
  have h1 : n ≠ 1 := by omega
  simp only [phaseContactPenalty, phaseContactCost, phaseContactSourceCoeff,
    if_neg h0, if_neg h1]
  linarith

/-- Every coefficient penalty in the exact contact certificate is
nonnegative, including all frequencies beyond the finite rational check. -/
theorem phaseContactPenalty_nonneg (n : ℕ) : 0 ≤ phaseContactPenalty n := by
  by_cases hn : n < 38
  · have h := phaseContactPenaltyQ_small n hn
    split_ifs at h with hm
    · rw [← phaseContactPenaltyQ_cast]
      exact_mod_cast h
    · have h' : (0 : ℚ) ≤ phaseContactPenaltyQ n := by linarith
      rw [← phaseContactPenaltyQ_cast]
      exact_mod_cast h'
  · linarith [phaseContactPenalty_large (by omega : 38 ≤ n)]

/-- Outside the nine selected frequencies, every coefficient pays at
least `1/64` in the exact efficiency deficit. This is a uniform theorem
over all natural frequencies, not a sampled positivity claim. -/
theorem one_div_sixtyFour_le_phaseContactPenalty {n : ℕ}
    (hn : n ∉ phaseContactFrequencies) : (1 / 64 : ℝ) ≤ phaseContactPenalty n := by
  by_cases hsmall : n < 38
  · have h := phaseContactPenaltyQ_small n hsmall
    rw [if_neg hn] at h
    rw [← phaseContactPenaltyQ_cast]
    have h' : ((1 / 64 : ℚ) : ℝ) ≤ (phaseContactPenaltyQ n : ℝ) := Rat.cast_le.mpr h
    norm_num at h'
    exact h'
  · exact phaseContactPenalty_large (by omega)

end

end RiemannGaussian
