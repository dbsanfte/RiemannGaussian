/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseExactPenalty
import RiemannGaussian.ZetaPhaseContactSparsity

/-!
# Infinite-family duality at the exact contact geometry

The actual four-contact root gives a source-to-cost upper bound for every
nonnegative phase kernel with nonnegative coefficients and finite height
budget. The exact deficit identity retains all contact values and every
frequency penalty. Equality forces support inside the selected finite set.
No feasibility or attainment is assumed for the proposed primal family.
-/

open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The full Fourier moment of the exact four-contact measure. -/
def phaseContactExactMoment (n : ℕ) : ℝ :=
  ∑ j : Fin 4, phaseContactExactRoot (phaseContactMassCoordinate j) *
    Real.cos ((n : ℝ) * phaseContactExactAngle j)

/-- The efficiency deficit from the exact contact root's source bound. -/
def phaseContactExactDeficit (a : ℕ → ℝ) : ℝ :=
  phaseContactExactRoot 8 * phaseContactBudget a - phaseContactSource a

private theorem exactContactSource_hasSum (a : ℕ → ℝ) :
    HasSum (fun n ↦ a n * phaseContactSourceCoeff n) (phaseContactSource a) := by
  have h := (hasSum_ite_eq 1 ((4 / 17 : ℝ) * a 1)).sub
    (hasSum_ite_eq 0 ((4 / 13 : ℝ) * a 0))
  apply h.congr_fun
  intro n
  by_cases h0 : n = 0
  · subst n
    norm_num [phaseContactSourceCoeff]
    ring
  · by_cases h1 : n = 1
    · subst n
      norm_num [phaseContactSourceCoeff]
      ring
    · simp [phaseContactSourceCoeff, h0, h1]

private theorem exactContactMoment_hasSum {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n)) :
    HasSum (fun n ↦ a n * phaseContactExactMoment n)
      (∑ i : Fin 4, phaseContactExactRoot (phaseContactMassCoordinate i) * phaseContactKernel a (phaseContactExactAngle i)) := by
  have h (i : Fin 4) :=
    (summable_phaseContactKernel ha hs (phaseContactExactAngle i)).hasSum.mul_left
      (phaseContactExactRoot (phaseContactMassCoordinate i))
  have hm := hasSum_sum (s := Finset.univ) (fun i _ ↦ h i)
  apply hm.congr_fun
  intro n
  simp only [phaseContactExactMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact identity explaining the sparse weights: the efficiency
deficit is the sum of contact values and frequency penalties. Every phase
and every contact is retained until this identity has been established. -/
theorem phaseContactExactDeficit_eq_contacts_add_penalties {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable (fun n ↦ phaseContactCost n * a n)) :
    phaseContactExactDeficit a =
      (∑ i : Fin 4, phaseContactExactRoot (phaseContactMassCoordinate i) * phaseContactKernel a (phaseContactExactAngle i)) +
        ∑' n : ℕ, a n * phaseContactExactPenalty n := by
  have h := ((hs.hasSum.mul_left (phaseContactExactRoot 8)).sub
    (exactContactSource_hasSum a)).sub (exactContactMoment_hasSum ha hs)
  have hp : HasSum (fun n ↦ a n * phaseContactExactPenalty n)
      (phaseContactExactDeficit a -
        ∑ i : Fin 4, phaseContactExactRoot (phaseContactMassCoordinate i) * phaseContactKernel a (phaseContactExactAngle i)) := by
    apply h.congr_fun
    intro n
    rw [phaseContactExactPenalty_eq_cos]
    unfold phaseContactExactMoment
    ring
  rw [hp.tsum_eq]
  ring

/-- The full infinite family of penalty terms is summable, so the exact
deficit decomposition never relies on a default value for a divergent sum. -/
theorem summable_phaseContactExactPenalty {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n)) :
    Summable (fun n ↦ a n * phaseContactExactPenalty n) := by
  have h := ((hs.mul_left (phaseContactExactRoot 8)).sub
    (exactContactSource_hasSum a).summable).sub (exactContactMoment_hasSum ha hs).summable
  apply h.congr
  intro n
  rw [phaseContactExactPenalty_eq_cos]
  unfold phaseContactExactMoment
  ring

/-- Every feasible nonnegative phase kernel obeys the exact efficiency
upper bound, for finite or infinite support. -/
theorem phaseContactSource_le_exactContactBound {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t) :
    phaseContactSource a ≤ (phaseContactExactRoot 8) * phaseContactBudget a := by
  have hc : 0 ≤ ∑ i : Fin 4, phaseContactExactRoot (phaseContactMassCoordinate i) *
      phaseContactKernel a (phaseContactExactAngle i) :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg ((phaseContactExactRoot_mass_pos i).le) (hp _))
  have hf : 0 ≤ ∑' n : ℕ, a n * phaseContactExactPenalty n :=
    tsum_nonneg (fun n ↦ mul_nonneg (ha n) (phaseContactExactPenalty_nonneg n))
  have h := phaseContactExactDeficit_eq_contacts_add_penalties ha hs
  unfold phaseContactExactDeficit at h
  linarith

/-- Quantitative sparse concentration: every coefficient outside the
nine selected frequencies contributes at least its weight divided by
`10000` to the exact deficit.
This statement includes arbitrarily high frequencies and infinite support. -/
theorem phaseContactExact_offSupport_mass_le {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable (fun n ↦ phaseContactCost n * a n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t) :
    (∑' n : ℕ, if n ∈ phaseContactFrequencies then 0 else a n) ≤
      10000 * phaseContactExactDeficit a := by
  have hsa := summable_of_phaseContactBudget ha hs
  have hso : Summable (fun n : ℕ ↦ if n ∈ phaseContactFrequencies then 0 else a n) := by
    apply Summable.of_nonneg_of_le (fun n ↦ by split_ifs; exact le_rfl; exact ha n) _ hsa
    intro n
    split_ifs <;> simp_all
  have hf := summable_phaseContactExactPenalty ha hs
  have hle := hso.tsum_le_tsum (fun n ↦ show
      (if n ∈ phaseContactFrequencies then 0 else a n) ≤
        10000 * (a n * phaseContactExactPenalty n) from by
    by_cases hn : n ∈ phaseContactFrequencies
    · simp only [if_pos hn]
      exact mul_nonneg (by norm_num) (mul_nonneg (ha n) (phaseContactExactPenalty_nonneg n))
    · simp only [if_neg hn]
      have h := mul_le_mul_of_nonneg_left (one_div_tenThousand_le_phaseContactExactPenalty hn) (ha n)
      nlinarith only [h]) (hf.mul_left 10000)
  rw [tsum_mul_left] at hle
  have hc : 0 ≤ ∑ i : Fin 4, phaseContactExactRoot (phaseContactMassCoordinate i) *
      phaseContactKernel a (phaseContactExactAngle i) :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg ((phaseContactExactRoot_mass_pos i).le) (hp _))
  have he := phaseContactExactDeficit_eq_contacts_add_penalties ha hs
  linarith

/-- The same exact deficit also controls the contact values. Efficient
kernels therefore approach zero at the positively weighted contact angles. -/
theorem phaseContactExact_contact_values_le_deficit {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n)) :
    (∑ i : Fin 4, phaseContactExactRoot (phaseContactMassCoordinate i) * phaseContactKernel a (phaseContactExactAngle i)) ≤
      phaseContactExactDeficit a := by
  have he := phaseContactExactDeficit_eq_contacts_add_penalties ha hs
  have hf : 0 ≤ ∑' n : ℕ, a n * phaseContactExactPenalty n :=
    tsum_nonneg (fun n ↦ mul_nonneg (ha n) (phaseContactExactPenalty_nonneg n))
  linarith

/-- Any positive coefficient outside the exact equality set forces a
strict source-to-cost loss, even when infinitely many phases are coupled. -/
theorem phaseContactSource_lt_exactContactBound_of_offSupport {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable (fun n ↦ phaseContactCost n * a n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t) {n : ℕ}
    (hn : n ∉ phaseContactFrequencies) (han : 0 < a n) :
    phaseContactSource a < phaseContactExactRoot 8 * phaseContactBudget a := by
  have ht : 0 < a n * phaseContactExactPenalty n :=
    mul_pos han (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 10000)
      (one_div_tenThousand_le_phaseContactExactPenalty hn))
  have hle := (summable_phaseContactExactPenalty ha hs).le_tsum n
    (fun k _ ↦ mul_nonneg (ha k) (phaseContactExactPenalty_nonneg k))
  have hc : 0 ≤ ∑ i : Fin 4, phaseContactExactRoot (phaseContactMassCoordinate i) *
      phaseContactKernel a (phaseContactExactAngle i) :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (phaseContactExactRoot_mass_pos i).le (hp _))
  have he := phaseContactExactDeficit_eq_contacts_add_penalties ha hs
  unfold phaseContactExactDeficit at he
  linarith

/-- Attainment of the exact source bound forces every unused coefficient
to vanish; finite support is a conclusion rather than an assumption. -/
theorem phaseContactExact_offSupport_eq_zero_of_equality {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable (fun n ↦ phaseContactCost n * a n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t)
    (he : phaseContactSource a = phaseContactExactRoot 8 * phaseContactBudget a)
    {n : ℕ} (hn : n ∉ phaseContactFrequencies) : a n = 0 := by
  by_contra hne
  have hpos : 0 < a n := lt_of_le_of_ne (ha n) (Ne.symm hne)
  have h := phaseContactSource_lt_exactContactBound_of_offSupport ha hs hp hn hpos
  rw [he] at h
  exact (lt_irrefl _) h

/-- The positive contact masses force every contact value to vanish
whenever a feasible family attains the exact efficiency bound. -/
theorem phaseContactExact_contact_eq_zero_of_equality {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable (fun n ↦ phaseContactCost n * a n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t)
    (he : phaseContactSource a = phaseContactExactRoot 8 * phaseContactBudget a) (j : Fin 4) :
    phaseContactKernel a (phaseContactExactAngle j) = 0 := by
  have hd : phaseContactExactDeficit a = 0 := by unfold phaseContactExactDeficit; rw [he, sub_self]
  have hle := phaseContactExact_contact_values_le_deficit ha hs
  rw [hd] at hle
  have hsingle := Finset.single_le_sum
    (f := fun i : Fin 4 ↦ phaseContactExactRoot (phaseContactMassCoordinate i) *
      phaseContactKernel a (phaseContactExactAngle i))
    (fun i _ ↦ mul_nonneg (phaseContactExactRoot_mass_pos i).le (hp _)) (Finset.mem_univ j)
  have hz : phaseContactExactRoot (phaseContactMassCoordinate j) *
      phaseContactKernel a (phaseContactExactAngle j) = 0 :=
    le_antisymm (hsingle.trans hle) (mul_nonneg (phaseContactExactRoot_mass_pos j).le (hp _))
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (phaseContactExactRoot_mass_pos j))


end

end RiemannGaussian
