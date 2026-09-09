/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseContactCertificate

/-!
# Why efficient phase kernels concentrate on sparse frequencies

For every nonnegative cosine kernel with nonnegative coefficients and
finite height budget, an exact contact identity decomposes the efficiency
deficit into nonnegative contact values and nonnegative frequency penalties.
The rational certificate gives a uniform penalty outside
`{0,1,2,3,4,7,10,13,24}`. Thus a small deficit forces small total coefficient
mass outside this sparse set, even for an infinite phase family.

This is an explicit dual certificate and a stability theorem for the
particular proved linear height budget and shift ratio `13/4`. It neither
asserts that the numerical optimizer is exact nor removes the open global
signed arithmetic premise for RH.
-/

open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The full phase kernel, retaining every coefficient in the infinite family. -/
def phaseContactKernel (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, a n * Real.cos ((n : ℝ) * t)

/-- The complete coefficient cost that bounds the local logarithmic heights. -/
def phaseContactBudget (a : ℕ → ℝ) : ℝ := ∑' n : ℕ, phaseContactCost n * a n

/-- The selected-zero source less the real-axis pole at shift ratio `13/4`. -/
def phaseContactSource (a : ℕ → ℝ) : ℝ := (4 / 17 : ℝ) * a 1 - (4 / 13 : ℝ) * a 0

/-- The exact gap from the contact certificate's upper efficiency bound. -/
def phaseContactDeficit (a : ℕ → ℝ) : ℝ :=
  (8801 / 500000 : ℝ) * phaseContactBudget a - phaseContactSource a

private theorem one_le_phaseContactCost (n : ℕ) : 1 ≤ phaseContactCost n := by
  by_cases hn : n = 0
  · simp [phaseContactCost, hn]
  · have h : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    simp only [phaseContactCost, if_neg hn]
    linarith

/-- Finite height budget implies absolute summability of all nonnegative
phase coefficients. -/
theorem summable_of_phaseContactBudget {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n)) : Summable a := by
  exact Summable.of_nonneg_of_le ha
    (fun n ↦ le_mul_of_one_le_left (ha n) (one_le_phaseContactCost n)) hs

/-- Every angle evaluation is absolutely convergent under the genuine
finite-budget hypothesis. -/
theorem summable_phaseContactKernel {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n)) (t : ℝ) :
    Summable (fun n : ℕ ↦ a n * Real.cos ((n : ℝ) * t)) := by
  apply (summable_of_phaseContactBudget ha hs).of_norm_bounded
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha n)]
  exact mul_le_of_le_one_right (ha n) (Real.abs_cos_le_one _)

private theorem phaseContactSource_hasSum (a : ℕ → ℝ) :
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

private theorem phaseContactMoment_hasSum {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n)) :
    HasSum (fun n ↦ a n * phaseContactMoment n)
      (∑ i : Fin 5, (phaseContactWeight i : ℝ) * phaseContactKernel a (phaseContactAngle i)) := by
  have h (i : Fin 5) :=
    (summable_phaseContactKernel ha hs (phaseContactAngle i)).hasSum.mul_left
      (phaseContactWeight i : ℝ)
  have hm := hasSum_sum (s := Finset.univ) (fun i _ ↦ h i)
  apply hm.congr_fun
  intro n
  simp only [phaseContactMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The exact identity explaining the sparse weights: the efficiency
deficit is the sum of contact values and frequency penalties. Every phase
and every contact is retained until this identity has been established. -/
theorem phaseContactDeficit_eq_contacts_add_penalties {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable (fun n ↦ phaseContactCost n * a n)) :
    phaseContactDeficit a =
      (∑ i : Fin 5, (phaseContactWeight i : ℝ) * phaseContactKernel a (phaseContactAngle i)) +
        ∑' n : ℕ, a n * phaseContactPenalty n := by
  have h := ((hs.hasSum.mul_left (8801 / 500000 : ℝ)).sub
    (phaseContactSource_hasSum a)).sub (phaseContactMoment_hasSum ha hs)
  have hp : HasSum (fun n ↦ a n * phaseContactPenalty n)
      (phaseContactDeficit a -
        ∑ i : Fin 5, (phaseContactWeight i : ℝ) * phaseContactKernel a (phaseContactAngle i)) := by
    apply h.congr_fun
    intro n
    unfold phaseContactPenalty
    ring
  rw [hp.tsum_eq]
  ring

/-- The full infinite family of penalty terms is summable, so the exact
deficit decomposition never relies on a default value for a divergent sum. -/
theorem summable_phaseContactPenalty {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n)) :
    Summable (fun n ↦ a n * phaseContactPenalty n) := by
  have h := ((hs.mul_left (8801 / 500000 : ℝ)).sub
    (phaseContactSource_hasSum a).summable).sub (phaseContactMoment_hasSum ha hs).summable
  apply h.congr
  intro n
  unfold phaseContactPenalty
  ring

/-- Every feasible nonnegative phase kernel obeys the exact efficiency
upper bound, for finite or infinite support. -/
theorem phaseContactSource_le_certificate {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t) :
    phaseContactSource a ≤ (8801 / 500000 : ℝ) * phaseContactBudget a := by
  have hc : 0 ≤ ∑ i : Fin 5, (phaseContactWeight i : ℝ) *
      phaseContactKernel a (phaseContactAngle i) :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (phaseContactWeight_nonneg i) (hp _))
  have hf : 0 ≤ ∑' n : ℕ, a n * phaseContactPenalty n :=
    tsum_nonneg (fun n ↦ mul_nonneg (ha n) (phaseContactPenalty_nonneg n))
  have h := phaseContactDeficit_eq_contacts_add_penalties ha hs
  unfold phaseContactDeficit at h
  linarith

/-- Quantitative sparse concentration: every coefficient outside the
nine selected frequencies costs at least `1/64` of the exact deficit.
This statement includes arbitrarily high frequencies and infinite support. -/
theorem phaseContact_offSupport_mass_le_sixtyFour_mul_deficit {a : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hs : Summable (fun n ↦ phaseContactCost n * a n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t) :
    (∑' n : ℕ, if n ∈ phaseContactFrequencies then 0 else a n) ≤
      64 * phaseContactDeficit a := by
  have hsa := summable_of_phaseContactBudget ha hs
  have hso : Summable (fun n : ℕ ↦ if n ∈ phaseContactFrequencies then 0 else a n) := by
    apply Summable.of_nonneg_of_le (fun n ↦ by split_ifs; exact le_rfl; exact ha n) _ hsa
    intro n
    split_ifs <;> simp_all
  have hf := summable_phaseContactPenalty ha hs
  have hle := hso.tsum_le_tsum (fun n ↦ show
      (if n ∈ phaseContactFrequencies then 0 else a n) ≤
        64 * (a n * phaseContactPenalty n) from by
    by_cases hn : n ∈ phaseContactFrequencies
    · simp only [if_pos hn]
      exact mul_nonneg (by norm_num) (mul_nonneg (ha n) (phaseContactPenalty_nonneg n))
    · simp only [if_neg hn]
      have h := mul_le_mul_of_nonneg_left (one_div_sixtyFour_le_phaseContactPenalty hn) (ha n)
      nlinarith only [h]) (hf.mul_left 64)
  rw [tsum_mul_left] at hle
  have hc : 0 ≤ ∑ i : Fin 5, (phaseContactWeight i : ℝ) *
      phaseContactKernel a (phaseContactAngle i) :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (phaseContactWeight_nonneg i) (hp _))
  have he := phaseContactDeficit_eq_contacts_add_penalties ha hs
  linarith

/-- The same exact deficit also controls the contact values. Efficient
kernels therefore approach zero at the positively weighted contact angles. -/
theorem phaseContact_contact_values_le_deficit {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n)) :
    (∑ i : Fin 5, (phaseContactWeight i : ℝ) * phaseContactKernel a (phaseContactAngle i)) ≤
      phaseContactDeficit a := by
  have he := phaseContactDeficit_eq_contacts_add_penalties ha hs
  have hf : 0 ≤ ∑' n : ℕ, a n * phaseContactPenalty n :=
    tsum_nonneg (fun n ↦ mul_nonneg (ha n) (phaseContactPenalty_nonneg n))
  linarith

/-- A candidate within `epsilon` of the certificate's efficiency bound
has at most `64 * epsilon` coefficient mass outside the sparse set. -/
theorem phaseContact_offSupport_mass_le_of_efficiency {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hs : Summable (fun n ↦ phaseContactCost n * a n))
    (hp : ∀ t, 0 ≤ phaseContactKernel a t) {epsilon : ℝ}
    (he : (8801 / 500000 : ℝ) * phaseContactBudget a - epsilon ≤ phaseContactSource a) :
    (∑' n : ℕ, if n ∈ phaseContactFrequencies then 0 else a n) ≤ 64 * epsilon := by
  have h := phaseContact_offSupport_mass_le_sixtyFour_mul_deficit ha hs hp
  unfold phaseContactDeficit at h
  linarith

end

end RiemannGaussian
