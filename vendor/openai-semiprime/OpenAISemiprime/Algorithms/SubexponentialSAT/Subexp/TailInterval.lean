import OpenAISemiprime.Algorithms.SubexponentialSAT.LeanCompat
import OpenAISemiprime.Algorithms.SubexponentialSAT.SubexpSwapMultiplicity

namespace OAI.Algorithms

/-!
# A computable centered interval for the multicolor binomial tail

The swap mean is between (Q - 1) / 4 and (Q - 1) / 2.  Taking the natural
floor of mean - R / 2 gives an interval of R consecutive integer weights.
The rounding error is at most one, absorbed by R ≥ 4.
-/

namespace SubexponentialSAT.Subexp.TailInterval

open SubexponentialSAT.SubexpSwapMultiplicity
open scoped BigOperators

/-- The mean of the Q - 1 independent swap signs. -/
def mean (r Q : ℕ) : ℚ := (Q - 1 : ℕ) * negativeProbability r

/-- A rational-floor computation, with no choice or search oracle. -/
def centeredStart (μ : ℚ) (R : ℕ) : ℕ := ⌊μ - (R : ℚ) / 2⌋₊

/-- The concrete interval start used for the multicolor matrix. -/
def intervalStart (r Q R : ℕ) : ℕ := centeredStart (mean r Q) R

theorem centeredStart_bounds {μ : ℚ} {R : ℕ} (hcenter : (R : ℚ) / 2 ≤ μ) :
    (centeredStart μ R : ℚ) ≤ μ - (R : ℚ) / 2 ∧
      μ - (R : ℚ) / 2 < (centeredStart μ R : ℚ) + 1 := by
  exact ⟨Nat.floor_le (by linarith), Nat.lt_floor_add_one _⟩

/-- The floor rounding error preserves distance at least R / 4 outside
the interval.  This holds for every natural weight, not just weights ≤ Q - 1. -/
theorem centeredStart_deviation {μ : ℚ} {R w : ℕ}
    (hR : 4 ≤ R) (hcenter : (R : ℚ) / 2 ≤ μ)
    (hw : w ∉ Finset.Ico (centeredStart μ R) (centeredStart μ R + R)) :
    (R : ℚ) ^ 2 ≤ 16 * ((w : ℚ) - μ) ^ 2 := by
  obtain ⟨hlo, hhi⟩ := centeredStart_bounds hcenter
  have hR0 : (0 : ℚ) ≤ R := Nat.cast_nonneg _
  have hR4 : (4 : ℚ) ≤ R := by exact_mod_cast hR
  by_cases hleft : w < centeredStart μ R
  · have hwQ : (w : ℚ) < centeredStart μ R := by exact_mod_cast hleft
    have hdist : (R : ℚ) ≤ 4 * (μ - w) := by linarith
    have hs := mul_self_le_mul_self hR0 hdist
    nlinarith
  · have hright : centeredStart μ R + R ≤ w := by
      simp only [Finset.mem_Ico] at hw
      omega
    have hwQ : (centeredStart μ R : ℚ) + R ≤ w := by exact_mod_cast hright
    have hdist : (R : ℚ) ≤ 4 * (w - μ) := by linarith
    have hs := mul_self_le_mul_self hR0 hdist
    nlinarith

theorem mean_bounds (r Q : ℕ) (hr : 2 ≤ r) :
    ((Q - 1 : ℕ) : ℚ) / 4 ≤ mean r Q ∧
      mean r Q ≤ ((Q - 1 : ℕ) : ℚ) / 2 := by
  obtain ⟨hlo, hhi⟩ := negativeProbability_bounds r hr
  have hlo' := mul_le_mul_of_nonneg_left hlo (show (0 : ℚ) ≤ (Q - 1 : ℕ) from Nat.cast_nonneg _)
  have hhi' := mul_le_mul_of_nonneg_left hhi.le (show (0 : ℚ) ≤ (Q - 1 : ℕ) from Nat.cast_nonneg _)
  dsimp [mean]
  constructor <;> linarith

theorem half_width_le_mean {r Q R : ℕ} (hr : 2 ≤ r)
    (hsize : 4 * R ≤ Q) :
    (R : ℚ) / 2 ≤ mean r Q := by
  have hq : 2 * R ≤ Q - 1 := by omega
  have hqQ : (2 : ℚ) * R ≤ (Q - 1 : ℕ) := by exact_mod_cast hq
  have hlo := (mean_bounds r Q hr).1
  linarith

/-- The interval fits within the available weights 0,...,Q-1. -/
theorem intervalStart_end_le {r Q R : ℕ} (hr : 2 ≤ r)
    (hR : 4 ≤ R) (hsize : 4 * R ≤ Q) :
    intervalStart r Q R + R ≤ Q := by
  have hcenter := half_width_le_mean hr hsize
  have hlo := (centeredStart_bounds hcenter).1
  have hmean := (mean_bounds r Q hr).2
  have hq : ((Q - 1 : ℕ) : ℚ) ≤ Q := by
    exact_mod_cast Nat.sub_le Q 1
  have hRQ : (R : ℚ) ≤ Q := by
    exact_mod_cast (show R ≤ Q by omega)
  have hend : (centeredStart (mean r Q) R : ℚ) + R ≤ Q := by linarith
  exact_mod_cast hend

/-- Required geometric hypothesis for the exact swap-probability tail bound. -/
theorem intervalStart_deviation {r Q R w : ℕ} (hr : 2 ≤ r)
    (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hw : w ∉ Finset.Ico (intervalStart r Q R) (intervalStart r Q R + R)) :
    (R : ℚ) ^ 2 ≤
      16 * ((w : ℚ) - (Q - 1 : ℕ) * negativeProbability r) ^ 2 :=
  centeredStart_deviation hR (half_width_le_mean hr hsize) hw

/-- Every integer weight within R / 4 of the mean belongs to the chosen interval. -/
theorem interval_contains_near_mean {r Q R w : ℕ} (hr : 2 ≤ r)
    (hR : 4 ≤ R) (hsize : 4 * R ≤ Q)
    (hnear : |(w : ℚ) - mean r Q| < (R : ℚ) / 4) :
    w ∈ Finset.Ico (intervalStart r Q R) (intervalStart r Q R + R) := by
  by_contra hnot
  have hsep := intervalStart_deviation hr hR hsize hnot
  change (R : ℚ) ^ 2 ≤ 16 * ((w : ℚ) - mean r Q) ^ 2 at hsep
  have hsq := mul_self_lt_mul_self (abs_nonneg ((w : ℚ) - mean r Q)) hnear
  nlinarith [sq_abs ((w : ℚ) - mean r Q)]

@[simp] theorem interval_card (r Q R : ℕ) :
    (Finset.Ico (intervalStart r Q R) (intervalStart r Q R + R)).card = R := by
  simp

theorem interval_subset_range {r Q R : ℕ} (hr : 2 ≤ r)
    (hR : 4 ≤ R) (hsize : 4 * R ≤ Q) :
    Finset.Ico (intervalStart r Q R) (intervalStart r Q R + R) ⊆ Finset.range Q := by
  intro w hw
  apply Finset.mem_range.mpr
  exact lt_of_lt_of_le (Finset.mem_Ico.mp hw).2 (intervalStart_end_le hr hR hsize)

/-- A fully explicit interval, including its endpoint and geometric guarantees. -/
theorem exists_interval {r Q R : ℕ} (hr : 2 ≤ r)
    (hR : 32 ≤ R) (hsize : 4 * R ≤ Q) :
    ∃ A : ℕ, A + R ≤ Q ∧ (Finset.Ico A (A + R)).card = R ∧
      ∀ w : ℕ, w ∉ Finset.Ico A (A + R) →
        (R : ℚ) ^ 2 ≤
          16 * ((w : ℚ) - (Q - 1 : ℕ) * negativeProbability r) ^ 2 := by
  refine ⟨intervalStart r Q R, intervalStart_end_le hr (by omega) hsize,
    interval_card r Q R, ?_⟩
  intro w hw
  exact intervalStart_deviation hr (by omega) hsize hw

/-- The numeric budget now implies the tail estimate without an additional
interval-location hypothesis.  The probability argument is reused verbatim. -/
theorem interval_tail_bound {r Q R Δ s : ℕ} (hr : 2 ≤ r)
    (hR : 32 ≤ R) (hsize : 4 * R ≤ Q) (hΔ : 0 < Δ) (hs : 0 < s)
    (hbudget : 16 * Q * Δ * s ≤ R ^ 2) :
    (∑ w ∈ Finset.range ((Q - 1) + 1),
      if w ∈ Finset.Ico (intervalStart r Q R) (intervalStart r Q R + R) then 0
      else swapProbability r (Q - 1) w) ≤ 1 / ((s : ℚ) * Δ) := by
  apply tail_bound_of_budget r Q (intervalStart r Q R) R Δ s
    (by omega) (by omega) hΔ hs hbudget
  intro w _ hw
  exact intervalStart_deviation hr (by omega) hsize hw

end SubexponentialSAT.Subexp.TailInterval

end OAI.Algorithms
