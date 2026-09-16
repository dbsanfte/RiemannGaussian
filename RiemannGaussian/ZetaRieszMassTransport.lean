/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPairMatching

/-!
# Preserve unused amplitudes through successive pairs

Every sent pair and remaining original amplitude stays explicit. Complete
fallback coverage controls the final unsent mass, but all fallback chord
costs remain in the whole bound. A source-scale bound for the sent sum and
a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszMassTransport
noncomputable section
open scoped BigOperators Classical

/-- The original complex ray, with the zero vector kept at zero. -/
def ray (z : ℂ) : ℂ := ‖z‖⁻¹ • z

/-- The ray has unit norm at every nonzero original amplitude. -/
theorem norm_ray {z : ℂ} (hz : z ≠ 0) : ‖ray z‖ = 1 := by
  rw [ray, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)

/-- Zero amplitudes cause no singular phase convention in the allowance. -/
theorem norm_ray_le (z : ℂ) : ‖ray z‖ ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz, ray]
  · exact (norm_ray hz).le

/-- Multiplying by the original norm recovers the entire complex amplitude. -/
theorem norm_smul_ray (z : ℂ) : ‖z‖ • ray z = z := by
  by_cases hz : z = 0
  · simp [hz, ray]
  · rw [ray, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_smul]

/-- The unsent mass stays on the same original ray. -/
def remainder (a : ℝ) (z : ℂ) : ℂ := (‖z‖ - a) • ray z

/-- Removing a supported nonnegative amount preserves its exact norm budget. -/
theorem norm_remainder {a : ℝ} {z : ℂ} (ha : 0 ≤ a) (haz : a ≤ ‖z‖) :
    ‖remainder a z‖ = ‖z‖ - a := by
  by_cases hz : z = 0
  · have ha0 : a = 0 := le_antisymm (by simpa only [hz, norm_zero] using haz) ha
    simp [hz, ha0, remainder, ray]
  · rw [remainder, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr haz), norm_ray hz, mul_one]

/-- The sent part and remaining part recover the original vector exactly. -/
theorem sent_add_remainder (a : ℝ) (z : ℂ) :
    a • ray z + remainder a z = z := by
  rw [remainder, ← add_smul, add_sub_cancel, norm_smul_ray]

/-- The largest equal amount available at both ends of a candidate pair. -/
def pairMass (z w : ℂ) : ℝ := min ‖z‖ ‖w‖

/-- Both retained directions contribute through their exact chord. -/
def pairCost (z w : ℂ) : ℝ := pairMass z w * ‖ray z + ray w‖

/-- The equal-mass pair retains its complete complex direction. -/
theorem norm_sent_pair (z w : ℂ) :
    ‖pairMass z w • (ray z + ray w)‖ = pairCost z w := by
  have hm : 0 ≤ pairMass z w := le_min (norm_nonneg _) (norm_nonneg _)
  rw [norm_smul, Real.norm_of_nonneg hm]
  rfl

/-- Every sent pair costs at most the two masses it removed. -/
theorem pairCost_le (z w : ℂ) : pairCost z w ≤ 2 * pairMass z w := by
  have hc : ‖ray z + ray w‖ ≤ 2 := (norm_add_le _ _).trans (by linarith [norm_ray_le z, norm_ray_le w])
  have hm : 0 ≤ pairMass z w := le_min (norm_nonneg _) (norm_nonneg _)
  unfold pairCost
  nlinarith

/-- Equal-mass extraction leaves both original phases and both residuals. -/
theorem pair_decomposition (z w : ℂ) :
    z + w = pairMass z w • (ray z + ray w) +
      (remainder (pairMass z w) z + remainder (pairMass z w) w) := by
  have hz := sent_add_remainder (pairMass z w) z
  have hw := sent_add_remainder (pairMass z w) w
  rw [smul_add]
  linear_combination -hz - hw

/-- A complete pair has an independent chord cost and exact unsent mass. -/
theorem norm_pair_le_transport (z w : ℂ) :
    ‖z + w‖ ≤ pairCost z w + (‖z‖ + ‖w‖ - 2 * pairMass z w) := by
  have hm : 0 ≤ pairMass z w := le_min (norm_nonneg _) (norm_nonneg _)
  calc
    _ = ‖pairMass z w • (ray z + ray w) +
        (remainder (pairMass z w) z + remainder (pairMass z w) w)‖ := by rw [← pair_decomposition]
    _ ≤ pairCost z w + (‖remainder (pairMass z w) z‖ + ‖remainder (pairMass z w) w‖) := by
      apply (norm_add_le _ _).trans
      rw [norm_sent_pair]
      exact add_le_add (le_refl _) (norm_add_le (remainder (pairMass z w) z) (remainder (pairMass z w) w))
    _ = _ := by rw [norm_remainder hm (min_le_left _ _), norm_remainder hm (min_le_right _ _)]; ring

/-- One actual edge removes only equal available mass from its two ends. -/
def transportStep (f : ℕ → ℂ) (e : ℕ × ℕ) (n : ℕ) : ℂ :=
  if n = e.1 then remainder (pairMass (f e.1) (f e.2)) (f e.1)
  else if n = e.2 then remainder (pairMass (f e.1) (f e.2)) (f e.2)
  else f n

/-- A transport step preserves the full complex sum with its sent pair. -/
theorem sum_transportStep (S : Finset ℕ) (f : ℕ → ℂ) {e : ℕ × ℕ}
    (hi : e.1 ∈ S) (hj : e.2 ∈ S) (hne : e.1 ≠ e.2) :
    (∑ n ∈ S, f n) = pairMass (f e.1) (f e.2) • (ray (f e.1) + ray (f e.2)) +
      ∑ n ∈ S, transportStep f e n := by
  let m := pairMass (f e.1) (f e.2)
  have he (n : ℕ) : f n = transportStep f e n +
      (if n = e.1 then m • ray (f e.1) else 0) +
      (if n = e.2 then m • ray (f e.2) else 0) := by
    by_cases hn : n = e.1
    · subst n
      simp only [transportStep, ite_true, if_neg hne, add_zero]
      exact (add_comm _ _).trans (sent_add_remainder m (f e.1)) |>.symm
    · by_cases hn' : n = e.2
      · subst n
        simp only [transportStep, if_neg hn, ite_true, add_zero]
        exact (add_comm _ _).trans (sent_add_remainder m (f e.2)) |>.symm
      · simp [transportStep, hn, hn']
  have hs := Finset.sum_congr (s₁ := S) rfl (fun n _ => he n)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hi, if_pos hj] at hs
  rw [smul_add]
  dsimp [m] at hs
  simp only [Complex.real_smul]
  linear_combination hs

/-- Every sent amount is removed exactly twice from the absolute budget. -/
theorem mass_transportStep (S : Finset ℕ) (f : ℕ → ℂ) {e : ℕ × ℕ}
    (hi : e.1 ∈ S) (hj : e.2 ∈ S) (hne : e.1 ≠ e.2) :
    (∑ n ∈ S, ‖transportStep f e n‖) =
      (∑ n ∈ S, ‖f n‖) - 2 * pairMass (f e.1) (f e.2) := by
  let m := pairMass (f e.1) (f e.2)
  have hm : 0 ≤ m := le_min (norm_nonneg _) (norm_nonneg _)
  have he (n : ℕ) : ‖f n‖ = ‖transportStep f e n‖ +
      (if n = e.1 then m else 0) + (if n = e.2 then m else 0) := by
    by_cases hn : n = e.1
    · subst n
      simp only [transportStep, ite_true, if_neg hne, add_zero]
      rw [norm_remainder hm (min_le_left _ _)]
      dsimp [m]
      ring
    · by_cases hn' : n = e.2
      · subst n
        simp only [transportStep, if_neg hn, ite_true, add_zero]
        rw [norm_remainder hm (min_le_right _ _)]
        dsimp [m]
        ring
      · simp [transportStep, hn, hn']
  have hs := Finset.sum_congr (s₁ := S) rfl (fun n _ => he n)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hi, if_pos hj] at hs
  dsimp [m] at hs
  linarith

/-- The whole finite support pays the exact chord and keeps its remainder. -/
theorem norm_sum_le_transportStep (S : Finset ℕ) (f : ℕ → ℂ) {e : ℕ × ℕ}
    (hi : e.1 ∈ S) (hj : e.2 ∈ S) (hne : e.1 ≠ e.2) :
    ‖∑ n ∈ S, f n‖ ≤ pairCost (f e.1) (f e.2) + ‖∑ n ∈ S, transportStep f e n‖ := by
  rw [sum_transportStep S f hi hj hne]
  exact (norm_add_le _ _).trans_eq (by rw [norm_sent_pair])

/-- A finite sequence pays each sent chord, then the actual unsent mass.
The same vertex may participate again using only its surviving amplitude. -/
def transportCost (S : Finset ℕ) (f : ℕ → ℂ) : List (ℕ × ℕ) → ℝ
  | [] => ∑ n ∈ S, ‖f n‖
  | e :: es => pairCost (f e.1) (f e.2) + transportCost S (transportStep f e) es

/-- The complete finite sequence is valid even when edges share vertices. -/
theorem norm_sum_le_transportCost (S : Finset ℕ) (f : ℕ → ℂ) (es : List (ℕ × ℕ))
    (he : ∀ e ∈ es, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2) :
    ‖∑ n ∈ S, f n‖ ≤ transportCost S f es := by
  induction es generalizing f with
  | nil => exact norm_sum_le _ _
  | cons e es ih =>
    have h := he e (List.mem_cons_self ..)
    exact (norm_sum_le_transportStep S f h.1 h.2.1 h.2.2).trans
      (add_le_add (le_refl _) (ih (transportStep f e) (fun a ha => he a (List.mem_cons_of_mem _ ha))))

/-- Successive partial matching never worsens the original triangle bound. -/
theorem transportCost_le_mass (S : Finset ℕ) (f : ℕ → ℂ) (es : List (ℕ × ℕ))
    (he : ∀ e ∈ es, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2) :
    transportCost S f es ≤ ∑ n ∈ S, ‖f n‖ := by
  induction es generalizing f with
  | nil => exact le_refl _
  | cons e es ih =>
    have h := he e (List.mem_cons_self ..)
    have hc := ih (transportStep f e) (fun a ha => he a (List.mem_cons_of_mem _ ha))
    have hm := mass_transportStep S f h.1 h.2.1 h.2.2
    have hp := pairCost_le (f e.1) (f e.2)
    change pairCost _ _ + transportCost S (transportStep f e) es ≤ _
    linarith

/-- The final unsent amplitudes retain their original integer labels. -/
def remainingAfter (f : ℕ → ℂ) : List (ℕ × ℕ) → ℕ → ℂ
  | [] => f
  | e :: es => remainingAfter (transportStep f e) es

/-- All sent pairs remain one complex sum, retaining cross-pair phases. -/
def sentAfter (f : ℕ → ℂ) : List (ℕ × ℕ) → ℂ
  | [] => 0
  | e :: es => pairMass (f e.1) (f e.2) • (ray (f e.1) + ray (f e.2)) +
      sentAfter (transportStep f e) es

/-- The complete transport algorithm preserves every complex contribution. -/
theorem sum_eq_sent_add_remaining (S : Finset ℕ) (f : ℕ → ℂ) (es : List (ℕ × ℕ))
    (he : ∀ e ∈ es, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2) :
    (∑ n ∈ S, f n) = sentAfter f es + ∑ n ∈ S, remainingAfter f es n := by
  induction es generalizing f with
  | nil => simp [sentAfter, remainingAfter]
  | cons e es ih =>
    have h := he e (List.mem_cons_self ..)
    have hs := ih (transportStep f e) (fun a ha => he a (List.mem_cons_of_mem _ ha))
    rw [sum_transportStep S f h.1 h.2.1 h.2.2, hs]
    simp only [sentAfter, remainingAfter, add_assoc]

end
end RiemannGaussian.ZetaRieszMassTransport
