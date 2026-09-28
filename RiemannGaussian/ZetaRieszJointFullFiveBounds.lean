/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPositiveFiveWholeBudget
import RiemannGaussian.ZetaRieszPositiveFiveBoundary
import RiemannGaussian.ZetaRieszJointOwnerPayment

/-!
# Spending the full positive-five interior in the whole signed ledger

Directed costs retain all favorable individual observations. The full
interior replaces the old fixed sector; no allowance is spent twice.
-/

namespace RiemannGaussian.ZetaRieszJointFullFiveBounds
noncomputable section
open Filter Topology
open scoped BigOperators Classical

/-- A directed debit pays a subset of the original signed rest and retains
all favorable atoms, including every earlier favorable subpopulation. -/
theorem floor_after_directed_payment {S D : Finset ℕ} (f : ℕ → ℂ) {d g whole : ℝ}
    (hD : D ⊆ S) (hcost : (∑ n ∈ D, max 0 (-(f n).re)) ≤ d)
    (hpaid : (∑ n ∈ S, f n).re+g ≤ whole) :
    (∑ n ∈ S\D, f n).re+(∑ n ∈ D, max 0 (f n).re)+g-d ≤ whole := by
  have he := congrArg Complex.re (Finset.sum_sdiff hD (f := f))
  simp only [Complex.add_re] at he
  have hparts : (∑ n ∈ D, f n).re =
      (∑ n ∈ D, max 0 (f n).re)-(∑ n ∈ D, max 0 (-(f n).re)) := by
    rw [← Finset.sum_sub_distrib]
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    simpa only [max_comm] using (max_zero_sub_max_neg_zero_eq_self (f n).re).symm
  linarith only [he,hparts,hcost,hpaid]

/-- The opposite directed debit retains every favorable upper atom and
the identical original support and coefficient. -/
theorem ceiling_after_directed_payment {S D : Finset ℕ} (f : ℕ → ℂ) {d g whole : ℝ}
    (hD : D ⊆ S) (hcost : (∑ n ∈ D, max 0 (f n).re) ≤ d)
    (hpaid : whole ≤ (∑ n ∈ S, f n).re-g) :
    whole ≤ (∑ n ∈ S\D, f n).re+(∑ n ∈ D, min (f n).re 0)-g+d := by
  have he := congrArg Complex.re (Finset.sum_sdiff hD (f := f))
  simp only [Complex.add_re] at he
  have hparts : (∑ n ∈ D, f n).re =
      (∑ n ∈ D, min (f n).re 0)+(∑ n ∈ D, max 0 (f n).re) := by
    rw [← Finset.sum_add_distrib]
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _
    simpa only [max_comm,add_zero] using (min_add_max (f n).re 0).symm
  linarith only [he,hparts,hcost,hpaid]

/-- No favorable observation on an older paid subset is lost when the
new full interior replaces that subset. -/
theorem positive_observation_mono {B I : Finset ℕ} (hBI : B ⊆ I) (f : ℕ → ℂ) :
    max (∑ n ∈ B, f n).re 0 ≤ ∑ n ∈ I, max 0 (f n).re := by
  apply max_le
  · have h := Finset.sum_le_sum (s := B) (fun n _ => le_max_right 0 (f n).re)
    simp only [Complex.re_sum] at ⊢
    exact h.trans (Finset.sum_le_sum_of_subset_of_nonneg hBI (fun n _ _ => le_max_left _ _))
  · exact Finset.sum_nonneg (fun n _ => le_max_left _ _)

/-- The upper observations are preserved in the same direction. -/
theorem negative_observation_mono {B I : Finset ℕ} (hBI : B ⊆ I) (f : ℕ → ℂ) :
    (∑ n ∈ I, min (f n).re 0) ≤ min (∑ n ∈ B, f n).re 0 := by
  have hp := positive_observation_mono hBI (fun n => -f n)
  simp only [Complex.neg_re,Finset.sum_neg_distrib] at hp
  have he (x : ℝ) : max 0 (-x) = -min x 0 := by
    by_cases hx : 0 ≤ x
    · simp only [min_eq_right hx,max_eq_left (neg_nonpos.mpr hx),neg_zero]
    · simp only [min_eq_left (le_of_not_ge hx),max_eq_right (neg_nonneg.mpr (le_of_not_ge hx))]
  simp only [he,Finset.sum_neg_distrib] at hp
  rw [max_comm (-(∑ n ∈ B, f n).re) 0,he] at hp
  linarith only [hp]

end
end RiemannGaussian.ZetaRieszJointFullFiveBounds
