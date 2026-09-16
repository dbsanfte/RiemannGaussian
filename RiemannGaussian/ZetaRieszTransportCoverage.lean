/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMassTransport
import RiemannGaussian.ZetaRieszPrimeMatching
import RiemannGaussian.ZetaArithmeticLocalEnergy

/-!
# Pay the final unsent mass with diagonal energy

Every sent pair and remaining original amplitude stays explicit. Complete
fallback coverage controls the final unsent mass, but all fallback chord
costs remain in the whole bound. A source-scale bound for the sent sum and
a new zero-free region remain open.
-/

namespace RiemannGaussian.ZetaRieszTransportCoverage
noncomputable section
open scoped BigOperators Classical
open ZetaRieszMassTransport

/-- A spent amplitude can never reappear in a later transport step. -/
theorem transportStep_zero (f : ℕ → ℂ) (e : ℕ × ℕ) {n : ℕ} (hn : f n = 0) :
    transportStep f e n = 0 := by
  by_cases hi : n = e.1
  · subst n
    simp [transportStep, hn, remainder, ray]
  · by_cases hj : n = e.2
    · subst n
      simp [transportStep, hi, hn, remainder, ray]
    · simp [transportStep, hi, hj, hn]

/-- No individual residual amplitude can grow during transport. -/
theorem norm_transportStep_le (f : ℕ → ℂ) (e : ℕ × ℕ) (n : ℕ) :
    ‖transportStep f e n‖ ≤ ‖f n‖ := by
  have hm : 0 ≤ pairMass (f e.1) (f e.2) := le_min (norm_nonneg _) (norm_nonneg _)
  by_cases hi : n = e.1
  · subst n
    simp only [transportStep, ite_true]
    rw [norm_remainder hm (min_le_left _ _)]
    linarith
  · by_cases hj : n = e.2
    · subst n
      simp only [transportStep, if_neg hi, ite_true]
      rw [norm_remainder hm (min_le_right _ _)]
      linarith
    · simp [transportStep, hi, hj]

/-- Each processed distinct pair exhausts at least one endpoint. -/
theorem transportStep_kills_end (f : ℕ → ℂ) {e : ℕ × ℕ} (he : e.1 ≠ e.2) :
    transportStep f e e.1 = 0 ∨ transportStep f e e.2 = 0 := by
  rcases le_total ‖f e.1‖ ‖f e.2‖ with h | h
  · left
    simp [transportStep, pairMass, min_eq_left h, remainder]
  · right
    simp [transportStep, he.symm, pairMass, min_eq_right h, remainder]

/-- Exhausted original labels stay exhausted after every later pair. -/
theorem remainingAfter_zero (f : ℕ → ℂ) (es : List (ℕ × ℕ)) {n : ℕ} (hn : f n = 0) :
    remainingAfter f es n = 0 := by
  induction es generalizing f with
  | nil => exact hn
  | cons e es ih => exact ih _ (transportStep_zero f e hn)

/-- The complete transport keeps every residual norm below its original norm. -/
theorem norm_remainingAfter_le (f : ℕ → ℂ) (es : List (ℕ × ℕ)) (n : ℕ) :
    ‖remainingAfter f es n‖ ≤ ‖f n‖ := by
  induction es generalizing f with
  | nil => exact le_refl _
  | cons e es ih => exact (ih _).trans (norm_transportStep_le f e n)

/-- The final nonzero support is independent of every processed edge. -/
theorem remainingAfter_edge_zero (f : ℕ → ℂ) (es : List (ℕ × ℕ))
    {e : ℕ × ℕ} (hem : e ∈ es) (hne : e.1 ≠ e.2) :
    remainingAfter f es e.1 = 0 ∨ remainingAfter f es e.2 = 0 := by
  induction es generalizing f with
  | nil => simp at hem
  | cons a es ih =>
    rcases List.mem_cons.mp hem with h | h
    · subst a
      rcases transportStep_kills_end f hne with hi | hj
      · exact Or.inl (remainingAfter_zero _ es hi)
      · exact Or.inr (remainingAfter_zero _ es hj)
    · exact ih _ h

/-- Processing every distinct original pair leaves at most one nonzero
amplitude. Its entire unsent squared mass is paid by the original diagonal
energy, regardless of the earlier ordering or shared vertices. -/
theorem remaining_mass_sq_le_diagonal (S : Finset ℕ) (f : ℕ → ℂ) (es : List (ℕ × ℕ))
    (hcover : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → (i,j) ∈ es) :
    (∑ n ∈ S, ‖remainingAfter f es n‖) ^ 2 ≤ ∑ n ∈ S, ‖f n‖ ^ 2 := by
  by_cases hz : ∀ n ∈ S, remainingAfter f es n = 0
  · have hs : (∑ n ∈ S, ‖remainingAfter f es n‖) = 0 :=
      Finset.sum_eq_zero (fun n hn => by rw [hz n hn, norm_zero])
    rw [hs, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · push Not at hz
    obtain ⟨j, hj, hj0⟩ := hz
    have hs : (∑ n ∈ S, ‖remainingAfter f es n‖) = ‖remainingAfter f es j‖ := by
      apply Finset.sum_eq_single_of_mem j hj
      intro i hi hij
      rcases remainingAfter_edge_zero f es (hcover i hi j hj hij) hij with h | h
      · exact norm_eq_zero.mpr h
      · exact (hj0 h).elim
    rw [hs]
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_remainingAfter_le f es j) 2).trans
      (Finset.single_le_sum (fun n _ => sq_nonneg ‖f n‖) hj)

/-- The full finite fallback visits every pair of distinct original labels.
Its chord costs must be paid; completing coverage is not free cancellation. -/
@[irreducible] def fullPairList (S : Finset ℕ) : List (ℕ × ℕ) :=
  ((S ×ˢ S).filter (fun e => e.1 ≠ e.2)).toList

/-- Every distinct original pair occurs in the explicit fallback. -/
theorem mem_fullPairList {S : Finset ℕ} {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) (hne : i ≠ j) :
    (i,j) ∈ fullPairList S := by
  simp only [fullPairList, Finset.mem_toList, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hi, hj⟩, hne⟩

/-- After any preliminary transport, the complete fallback pays the whole
remaining mass by the already proved diagonal energy of the actual band.
The bound is uniform in height, cutoff and transport order. -/
theorem actual_remaining_mass_sq_le (P : Polynomial ℂ) (N : ℕ) (t : ℝ)
    (earlyPairs : List (ℕ × ℕ)) {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hr1 : r < 1) :
    (∑ n ∈ zetaPrimeLogBand N, ‖remainingAfter (ZetaRieszConditionedEnergy.bandWeight L P N t)
      (earlyPairs ++ fullPairList (zetaPrimeLogBand N)) n‖) ^ 2 ≤
        zetaArithmeticEnergyConstant P r * (r⁻¹ ^ N) ^ 2 := by
  apply (remaining_mass_sq_le_diagonal (zetaPrimeLogBand N)
    (ZetaRieszConditionedEnergy.bandWeight L P N t) _ (fun i hi j hj hne =>
      List.mem_append.mpr (Or.inr (mem_fullPairList hi hj hne)))).trans
  have he : (∑ n ∈ zetaPrimeLogBand N, ‖ZetaRieszConditionedEnergy.bandWeight L P N t n‖ ^ 2) =
      ∑ n ∈ zetaPrimeLogBand N, ‖SquarefreeVaughanLogSource.coefficient L n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * t) n‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [ZetaRieszConditionedEnergy.bandWeight, if_pos hn]
  rw [he]
  exact sum_norm_zetaArithmeticKernel_sq_le _ (SquarefreeVaughanLogSource.norm_coefficient_le hL)
    P N t _ hr hr1

/-- The final unmatched mass at the actual moving cutoff tends to zero
at every source scale 0 < u < 1, for every fixed full polynomial. The
complete sent chord cost remains to be bounded and is not discarded. -/
theorem tendsto_actual_remaining_mass (P : Polynomial ℂ) (height : ℕ → ℝ)
    (earlyPairs : ℕ → List (ℕ × ℕ)) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Filter.Tendsto (fun N => u ^ (N + 1) *
      ∑ n ∈ zetaPrimeLogBand N, ‖remainingAfter
        (ZetaRieszConditionedEnergy.bandWeight (SquarefreeVaughanLogSource.length u N) P N (height N))
        (earlyPairs N ++ fullPairList (zetaPrimeLogBand N)) n‖) Filter.atTop (nhds 0) := by
  let r := (u + 1) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hur : u < r := by dsimp [r]; linarith
  have hq : u * r⁻¹ < 1 := by rw [← div_eq_mul_inv]; exact (div_lt_one hr).mpr hur
  let M (N : ℕ) : ℝ := u ^ (N + 1) *
    ∑ n ∈ zetaPrimeLogBand N, ‖remainingAfter
      (ZetaRieszConditionedEnergy.bandWeight (SquarefreeVaughanLogSource.length u N) P N (height N))
      (earlyPairs N ++ fullPairList (zetaPrimeLogBand N)) n‖
  have hM (N : ℕ) : 0 ≤ M N := mul_nonneg (pow_nonneg hu.le _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  have hb (N : ℕ) : (M N) ^ 2 ≤ zetaArithmeticEnergyConstant P r * (u * (u * r⁻¹) ^ N) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left
      (actual_remaining_mass_sq_le P N (height N) (earlyPairs N) (SquarefreeVaughanLogSource.length_pos u N) hr hr1)
      (sq_nonneg (u ^ (N + 1)))
    dsimp [M]
    rw [mul_pow]
    apply h.trans_eq
    simp only [mul_pow, pow_succ]
    ring
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one (mul_nonneg hu.le (inv_nonneg.mpr hr.le)) hq
  have he := ((hp.const_mul u).pow 2).const_mul (zetaArithmeticEnergyConstant P r)
  simp only [mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at he
  have hs : Filter.Tendsto (fun N => (M N) ^ 2) Filter.atTop (nhds 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hb he
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hs
  change Filter.Tendsto (fun N => Real.sqrt ((M N) ^ 2)) Filter.atTop (nhds (Real.sqrt 0)) at hsqrt
  have hroot (N : ℕ) : Real.sqrt ((M N) ^ 2) = M N := Real.sqrt_sq (hM N)
  simpa only [hroot, Real.sqrt_zero] using hsqrt

/-- Every fallback edge uses two distinct labels inside the original set. -/
theorem fullPairList_valid (S : Finset ℕ) :
    ∀ e ∈ fullPairList S, e.1 ∈ S ∧ e.2 ∈ S ∧ e.1 ≠ e.2 := by
  intro e he
  simp only [fullPairList, Finset.mem_toList, Finset.mem_filter, Finset.mem_product] at he
  exact ⟨he.1.1, he.1.2, he.2⟩

end
end RiemannGaussian.ZetaRieszTransportCoverage
