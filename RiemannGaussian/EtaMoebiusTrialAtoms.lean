import RiemannGaussian.MoebiusHarmonicHyperbola

/-!
# Balanced Möbius trial atoms on the actual physical scale grid

The signed atom is `1_[n,∞) - min(x,n)/n * 1_[1,∞)`. It is the
difference of two bounded monotone
channels. Keeping both channels gives a total variation bound of two
on the actual grid `x_j=d/(j+1)`, without losing the signed atom itself.
These atoms implement subtraction of the finite harmonic value at one.
-/

open scoped ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The jump at the original positive integer threshold. -/
def pairedEtaMoebiusTrialStep (n : ℕ) (x : ℝ) : ℝ := if (n : ℝ) ≤ x then 1 else 0

/-- The bounded ramp which supplies the exact harmonic correction to the jump. -/
def pairedEtaMoebiusTrialRamp (n : ℕ) (x : ℝ) : ℝ :=
  if 1 ≤ x then min x (n : ℝ) / n else 0

/-- The signed arithmetic atom retains both its jump and harmonic correction. -/
def pairedEtaMoebiusTrialAtom (n : ℕ) (x : ℝ) : ℝ :=
  pairedEtaMoebiusTrialStep n x - pairedEtaMoebiusTrialRamp n x

/-- The step channel is monotone before it is combined with the opposite ramp channel. -/
theorem pairedEtaMoebiusTrialStep_monotone (n : ℕ) : Monotone (pairedEtaMoebiusTrialStep n) := by
  intro x y hxy
  by_cases hx : (n : ℝ) ≤ x
  · simp [pairedEtaMoebiusTrialStep, hx, hx.trans hxy]
  · by_cases hy : (n : ℝ) ≤ y <;> simp [pairedEtaMoebiusTrialStep, hx, hy]

/-- The complete step channel lies between zero and one. -/
theorem pairedEtaMoebiusTrialStep_bounds (n : ℕ) (x : ℝ) :
    0 ≤ pairedEtaMoebiusTrialStep n x ∧ pairedEtaMoebiusTrialStep n x ≤ 1 := by
  unfold pairedEtaMoebiusTrialStep
  split_ifs <;> norm_num

/-- The harmonic ramp is monotone at every positive integer threshold. -/
theorem pairedEtaMoebiusTrialRamp_monotone {n : ℕ} (hn : 1 ≤ n) :
    Monotone (pairedEtaMoebiusTrialRamp n) := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  intro x y hxy
  by_cases hx : (1 : ℝ) ≤ x
  · simp only [pairedEtaMoebiusTrialRamp, if_pos hx, if_pos (hx.trans hxy)]
    exact div_le_div_of_nonneg_right (min_le_min hxy le_rfl) hnp.le
  · by_cases hy : (1 : ℝ) ≤ y
    · simp only [pairedEtaMoebiusTrialRamp, if_neg hx, if_pos hy]
      exact div_nonneg (le_min (by linarith) hnp.le) hnp.le
    · simp [pairedEtaMoebiusTrialRamp, hx, hy]

/-- The whole harmonic correction lies between zero and one, independently of its integer threshold. -/
theorem pairedEtaMoebiusTrialRamp_bounds {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    0 ≤ pairedEtaMoebiusTrialRamp n x ∧ pairedEtaMoebiusTrialRamp n x ≤ 1 := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hx : (1 : ℝ) ≤ x
  · simp only [pairedEtaMoebiusTrialRamp, if_pos hx]
    exact ⟨div_nonneg (le_min (by linarith) hnp.le) hnp.le,
      (div_le_one hnp).mpr (min_le_right _ _)⟩
  · simp [pairedEtaMoebiusTrialRamp, hx]

/-- Below the original unit threshold, both signed channels vanish exactly. -/
theorem pairedEtaMoebiusTrialAtom_eq_zero_of_lt_one {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x < 1) :
    pairedEtaMoebiusTrialAtom n x = 0 := by
  have hnx : ¬ (n : ℝ) ≤ x := by
    have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  simp [pairedEtaMoebiusTrialAtom, pairedEtaMoebiusTrialStep, pairedEtaMoebiusTrialRamp, hnx, hx.not_ge]

/-- Beyond its integer endpoint the step and ramp cancel exactly. -/
theorem pairedEtaMoebiusTrialAtom_eq_zero_of_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : (n : ℝ) ≤ x) :
    pairedEtaMoebiusTrialAtom n x = 0 := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  simp [pairedEtaMoebiusTrialAtom, pairedEtaMoebiusTrialStep, pairedEtaMoebiusTrialRamp,
    hx, hn1.trans hx, hn0]

/-- Between the unit and integer thresholds the original signed atom is exactly the negative harmonic ramp. -/
theorem pairedEtaMoebiusTrialAtom_eq_neg_div {n : ℕ} {x : ℝ} (hx : 1 ≤ x) (hxn : x < n) :
    pairedEtaMoebiusTrialAtom n x = -x / n := by
  simp [pairedEtaMoebiusTrialAtom, pairedEtaMoebiusTrialStep, pairedEtaMoebiusTrialRamp,
    hx, hxn.not_ge, min_eq_left hxn.le, neg_div]

/-- The reciprocal coordinates of the actual uniform physical scale grid decrease at every step. -/
theorem pairedEtaMoebiusTrialGrid_antitone_step (d j : ℕ) :
    (d : ℝ) / (j + 2 : ℝ) ≤ (d : ℝ) / (j + 1 : ℝ) :=
  div_le_div_of_nonneg_left (Nat.cast_nonneg d) (by positivity) (by linarith)

/-- The entire sampled variation of each signed arithmetic atom is at most two, with both channels retained in the proof. -/
theorem pairedEtaMoebiusTrialAtom_grid_variation_le (d : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (∑ j : Fin d, |pairedEtaMoebiusTrialAtom n ((d : ℝ) / (j.1 + 1 : ℝ)) -
      pairedEtaMoebiusTrialAtom n ((d : ℝ) / (j.1 + 2 : ℝ))|) ≤ 2 := by
  let u : ℕ → ℝ := fun j ↦ pairedEtaMoebiusTrialStep n ((d : ℝ) / (j + 1 : ℝ))
  let v : ℕ → ℝ := fun j ↦ pairedEtaMoebiusTrialRamp n ((d : ℝ) / (j + 1 : ℝ))
  have hu (j : ℕ) : u (j + 1) ≤ u j := by
    simpa only [u, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      pairedEtaMoebiusTrialStep_monotone n (pairedEtaMoebiusTrialGrid_antitone_step d j)
  have hv (j : ℕ) : v (j + 1) ≤ v j := by
    simpa only [v, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      pairedEtaMoebiusTrialRamp_monotone hn (pairedEtaMoebiusTrialGrid_antitone_step d j)
  have hpoint (j : ℕ) : |(u j - v j) - (u (j + 1) - v (j + 1))| ≤
      (u j - u (j + 1)) + (v j - v (j + 1)) := by
    rw [show (u j - v j) - (u (j + 1) - v (j + 1)) =
      (u j - u (j + 1)) - (v j - v (j + 1)) by ring]
    simpa only [abs_of_nonneg (sub_nonneg.mpr (hu j)), abs_of_nonneg (sub_nonneg.mpr (hv j))]
      using abs_sub (u j - u (j + 1)) (v j - v (j + 1))
  have hsum := Finset.sum_le_sum (s := Finset.range d) (fun j _ ↦ hpoint j)
  rw [Finset.sum_add_distrib, Finset.sum_range_sub', Finset.sum_range_sub'] at hsum
  have hbound : u 0 - u d + (v 0 - v d) ≤ 2 := by
    have hu0 := (pairedEtaMoebiusTrialStep_bounds n ((d : ℝ) / (0 + 1 : ℝ))).2
    have hud := (pairedEtaMoebiusTrialStep_bounds n ((d : ℝ) / (d + 1 : ℝ))).1
    have hv0 := (pairedEtaMoebiusTrialRamp_bounds hn ((d : ℝ) / (0 + 1 : ℝ))).2
    have hvd := (pairedEtaMoebiusTrialRamp_bounds hn ((d : ℝ) / (d + 1 : ℝ))).1
    dsimp [u, v]
    linarith
  have h := hsum.trans hbound
  rw [← Fin.sum_univ_eq_sum_range] at h
  simpa only [u, v, pairedEtaMoebiusTrialAtom, Nat.cast_add, Nat.cast_one,
    add_assoc, one_add_one_eq_two] using h

end

end RiemannGaussian
