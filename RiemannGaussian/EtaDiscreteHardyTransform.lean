import RiemannGaussian.EtaMoebiusArithmeticTail

/-!
# The exact discrete Hardy transform of bounded arithmetic cells

The weighted tail integral of a constant arithmetic cell is a reciprocal
cell sum. Its Hardy transform has an exact finite energy identity, with
the full endpoint tail retained. For bounded cells that endpoint tends
to zero, giving an isometry between the weighted cell norm and the
ordinary square norm of the transformed cells.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The complete weighted integral after an arithmetic cell, retaining every subsequent cell. -/
def etaDiscreteHardyTail (b : ℕ → ℝ) (L : ℕ) : ℝ :=
  ∑' j : ℕ, b (j + L + 1) / ((j + L + 1 : ℝ) * (j + L + 2 : ℝ))

/-- The exact coefficient of the continuous Hardy transform on an arithmetic cell. -/
def etaDiscreteHardyTransform (b : ℕ → ℝ) (L : ℕ) : ℝ :=
  b L / (L + 1 : ℝ) - etaDiscreteHardyTail b L

private theorem reciprocal_cells (L : ℕ) :
    HasSum (fun j : ℕ ↦ 1 / ((j + L + 1 : ℝ) * (j + L + 2 : ℝ))) (1 / (L + 1 : ℝ)) := by
  have hs : HasSum (fun j : ℕ ↦ 1 / (j + L + 1 : ℝ) - 1 / (j + L + 2 : ℝ)) (1 / (L + 1 : ℝ)) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun j ↦ sub_nonneg.mpr
      (one_div_le_one_div_of_le (by positivity) (by linarith))) _).mpr
    have hzero : Tendsto (fun j : ℕ ↦ 1 / (j + L + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (((tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ ↦ (j : ℝ)) atTop atTop).atTop_add
          tendsto_const_nhds).atTop_add tendsto_const_nhds)
    have hh : Tendsto (fun j : ℕ ↦ 1 / (L + 1 : ℝ) - 1 / (j + L + 1 : ℝ)) atTop
        (𝓝 (1 / (L + 1 : ℝ))) := by simpa using tendsto_const_nhds.sub hzero
    convert hh using 1
    ext N
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add,
      show ∀ j : ℝ, j + 1 + L + 1 = j + L + 2 by intro j; ring] using
      Finset.sum_range_sub' (fun j : ℕ ↦ 1 / (j + L + 1 : ℝ)) N
  convert hs using 1
  ext j
  field_simp
  ring

private theorem norm_cell_le {b : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |b n| ≤ C) (L j : ℕ) :
    ‖b (j + L + 1) / ((j + L + 1 : ℝ) * (j + L + 2 : ℝ))‖ ≤
      C * (1 / ((j + L + 1 : ℝ) * (j + L + 2 : ℝ))) := by
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < (j + L + 1 : ℝ) * (j + L + 2 : ℝ))]
  simpa only [mul_one_div] using div_le_div_of_nonneg_right (hb (j + L + 1))
    (by positivity : 0 ≤ (j + L + 1 : ℝ) * (j + L + 2 : ℝ))

/-- The full weighted tail defining the arithmetic Hardy transform is genuinely summable for bounded cells. -/
theorem summable_etaDiscreteHardyTail {b : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |b n| ≤ C) (L : ℕ) :
    Summable (fun j : ℕ ↦ b (j + L + 1) / ((j + L + 1 : ℝ) * (j + L + 2 : ℝ))) :=
  ((reciprocal_cells L).mul_left C).summable.of_norm_bounded (norm_cell_le hb L)

/-- The entire weighted Hardy tail has an explicit bound at every physical endpoint. -/
theorem abs_etaDiscreteHardyTail_le {b : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |b n| ≤ C) (L : ℕ) :
    |etaDiscreteHardyTail b L| ≤ C / (L + 1 : ℝ) := by
  have hs := summable_etaDiscreteHardyTail hb L
  calc
    _ ≤ ∑' j : ℕ, ‖b (j + L + 1) / ((j + L + 1 : ℝ) * (j + L + 2 : ℝ))‖ := by
      simpa only [etaDiscreteHardyTail, Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' j : ℕ, C * (1 / ((j + L + 1 : ℝ) * (j + L + 2 : ℝ))) :=
      hs.norm.tsum_le_tsum (norm_cell_le hb L) ((reciprocal_cells L).mul_left C).summable
    _ = _ := by rw [((reciprocal_cells L).mul_left C).tsum_eq]; ring

/-- Adjacent full Hardy tails differ by exactly the original intervening arithmetic cell. -/
theorem etaDiscreteHardyTail_eq_cell_add_succ {b : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |b n| ≤ C) (L : ℕ) :
    etaDiscreteHardyTail b L = b (L + 1) / ((L + 1 : ℝ) * (L + 2 : ℝ)) + etaDiscreteHardyTail b (L + 1) := by
  have h := (summable_etaDiscreteHardyTail hb L).sum_add_tsum_nat_add 1
  simpa only [Finset.sum_range_one, etaDiscreteHardyTail, zero_add, Nat.cast_zero,
    add_assoc, Nat.cast_add, Nat.cast_one, add_comm (1 : ℝ) (L : ℝ), add_comm 1 L] using h.symm

/-- The exact transformed-cell increment is the original cell increment divided by its physical endpoint. -/
theorem etaDiscreteHardyTransform_succ_sub {b : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |b n| ≤ C) (L : ℕ) :
    etaDiscreteHardyTransform b (L + 1) - etaDiscreteHardyTransform b L =
      (b (L + 1) - b L) / (L + 1 : ℝ) := by
  unfold etaDiscreteHardyTransform
  rw [etaDiscreteHardyTail_eq_cell_add_succ hb L]
  push_cast
  field_simp
  ring

private theorem energy_step {b : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |b n| ≤ C) (L : ℕ) :
    etaDiscreteHardyTransform b (L + 1) ^ 2 - b (L + 1) ^ 2 / ((L + 1 : ℝ) * (L + 2 : ℝ)) =
      (L + 2 : ℝ) * etaDiscreteHardyTail b (L + 1) ^ 2 - (L + 1 : ℝ) * etaDiscreteHardyTail b L ^ 2 := by
  unfold etaDiscreteHardyTransform
  rw [etaDiscreteHardyTail_eq_cell_add_succ hb L]
  push_cast
  field_simp
  ring

/-- The finite Hardy energy identity retains the complete boundary-tail square at the actual endpoint. -/
theorem sum_etaDiscreteHardyTransform_sq_eq {b : ℕ → ℝ} {C : ℝ}
    (hb : ∀ n, |b n| ≤ C) (hb0 : b 0 = 0) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), etaDiscreteHardyTransform b n ^ 2) =
      (∑ n ∈ Finset.range N, b (n + 1) ^ 2 / ((n + 1 : ℝ) * (n + 2 : ℝ))) +
        (N + 1 : ℝ) * etaDiscreteHardyTail b N ^ 2 := by
  induction N with
  | zero => simp [etaDiscreteHardyTransform, hb0]
  | succ N ih =>
    rw [Finset.sum_range_succ (fun n ↦ etaDiscreteHardyTransform b n ^ 2) (N + 1), ih,
      Finset.sum_range_succ]
    have h := energy_step hb N
    push_cast
    linarith

/-- The transformed coefficient has a uniform inverse-linear bound at every cell. -/
theorem abs_etaDiscreteHardyTransform_le {b : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |b n| ≤ C) (L : ℕ) :
    |etaDiscreteHardyTransform b L| ≤ 2 * C / (L + 1 : ℝ) := by
  unfold etaDiscreteHardyTransform
  apply (abs_sub _ _).trans
  have hfirst : |b L / (L + 1 : ℝ)| ≤ C / (L + 1 : ℝ) := by
    rw [abs_div, show |(L + 1 : ℝ)| = L + 1 from abs_of_pos (by positivity)]
    exact div_le_div_of_nonneg_right (hb L) (by positivity)
  calc
    _ ≤ C / (L + 1 : ℝ) + C / (L + 1 : ℝ) := add_le_add hfirst (abs_etaDiscreteHardyTail_le hb L)
    _ = _ := by ring

/-- The complete square sum of the transformed bounded arithmetic cells is genuinely summable. -/
theorem summable_etaDiscreteHardyTransform_sq {b : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |b n| ≤ C) :
    Summable (fun L : ℕ ↦ etaDiscreteHardyTransform b L ^ 2) := by
  apply (((reciprocal_cells 0).mul_left (8 * C ^ 2)).summable.of_nonneg_of_le (fun _ ↦ sq_nonneg _))
  intro L
  have hh := pow_le_pow_left₀ (abs_nonneg _) (abs_etaDiscreteHardyTransform_le hb L) 2
  rw [sq_abs] at hh
  calc
    _ ≤ (2 * C / (L + 1 : ℝ)) ^ 2 := hh
    _ ≤ _ := by
      simp only [Nat.cast_zero, add_zero]
      field_simp
      nlinarith [mul_nonneg (sq_nonneg C) (Nat.cast_nonneg (α := ℝ) L)]

/-- The weighted square sum of all original bounded arithmetic cells is genuinely summable. -/
theorem summable_etaDiscreteHardyCellEnergy {b : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |b n| ≤ C) :
    Summable (fun n : ℕ ↦ b (n + 1) ^ 2 / ((n + 1 : ℝ) * (n + 2 : ℝ))) := by
  apply (((reciprocal_cells 0).mul_left (C ^ 2)).summable.of_nonneg_of_le (fun _ ↦ by positivity))
  intro n
  have hh := pow_le_pow_left₀ (abs_nonneg _) (hb (n + 1)) 2
  rw [sq_abs] at hh
  simpa only [Nat.cast_zero, add_zero, mul_one_div] using div_le_div_of_nonneg_right hh
    (by positivity : 0 ≤ (n + 1 : ℝ) * (n + 2 : ℝ))

/-- The full boundary-tail square in the finite Hardy identity tends to zero for the actual bounded cells. -/
theorem etaDiscreteHardyBoundary_tendsto_zero {b : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |b n| ≤ C) :
    Tendsto (fun N : ℕ ↦ (N + 1 : ℝ) * etaDiscreteHardyTail b N ^ 2) atTop (𝓝 0) := by
  have hzero : Tendsto (fun N : ℕ ↦ C ^ 2 / (N + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop).atTop_add tendsto_const_nhds)
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ by positivity)) (Eventually.of_forall (fun N ↦ ?_)) hzero
  have hh := pow_le_pow_left₀ (abs_nonneg _) (abs_etaDiscreteHardyTail_le hb N) 2
  rw [sq_abs] at hh
  calc
    _ ≤ (N + 1 : ℝ) * (C / (N + 1 : ℝ)) ^ 2 := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by field_simp

/-- The arithmetic Hardy transform preserves the full norm exactly: its ordinary square sum equals the original reciprocal-cell-weighted square sum, with the full endpoint limit discharged. -/
theorem tsum_etaDiscreteHardyTransform_sq_eq {b : ℕ → ℝ} {C : ℝ}
    (hb : ∀ n, |b n| ≤ C) (hb0 : b 0 = 0) :
    (∑' n : ℕ, etaDiscreteHardyTransform b n ^ 2) =
      ∑' n : ℕ, b (n + 1) ^ 2 / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
  have hleft := (summable_etaDiscreteHardyTransform_sq hb).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hright := (summable_etaDiscreteHardyCellEnergy hb).hasSum.tendsto_sum_nat.add
    (etaDiscreteHardyBoundary_tendsto_zero hb)
  simp only [add_zero] at hright
  apply tendsto_nhds_unique hleft
  convert hright using 1
  ext N
  exact sum_etaDiscreteHardyTransform_sq_eq hb hb0 N

end

end RiemannGaussian
