import RiemannGaussian.EtaMoebiusArithmeticEnergy

/-!
# Uniform tails of the complete arithmetic square sum

The continuum norm bound gives an explicit bound on every exterior cell,
including its integer endpoint. Telescoping then bounds the entire infinite
arithmetic tail at any chosen cutoff. The finite signed square sum remains
unchanged; its growth with the arithmetic cutoff is the unresolved estimate.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The unchanged signed divisor residual squares on the first `R` physical cells. -/
def pairedEtaMoebiusArithmeticSquarePrefix (M R : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Finset.range R, pairedEtaMoebiusArithmeticCellResidual M w (n + 1) ^ 2

/-- Every physical cell after `R`, retaining the entire genuinely summable infinite tail. -/
def pairedEtaMoebiusArithmeticSquareTail (M R : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, pairedEtaMoebiusArithmeticCellResidual M w (n + R + 1) ^ 2

/-- The complete actual continuum residual splits exactly into its first `R` signed arithmetic squares and all remaining squares. -/
theorem pairedEtaMoebiusContinuumResidualEnergy_eq_prefix_add_tail (M R : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    pairedEtaMoebiusContinuumResidualEnergy M w =
      pairedEtaMoebiusArithmeticSquarePrefix M R w + pairedEtaMoebiusArithmeticSquareTail M R w := by
  rw [pairedEtaMoebiusContinuumResidualEnergy_eq_arithmetic_sum M hw]
  exact ((summable_pairedEtaMoebiusArithmeticCellResidual_sq M hw).sum_add_tsum_nat_add R).symm

/-- A bound for the actual signed residual on every exterior integer cell, obtained at the original upper endpoint without changing the carrier. -/
theorem abs_pairedEtaMoebiusArithmeticCellResidual_le {M L : ℕ} (hL : 2 ≤ L) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    |pairedEtaMoebiusArithmeticCellResidual M w L| ≤ 2 * (M : ℝ) / (L + 1) := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hc : Real.log ((L : ℝ) + 1) ∈ Ioc (Real.log L) (Real.log ((L : ℝ) + 1)) :=
    ⟨Real.log_lt_log hLp (by linarith), le_rfl⟩
  have hz : pairedEtaProjectionHead (Real.log ((L : ℝ) + 1)) = 0 := by
    have hh : Real.log 2 < Real.log ((L : ℝ) + 1) :=
      Real.log_lt_log (by norm_num) (by exact_mod_cast (show 2 < L + 1 by omega))
    simp [pairedEtaProjectionHead, not_le.mpr hh]
  have he := pairedEtaMoebiusContinuumResidual_eq_arithmetic_cell M w (by omega : 1 ≤ L) hc
  have hn := congrArg norm he
  rw [hz, zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _), Real.exp_log (by positivity : 0 < (L : ℝ) + 1)] at hn
  apply (le_div_iff₀ (by positivity : 0 < (L : ℝ) + 1)).mpr
  calc
    _ = ‖pairedEtaMoebiusContinuumCombination M w (Real.log ((L : ℝ) + 1))‖ := by
      rw [hn]
      ring
    _ ≤ _ := norm_pairedEtaMoebiusContinuumCombination_le M hw _

private theorem hasSum_reciprocal_step (R : ℕ) :
    HasSum (fun n : ℕ ↦ 1 / (n + R + 1 : ℝ) - 1 / (n + R + 2 : ℝ))
      (1 / (R + 1 : ℝ)) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ sub_nonneg.mpr
    (one_div_le_one_div_of_le (by positivity) (by linarith))) _).mpr
  have hzero : Tendsto (fun n : ℕ ↦ 1 / (n + R + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (by
      exact ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).atTop_add
        tendsto_const_nhds).atTop_add tendsto_const_nhds)
  have hh : Tendsto (fun n : ℕ ↦ 1 / (R + 1 : ℝ) - 1 / (n + R + 1 : ℝ)) atTop
      (𝓝 (1 / (R + 1 : ℝ))) := by simpa using tendsto_const_nhds.sub hzero
  convert hh using 1
  ext N
  have he := Finset.sum_range_sub' (fun n : ℕ ↦ 1 / (n + R + 1 : ℝ)) N
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, show
    ∀ n : ℝ, n + 1 + R + 1 = n + R + 2 by intro n; ring] using he

/-- The entire infinite arithmetic tail has an explicit bound uniform in both cutoffs; every signed residual beyond the finite prefix is included. -/
theorem pairedEtaMoebiusArithmeticSquareTail_le {M R : ℕ} (hR : 1 ≤ R) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    pairedEtaMoebiusArithmeticSquareTail M R w ≤ 4 * (M : ℝ) ^ 2 / (R + 1) := by
  have hs : Summable (fun n : ℕ ↦ pairedEtaMoebiusArithmeticCellResidual M w (n + R + 1) ^ 2) :=
    (summable_nat_add_iff R).mpr (summable_pairedEtaMoebiusArithmeticCellResidual_sq M hw)
  have ht := (hasSum_reciprocal_step R).mul_left (4 * (M : ℝ) ^ 2)
  have hp (n : ℕ) : pairedEtaMoebiusArithmeticCellResidual M w (n + R + 1) ^ 2 ≤
      4 * (M : ℝ) ^ 2 * (1 / (n + R + 1 : ℝ) - 1 / (n + R + 2 : ℝ)) := by
    have hb := abs_pairedEtaMoebiusArithmeticCellResidual_le (M := M) (by omega : 2 ≤ n + R + 1) hw
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hsq
    have hnp : 0 < (n : ℝ) + R + 1 := by positivity
    have hnq : 0 < (n : ℝ) + R + 2 := by positivity
    calc
      _ ≤ (2 * (M : ℝ) / (n + R + 2 : ℝ)) ^ 2 := by
        simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using hsq
      _ ≤ _ := by
        field_simp
        nlinarith [sq_nonneg (M : ℝ)]
  exact (hs.tsum_le_tsum hp ht.summable).trans_eq (by
    rw [ht.tsum_eq]
    ring)

/-- The full residual is bounded by a computable finite signed square sum and a proved bound for every omitted cell. -/
theorem pairedEtaMoebiusContinuumResidualEnergy_le_prefix_add_tailBound {M R : ℕ}
    (hR : 1 ≤ R) {w : ℕ → ℝ} (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    pairedEtaMoebiusContinuumResidualEnergy M w ≤
      pairedEtaMoebiusArithmeticSquarePrefix M R w + 4 * (M : ℝ) ^ 2 / (R + 1) := by
  rw [pairedEtaMoebiusContinuumResidualEnergy_eq_prefix_add_tail M R hw]
  exact add_le_add_right (pairedEtaMoebiusArithmeticSquareTail_le hR hw) _

/-- All cells beyond the explicit quartic physical cutoff contribute at most a vanishing inverse-square allowance. -/
theorem pairedEtaMoebiusArithmeticSquareTail_quartic_le (M : ℕ) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    pairedEtaMoebiusArithmeticSquareTail M ((M + 1) ^ 4) w ≤ 4 / (M + 1 : ℝ) ^ 2 := by
  apply (pairedEtaMoebiusArithmeticSquareTail_le
    (by
      have : 0 < (M + 1) ^ 4 := by positivity
      omega) hw).trans
  rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  have hp : 0 < (M : ℝ) + 1 := by positivity
  have hMs : (M : ℝ) ^ 2 ≤ ((M : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hMs (sq_nonneg ((M : ℝ) + 1))]

/-- The actual full residual and its unchanged signed divisor sum through the explicit quartic physical cutoff differ by a proved vanishing quantity. -/
theorem pairedEtaMoebiusContinuumResidualEnergy_sub_quarticPrefix_tendsto_zero :
    Tendsto (fun M : ℕ ↦ pairedEtaMoebiusContinuumResidualEnergy M (pairedEtaMoebiusTrialLogWeight M) -
      pairedEtaMoebiusArithmeticSquarePrefix M ((M + 1) ^ 4) (pairedEtaMoebiusTrialLogWeight M))
      atTop (𝓝 0) := by
  have hzero : Tendsto (fun M : ℕ ↦ 4 / (M + 1 : ℝ) ^ 2) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun M : ℕ ↦ 1 / (M + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop).atTop_add tendsto_const_nhds)
    simpa only [one_div_pow, mul_zero, zero_pow (by decide : 2 ≠ 0), div_eq_mul_inv,
      one_mul, inv_pow] using (hdiv.pow 2).const_mul (4 : ℝ)
  apply squeeze_zero' _ _ hzero
  · exact Filter.Eventually.of_forall fun M ↦ by
      rw [pairedEtaMoebiusContinuumResidualEnergy_eq_prefix_add_tail M ((M + 1) ^ 4)
        (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn), add_sub_cancel_left]
      exact tsum_nonneg (fun _ ↦ sq_nonneg _)
  · exact Filter.Eventually.of_forall fun M ↦ by
      rw [pairedEtaMoebiusContinuumResidualEnergy_eq_prefix_add_tail M ((M + 1) ^ 4)
        (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn), add_sub_cancel_left]
      exact pairedEtaMoebiusArithmeticSquareTail_quartic_le M
        (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn)

end

end RiemannGaussian
