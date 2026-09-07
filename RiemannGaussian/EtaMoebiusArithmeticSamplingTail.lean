import RiemannGaussian.EtaMoebiusQuotientError
import RiemannGaussian.EtaMoebiusArithmeticTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The complete arithmetic tail in the quadratic sampling range

The actual quotient parity sampler, with its physical-window condition,
controls every block beyond the quadratic cutoff. The exact arithmetic
square sum is regrouped into consecutive blocks using its already proved
summability. A telescoping majorant includes the entire infinite tail.
No estimate on the growing near region is assumed or claimed.
-/

open Filter
open scoped Topology ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

private theorem coefficient_energy_le {M : ℕ} {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    (∑ n ∈ Finset.Icc 1 M, ((μ n : ℝ) * w n) ^ 2) ≤ M := by
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 M, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have ha : |(μ n : ℝ) * w n| ≤ 1 := by
        rw [abs_mul]
        exact (mul_le_mul (abs_real_moebius_le_one n) (hw n hn) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
      simpa only [sq_abs, one_pow] using pow_le_pow_left₀ (abs_nonneg _) ha 2
    _ = _ := by simp

private theorem reciprocal_steps :
    HasSum (fun b : ℕ ↦ 1 / (b + 1 : ℝ) - 1 / (b + 2 : ℝ)) (1 : ℝ) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun b ↦ sub_nonneg.mpr
    (one_div_le_one_div_of_le (by positivity) (by linarith))) _).mpr
  have hzero : Tendsto (fun b : ℕ ↦ 1 / (b + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_natCast_atTop_atTop : Tendsto (fun b : ℕ ↦ (b : ℝ)) atTop atTop).atTop_add tendsto_const_nhds)
  have hh : Tendsto (fun b : ℕ ↦ 1 - 1 / (b + 1 : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hzero
  convert hh using 1
  ext N
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, div_one,
    add_assoc, one_add_one_eq_two] using Finset.sum_range_sub' (fun b : ℕ ↦ 1 / (b + 1 : ℝ)) N

private theorem window_bound {M R : ℕ} (hM : 1 ≤ M) (hMR : M ^ 2 ≤ R)
    {w : ℕ → ℝ} (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (A : ℕ) :
    (∑ j ∈ Finset.range R, ‖pairedEtaWeightedDivisorParityFamily (fun n ↦ (μ n : ℝ) * w n) (A + j) M‖ ^ 2) ≤
      (5 * finiteCircleSamplingConstant * (1 + Real.log M) ^ 2 * M) * R := by
  have hR : 0 < R := (pow_pos hM 2).trans_le hMR
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  apply (div_le_iff₀ hRp).mp
  apply (pairedEtaWeightedDivisorParityFamily_meanSquare_le_quadratic _ A hM hMR).trans
  exact mul_le_mul_of_nonneg_left (coefficient_energy_le hw)
    (mul_nonneg (mul_nonneg (by norm_num) finiteCircleSamplingConstant_pos.le) (sq_nonneg _))

private theorem residual_block_bound {M R : ℕ} (hM : 1 ≤ M) (hMR : M ^ 2 ≤ R)
    {w : ℕ → ℝ} (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) (b : ℕ) :
    (∑ j ∈ Finset.range R, pairedEtaMoebiusArithmeticCellResidual M w (b * R + j + R + 1) ^ 2) ≤
      ((pairedEtaMoebiusArithmeticHarmonic M w ^ 2 +
        5 * finiteCircleSamplingConstant * (1 + Real.log M) ^ 2 * M) / R +
        2 * (M : ℝ) ^ 4 / (R : ℝ) ^ 3) / (b + 1 : ℝ) ^ 2 := by
  have hR : 0 < R := (pow_pos hM 2).trans_le hMR
  have hRp : (0 : ℝ) < R := by exact_mod_cast hR
  let X : ℝ := (b + 1 : ℝ) * R
  have hXp : 0 < X := by dsimp [X]; positivity
  let P := pairedEtaMoebiusArithmeticHarmonic M w ^ 2
  let C := 5 * finiteCircleSamplingConstant * (1 + Real.log M) ^ 2 * M
  have hcell (j : ℕ) : pairedEtaMoebiusArithmeticCellResidual M w (b * R + j + R + 1) ^ 2 ≤
      (P + ‖pairedEtaWeightedDivisorParityFamily (fun n ↦ (μ n : ℝ) * w n) (b * R + j + R + 1) M‖ ^ 2) / X ^ 2 +
        2 * (M : ℝ) ^ 4 / X ^ 4 := by
    have hL : 2 ≤ b * R + j + R + 1 := by omega
    have hXL : X ≤ (b * R + j + R + 1 : ℕ) := by
      dsimp [X]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) j]
    apply (pairedEtaMoebiusArithmeticCellResidual_sq_le_quotientFamily hM hL hw).trans
    exact add_le_add
      (div_le_div_of_nonneg_left (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
        (pow_le_pow_left₀ hXp.le hXL 2))
      (div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hXp.le hXL 4))
  have hs := Finset.sum_le_sum (s := Finset.range R) (fun j _ ↦ hcell j)
  have hw' := window_bound hM hMR hw (b * R + R + 1)
  simp_rw [show ∀ j : ℕ, b * R + R + 1 + j = b * R + j + R + 1 by intro j; omega] at hw'
  calc
    _ ≤ ((R : ℝ) * P + ∑ j ∈ Finset.range R,
        ‖pairedEtaWeightedDivisorParityFamily (fun n ↦ (μ n : ℝ) * w n) (b * R + j + R + 1) M‖ ^ 2) / X ^ 2 +
        R * (2 * (M : ℝ) ^ 4 / X ^ 4) := by
      simpa only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, mul_div_assoc] using hs
    _ ≤ ((R : ℝ) * P + C * R) / X ^ 2 + R * (2 * (M : ℝ) ^ 4 / X ^ 4) := by
      exact add_le_add_left (div_le_div_of_nonneg_right (add_le_add_right hw' _)
        (by positivity : 0 ≤ X ^ 2)) _
    _ ≤ _ := by
      have hb : (1 : ℝ) ≤ b + 1 := by linarith [Nat.cast_nonneg (α := ℝ) b]
      have hM4 : 0 ≤ (M : ℝ) ^ 4 := by positivity
      dsimp only [X, P, C]
      field_simp
      nlinarith [mul_nonneg hM4 (sub_nonneg.mpr (show (1 : ℝ) ≤ (b + 1 : ℝ) ^ 2 by nlinarith))]

/-- The complete infinite residual tail is controlled by the proved parity sampler in its valid quadratic window range, with all amplitude and endpoint terms paid explicitly. -/
theorem pairedEtaMoebiusArithmeticSquareTail_le_sampling {M R : ℕ}
    (hM : 1 ≤ M) (hMR : M ^ 2 ≤ R) {w : ℕ → ℝ}
    (hw : ∀ n ∈ Finset.Icc 1 M, |w n| ≤ 1) :
    pairedEtaMoebiusArithmeticSquareTail M R w ≤
      2 * (pairedEtaMoebiusArithmeticHarmonic M w ^ 2 +
        5 * finiteCircleSamplingConstant * (1 + Real.log M) ^ 2 * M) / R +
        4 * (M : ℝ) ^ 4 / (R : ℝ) ^ 3 := by
  have hR : 0 < R := (pow_pos hM 2).trans_le hMR
  let : NeZero R := ⟨hR.ne'⟩
  let f : ℕ → ℝ := fun n ↦ pairedEtaMoebiusArithmeticCellResidual M w (n + R + 1) ^ 2
  have hs : Summable f := (summable_nat_add_iff R).mpr (summable_pairedEtaMoebiusArithmeticCellResidual_sq M hw)
  have hp : Summable (fun z : ℕ × Fin R ↦ f ((Nat.divModEquiv R).symm z)) :=
    hs.comp_injective (Nat.divModEquiv R).symm.injective
  have hfin (b : ℕ) : (∑ j : Fin R, pairedEtaMoebiusArithmeticCellResidual M w (b * R + j.1 + R + 1) ^ 2) =
      ∑ j ∈ Finset.range R, pairedEtaMoebiusArithmeticCellResidual M w (b * R + j + R + 1) ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ pairedEtaMoebiusArithmeticCellResidual M w (b * R + j + R + 1) ^ 2) R
  have he : pairedEtaMoebiusArithmeticSquareTail M R w =
      ∑' b : ℕ, ∑ j ∈ Finset.range R, pairedEtaMoebiusArithmeticCellResidual M w (b * R + j + R + 1) ^ 2 := by
    change (∑' n : ℕ, f n) = _
    rw [← (Nat.divModEquiv R).symm.tsum_eq f, hp.tsum_prod]
    simp only [Nat.divModEquiv_symm_apply, f, tsum_fintype, hfin]
  have hbs : Summable (fun b : ℕ ↦ ∑ j ∈ Finset.range R,
      pairedEtaMoebiusArithmeticCellResidual M w (b * R + j + R + 1) ^ 2) := by
    simpa only [Nat.divModEquiv_symm_apply, f, tsum_fintype, hfin] using hp.prod
  let B := (pairedEtaMoebiusArithmeticHarmonic M w ^ 2 +
    5 * finiteCircleSamplingConstant * (1 + Real.log M) ^ 2 * M) / R + 2 * (M : ℝ) ^ 4 / (R : ℝ) ^ 3
  have hC : 0 ≤ finiteCircleSamplingConstant := finiteCircleSamplingConstant_pos.le
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (b : ℕ) : (∑ j ∈ Finset.range R, pairedEtaMoebiusArithmeticCellResidual M w (b * R + j + R + 1) ^ 2) ≤
      2 * B * (1 / (b + 1 : ℝ) - 1 / (b + 2 : ℝ)) := by
    apply (residual_block_bound hM hMR hw b).trans
    change B / (b + 1 : ℝ) ^ 2 ≤ _
    have hh : 1 / (b + 1 : ℝ) ^ 2 ≤ 2 * (1 / (b + 1 : ℝ) - 1 / (b + 2 : ℝ)) := by
      field_simp
      nlinarith [Nat.cast_nonneg (α := ℝ) b]
    simpa only [← mul_div_assoc, mul_one, mul_assoc, mul_left_comm] using mul_le_mul_of_nonneg_left hh hB
  rw [he]
  apply (hbs.tsum_le_tsum hb (reciprocal_steps.mul_left (2 * B)).summable).trans_eq
  rw [(reciprocal_steps.mul_left (2 * B)).tsum_eq]
  dsimp [B]
  ring

/-- The proved full tail allowance at the quadratic physical cutoff for the exact logarithmic Möbius family. -/
def pairedEtaMoebiusQuadraticTailAllowance (M : ℕ) : ℝ :=
  (2 * pairedEtaMoebiusLogHarmonic M ^ 2 + 4) / (M : ℝ) ^ 2 +
    10 * finiteCircleSamplingConstant * ((1 + Real.log M) ^ 2 / M)

/-- The original logarithmic family's entire tail past the quadratic physical cutoff has an explicit vanishing allowance. -/
theorem pairedEtaMoebiusArithmeticSquareTail_quadratic_le {M : ℕ} (hM : 1 ≤ M) :
    pairedEtaMoebiusArithmeticSquareTail M (M ^ 2) (pairedEtaMoebiusTrialLogWeight M) ≤
      pairedEtaMoebiusQuadraticTailAllowance M := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast hM
  apply (pairedEtaMoebiusArithmeticSquareTail_le_sampling hM (le_refl (M ^ 2))
    (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn)).trans_eq
  rw [Nat.cast_pow]
  unfold pairedEtaMoebiusQuadraticTailAllowance pairedEtaMoebiusArithmeticHarmonic pairedEtaMoebiusLogHarmonic
  field_simp
  ring

/-- The explicit quadratic-tail allowance tends to zero by the existing harmonic cancellation and logarithm-versus-power limits. -/
theorem pairedEtaMoebiusQuadraticTailAllowance_tendsto_zero :
    Tendsto pairedEtaMoebiusQuadraticTailAllowance atTop (𝓝 0) := by
  have hnat : Tendsto (fun M : ℕ ↦ (M : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun M : ℕ ↦ 1 / (M : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hnat
  have hlog : Tendsto (fun M : ℕ ↦ Real.log M / (M : ℝ)) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hnat
  have hlog2 : Tendsto (fun M : ℕ ↦ Real.log M ^ 2 / (M : ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_two, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp hnat
  have hlogs : Tendsto (fun M : ℕ ↦ (1 + Real.log M) ^ 2 / (M : ℝ)) atTop (𝓝 0) := by
    convert hinv.add ((hlog.const_mul 2).add hlog2) using 1
    · ext M
      ring
    · norm_num
  have hfirst : Tendsto (fun M : ℕ ↦ (2 * pairedEtaMoebiusLogHarmonic M ^ 2 + 4) / (M : ℝ) ^ 2) atTop (𝓝 0) := by
    convert (((pairedEtaMoebiusLogHarmonic_tendsto_zero.pow 2).const_mul 2).add
      (tendsto_const_nhds (x := (4 : ℝ)))).mul (hinv.pow 2) using 1
    · ext M
      ring
    · norm_num
  change Tendsto (fun M : ℕ ↦ (2 * pairedEtaMoebiusLogHarmonic M ^ 2 + 4) / (M : ℝ) ^ 2 +
    10 * finiteCircleSamplingConstant * ((1 + Real.log M) ^ 2 / M)) atTop (𝓝 0)
  simpa only [mul_zero, add_zero] using hfirst.add (hlogs.const_mul (10 * finiteCircleSamplingConstant))

/-- Every cell beyond the quadratic physical cutoff has total squared residual tending to zero for the exact logarithmic family. -/
theorem pairedEtaMoebiusArithmeticSquareTail_quadratic_tendsto_zero :
    Tendsto (fun M : ℕ ↦ pairedEtaMoebiusArithmeticSquareTail M (M ^ 2) (pairedEtaMoebiusTrialLogWeight M))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ tsum_nonneg (fun _ ↦ sq_nonneg _))) _
    pairedEtaMoebiusQuadraticTailAllowance_tendsto_zero
  exact (eventually_ge_atTop 1).mono (fun _ hM ↦ pairedEtaMoebiusArithmeticSquareTail_quadratic_le hM)

/-- The unchanged full continuum residual differs from its signed arithmetic prefix through the quadratic physical cutoff by a proved vanishing quantity. -/
theorem pairedEtaMoebiusContinuumResidualEnergy_sub_quadraticPrefix_tendsto_zero :
    Tendsto (fun M : ℕ ↦ pairedEtaMoebiusContinuumResidualEnergy M (pairedEtaMoebiusTrialLogWeight M) -
      pairedEtaMoebiusArithmeticSquarePrefix M (M ^ 2) (pairedEtaMoebiusTrialLogWeight M)) atTop (𝓝 0) := by
  convert pairedEtaMoebiusArithmeticSquareTail_quadratic_tendsto_zero using 1
  ext M
  rw [pairedEtaMoebiusContinuumResidualEnergy_eq_prefix_add_tail M (M ^ 2)
    (fun _ hn ↦ abs_pairedEtaMoebiusTrialLogWeight_le hn), add_sub_cancel_left]

end

end RiemannGaussian
