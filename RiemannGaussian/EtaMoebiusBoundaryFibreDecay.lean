import RiemannGaussian.EtaMoebiusBoundaryFibre
import RiemannGaussian.EtaMoebiusTwoThirdsQuotientEnergy

/-!
# Vanishing boundary and the complete-block source limit

The only clipped fibre has a uniform vanishing norm allowance. Completing
it therefore leaves the nonzero source limit unchanged. This eliminates
the boundary as an arithmetic obstruction without estimating the remaining
complete blocks. A fixed gap below the source square would suffice for
the reductio; a gap that vanishes with the cutoff would not.
-/

open Complex Filter
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- The uniform norm allowance for the single boundary on every cubic window. -/
def pairedEtaMoebiusBoundaryAllowance (rho : NontrivialZetaZero) (D : ℕ) : ℝ :=
  pairedEtaCompletedMoebiusTermConstant rho * (D : ℝ) ^ (1 - 3 * rho.1.re)

/-- The actual boundary allowance tends to zero already when the real part exceeds one third. -/
theorem pairedEtaMoebiusBoundaryAllowance_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 3 < rho.1.re) :
    Tendsto (pairedEtaMoebiusBoundaryAllowance rho) atTop (𝓝 0) := by
  have hp : Tendsto (fun D : ℕ ↦ (D : ℝ) ^ (1 - 3 * rho.1.re)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < 3 * rho.1.re - 1)).comp tendsto_natCast_atTop_atTop
  change Tendsto (fun D : ℕ ↦ pairedEtaCompletedMoebiusTermConstant rho * (D : ℝ) ^ (1 - 3 * rho.1.re)) atTop (𝓝 0)
  simpa only [mul_zero] using
    hp.const_mul (pairedEtaCompletedMoebiusTermConstant rho)

/-- The full complex error after completing the blocks is exactly boundary minus the original small-divisor aggregate. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientAggregate_sub_source
    (rho : NontrivialZetaZero) {M D : ℕ} (hM : 2 ≤ M) (hDM : D ≤ M) :
    pairedEtaCompletedMoebiusCompleteQuotientAggregate rho M D - pairedEtaCompletedMoebiusSource rho =
      pairedEtaCompletedMoebiusBoundaryFibre rho M D - pairedEtaCompletedMoebiusPartialAggregate rho M D := by
  rw [pairedEtaCompletedMoebiusCompleteQuotientAggregate_eq_boundary_add_large rho hDM,
    pairedEtaCompletedMoebiusLargeAggregate_eq_source_sub rho hM hDM]
  ring

/-- The entire mean square of the single added fibre on the original physical window. -/
def pairedEtaCompletedMoebiusBoundaryMeanSquare (rho : NontrivialZetaZero) (A L D : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L, ‖pairedEtaCompletedMoebiusBoundaryFibre rho (A + n) D‖ ^ 2) / L

/-- The single boundary's full-window energy is bounded by the square of its uniform allowance. -/
theorem pairedEtaCompletedMoebiusBoundaryMeanSquare_twoThirds_le
    (rho : NontrivialZetaZero) {D : ℕ} (hD : 1 ≤ D) :
    pairedEtaCompletedMoebiusBoundaryMeanSquare rho (D ^ 3) (D ^ 3) (D ^ 2) ≤
      pairedEtaMoebiusBoundaryAllowance rho D ^ 2 := by
  have hDp : (0 : ℝ) < (D ^ 3 : ℕ) := by positivity
  apply (div_le_iff₀ hDp).mpr
  calc
    _ ≤ ∑ _n ∈ Finset.range (D ^ 3), pairedEtaMoebiusBoundaryAllowance rho D ^ 2 := by
      apply Finset.sum_le_sum
      intro n _
      exact pow_le_pow_left₀ (norm_nonneg _)
        (norm_pairedEtaCompletedMoebiusBoundaryFibre_twoThirds_le rho hD (by omega)) 2
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- The single clipped boundary has vanishing mean square on the whole cubic window, without any estimate for the surviving complete quotient blocks. -/
theorem pairedEtaCompletedMoebiusBoundaryMeanSquare_twoThirds_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 3 < rho.1.re) :
    Tendsto (fun D : ℕ ↦ pairedEtaCompletedMoebiusBoundaryMeanSquare rho (D ^ 3) (D ^ 3) (D ^ 2))
      atTop (𝓝 0) := by
  have hb := (pairedEtaMoebiusBoundaryAllowance_tendsto_zero rho hrho).pow 2
  simp only [zero_pow (by decide : 2 ≠ 0)] at hb
  exact squeeze_zero' (Eventually.of_forall (fun D ↦
    div_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) (Nat.cast_nonneg (D ^ 3))))
    ((eventually_ge_atTop 1).mono fun _ hD ↦ pairedEtaCompletedMoebiusBoundaryMeanSquare_twoThirds_le rho hD) hb

/-- Mean square of the surviving complete quotient-block sum, with its actual moving quotient boundary. -/
def pairedEtaCompletedMoebiusCompleteQuotientMeanSquare (rho : NontrivialZetaZero) (A L D : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L, ‖pairedEtaCompletedMoebiusCompleteQuotientAggregate rho (A + n) D‖ ^ 2) / L

/-- The mean-square error from the original source after completing the quotient blocks. -/
def pairedEtaCompletedMoebiusCompleteQuotientSourceError (rho : NontrivialZetaZero) (A L D : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L,
    ‖pairedEtaCompletedMoebiusCompleteQuotientAggregate rho (A + n) D - pairedEtaCompletedMoebiusSource rho‖ ^ 2) / L

/-- Completing the blocks costs only the already controlled small-divisor mean square and the vanishing boundary square. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientSourceError_twoThirds_le
    (rho : NontrivialZetaZero) {D : ℕ} (hD : 2 ≤ D) :
    pairedEtaCompletedMoebiusCompleteQuotientSourceError rho (D ^ 3) (D ^ 3) (D ^ 2) ≤
      2 * pairedEtaMoebiusTwoThirdsAllowance rho D + 2 * pairedEtaMoebiusBoundaryAllowance rho D ^ 2 := by
  have h23 : D ^ 2 ≤ D ^ 3 := by nlinarith [Nat.mul_le_mul_left (D ^ 2) (by omega : 1 ≤ D)]
  have hD3 : 2 ≤ D ^ 3 := by nlinarith
  have hpoint (n : ℕ) :
      ‖pairedEtaCompletedMoebiusCompleteQuotientAggregate rho (D ^ 3 + n) (D ^ 2) - pairedEtaCompletedMoebiusSource rho‖ ^ 2 ≤
        2 * ‖pairedEtaCompletedMoebiusPartialAggregate rho (D ^ 3 + n) (D ^ 2)‖ ^ 2 +
          2 * ‖pairedEtaCompletedMoebiusBoundaryFibre rho (D ^ 3 + n) (D ^ 2)‖ ^ 2 := by
    rw [pairedEtaCompletedMoebiusCompleteQuotientAggregate_sub_source rho (by omega) (by omega)]
    have hn := norm_sub_le (pairedEtaCompletedMoebiusBoundaryFibre rho (D ^ 3 + n) (D ^ 2))
      (pairedEtaCompletedMoebiusPartialAggregate rho (D ^ 3 + n) (D ^ 2))
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (‖pairedEtaCompletedMoebiusBoundaryFibre rho (D ^ 3 + n) (D ^ 2)‖ -
      ‖pairedEtaCompletedMoebiusPartialAggregate rho (D ^ 3 + n) (D ^ 2)‖)]
  calc
    _ ≤ 2 * pairedEtaCompletedMoebiusOriginalMeanSquare rho (D ^ 3) (D ^ 3) (D ^ 2) +
        2 * pairedEtaCompletedMoebiusBoundaryMeanSquare rho (D ^ 3) (D ^ 3) (D ^ 2) := by
      unfold pairedEtaCompletedMoebiusCompleteQuotientSourceError
        pairedEtaCompletedMoebiusOriginalMeanSquare pairedEtaCompletedMoebiusBoundaryMeanSquare
      simp only [← mul_div_assoc, ← add_div, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun n _ ↦ hpoint n)) (Nat.cast_nonneg _)
    _ ≤ _ := by
      have hl := pairedEtaCompletedMoebiusOriginalMeanSquare_twoThirds_le rho (by omega : 1 ≤ D)
      have hb := pairedEtaCompletedMoebiusBoundaryMeanSquare_twoThirds_le rho (by omega : 1 ≤ D)
      linarith

private theorem meanSquare_source_error_le (v : ℕ → ℂ) (s : ℂ) {L : ℕ} (hL : 0 < L) :
    |(∑ n ∈ Finset.range L, ‖v n‖ ^ 2) / L - ‖s‖ ^ 2| ≤
      (∑ n ∈ Finset.range L, ‖v n - s‖ ^ 2) / L +
        2 * ‖s‖ * Real.sqrt ((∑ n ∈ Finset.range L, ‖v n - s‖ ^ 2) / L) := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range L) (fun _ : ℕ ↦ (1 : ℝ))
    (fun n ↦ ‖v n - s‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hc
  have havg : (∑ n ∈ Finset.range L, ‖v n - s‖) / L ≤
      Real.sqrt ((∑ n ∈ Finset.range L, ‖v n - s‖ ^ 2) / L) := by
    apply Real.le_sqrt_of_sq_le
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hLR)).mpr
    convert hc using 1
    field_simp
  have hpoint (n : ℕ) : |‖v n‖ ^ 2 - ‖s‖ ^ 2| ≤
      ‖v n - s‖ ^ 2 + 2 * ‖s‖ * ‖v n - s‖ := by
    have he : ‖v n‖ ^ 2 - ‖s‖ ^ 2 = ‖v n - s‖ ^ 2 + 2 * (s * starRingEnd ℂ (v n - s)).re := by
      have hx : v n = s + (v n - s) := by ring
      conv_lhs => rw [hx]
      simp only [Complex.sq_norm, Complex.normSq_add]
      ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hr := Complex.abs_re_le_norm (s * starRingEnd ℂ (v n - s))
    rw [norm_mul, Complex.norm_conj] at hr
    nlinarith
  calc
    _ = |(∑ n ∈ Finset.range L, (‖v n‖ ^ 2 - ‖s‖ ^ 2)) / L| := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      congr 1
      field_simp
    _ ≤ (∑ n ∈ Finset.range L, (‖v n - s‖ ^ 2 + 2 * ‖s‖ * ‖v n - s‖)) / L := by
      rw [abs_div, abs_of_pos hLR]
      exact div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun n _ ↦ hpoint n))) hLR.le
    _ = (∑ n ∈ Finset.range L, ‖v n - s‖ ^ 2) / L +
        2 * ‖s‖ * ((∑ n ∈ Finset.range L, ‖v n - s‖) / L) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, add_div, mul_div_assoc]
    _ ≤ _ := by gcongr

/-- The energy of the actual complete quotient blocks has the full source-error allowance, including its square-root cross-term cost. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_source_error_le
    (rho : NontrivialZetaZero) {D : ℕ} (hD : 2 ≤ D) :
    let U := 2 * pairedEtaMoebiusTwoThirdsAllowance rho D + 2 * pairedEtaMoebiusBoundaryAllowance rho D ^ 2
    |pairedEtaCompletedMoebiusCompleteQuotientMeanSquare rho (D ^ 3) (D ^ 3) (D ^ 2) -
      ‖pairedEtaCompletedMoebiusSource rho‖ ^ 2| ≤ U + 2 * ‖pairedEtaCompletedMoebiusSource rho‖ * Real.sqrt U := by
  dsimp only
  have hu := pairedEtaCompletedMoebiusCompleteQuotientSourceError_twoThirds_le rho hD
  apply (meanSquare_source_error_le
    (fun n ↦ pairedEtaCompletedMoebiusCompleteQuotientAggregate rho (D ^ 3 + n) (D ^ 2))
    (pairedEtaCompletedMoebiusSource rho) (by positivity : 0 < D ^ 3)).trans
  exact add_le_add hu (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hu) (by positivity))

/-- Removing the only clipped fibre leaves the same positive source limit in the entire complete-block mean square. -/
theorem pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_tendsto_source
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun D : ℕ ↦ pairedEtaCompletedMoebiusCompleteQuotientMeanSquare rho (D ^ 3) (D ^ 3) (D ^ 2))
      atTop (𝓝 (‖pairedEtaCompletedMoebiusSource rho‖ ^ 2)) := by
  have hl := pairedEtaMoebiusTwoThirdsAllowance_tendsto_zero rho hrho
  have he := pairedEtaMoebiusBoundaryAllowance_tendsto_zero rho (by linarith : (1 : ℝ) / 3 < rho.1.re)
  have hu := (hl.const_mul 2).add ((he.pow 2).const_mul 2)
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hu
  have hb := hu.add (hu.sqrt.const_mul (2 * ‖pairedEtaCompletedMoebiusSource rho‖))
  simp only [Real.sqrt_zero, mul_zero, add_zero] at hb
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  exact squeeze_zero' (Eventually.of_forall (fun _ ↦ abs_nonneg _))
    ((eventually_ge_atTop 2).mono fun _ hD ↦
      pairedEtaCompletedMoebiusCompleteQuotientMeanSquare_twoThirds_source_error_le rho hD) hb

end

end RiemannGaussian
