import RiemannGaussian.EtaMoebiusWindowMeanSquare
import RiemannGaussian.EtaMoebiusHyperbolaSourceLimit

/-!
# A two-thirds divisor range for the actual completed source

Retaining the full sampling-window loss permits the divisor cutoff `D²`
on the physical window `[D³, 2D³)`. Both endpoint costs are included.
The resulting allowance decays at a hypothetical right-half zero, so a
strictly larger portion of the original aggregate is now controlled.
The complementary large-divisor sum still needs an independent estimate.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit full mean-square allowance for divisors through `D²` on a physical window of starting cutoff and length `D³`. -/
def pairedEtaMoebiusTwoThirdsAllowance (rho : NontrivialZetaZero) (D : ℕ) : ℝ :=
  11 * pairedEtaCompletedMoebiusOriginalQuadraticConstant rho * (1 + Real.log D) *
    (D : ℝ) ^ (3 - 6 * rho.1.re)

/-- The retained window and endpoint budget on the two-thirds divisor schedule has only cubic logarithmic growth before the original physical decay is applied. -/
theorem moebiusTwoThirds_window_budget_le {D : ℕ} (hD : 1 ≤ D) :
    ((4 * ((D : ℝ) ^ 2) ^ 2 + (D : ℝ) ^ 3) / (D : ℝ) ^ 3) *
        (D : ℝ) ^ 2 * (1 + Real.log ((D : ℝ) ^ 2)) +
      ((D : ℝ) ^ 2) ^ 4 / ((D : ℝ) ^ 3) ^ 2 ≤
        11 * (D : ℝ) ^ 3 * (1 + Real.log D) := by
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDp : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDR
  have hlog := Real.log_nonneg hDR
  have hpow : (D : ℝ) ^ 2 ≤ (D : ℝ) ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hDR (sq_nonneg (D : ℝ))]
  have hc : (D : ℝ) ^ 2 + 4 * (D : ℝ) ^ 3 ≤ 5 * (D : ℝ) ^ 3 := by linarith
  have he : (D : ℝ) ^ 2 ≤ (D : ℝ) ^ 3 * (1 + Real.log D) := by
    nlinarith [mul_nonneg (pow_nonneg hDp.le 3) hlog]
  calc
    _ = ((D : ℝ) ^ 2 + 4 * (D : ℝ) ^ 3) * (1 + 2 * Real.log D) + (D : ℝ) ^ 2 := by
      rw [Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      field_simp
      ring
    _ ≤ (5 * (D : ℝ) ^ 3) * (2 * (1 + Real.log D)) +
        (D : ℝ) ^ 3 * (1 + Real.log D) := by
      exact add_le_add (mul_le_mul hc (by linarith) (by positivity) (by positivity)) he
    _ = _ := by ring

/-- The complete original aggregate through the two-thirds divisor cutoff has a checked mean-square bound on every cubic physical window. -/
theorem pairedEtaCompletedMoebiusOriginalMeanSquare_twoThirds_le
    (rho : NontrivialZetaZero) {D : ℕ} (hD : 1 ≤ D) :
    pairedEtaCompletedMoebiusOriginalMeanSquare rho (D ^ 3) (D ^ 3) (D ^ 2) ≤
      pairedEtaMoebiusTwoThirdsAllowance rho D := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have h23 : D ^ 2 ≤ D ^ 3 := by
    nlinarith [Nat.mul_le_mul_left (D ^ 2) hD]
  have hD2 : 1 ≤ D ^ 2 := by nlinarith
  have hD3 : 1 ≤ D ^ 3 := hD2.trans h23
  have hb := pairedEtaCompletedMoebiusOriginalMeanSquare_le_window rho (A := D ^ 3) (L := D ^ 3) (D := D ^ 2)
    hD3 hD3 hD2 h23
  have hc := pairedEtaCompletedMoebiusOriginalQuadraticConstant_nonneg rho
  have hbudget := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (moebiusTwoThirds_window_budget_le hD) hc)
    (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (D : ℝ) ^ 3) (-2 * rho.1.re))
  simp only [Nat.cast_pow] at hb
  apply (hb.trans hbudget).trans_eq
  have hp : ((D : ℝ) ^ 3) ^ (-2 * rho.1.re) = (D : ℝ) ^ (3 * (-2 * rho.1.re)) := by
    simpa only [Real.rpow_ofNat] using (Real.rpow_mul hDR.le 3 (-2 * rho.1.re)).symm
  have he : (D : ℝ) ^ 3 * ((D : ℝ) ^ 3) ^ (-2 * rho.1.re) = (D : ℝ) ^ (3 - 6 * rho.1.re) := by
    rw [hp, show 3 - 6 * rho.1.re = 3 + 3 * (-2 * rho.1.re) by ring,
      Real.rpow_add hDR, Real.rpow_ofNat]
  rw [pairedEtaMoebiusTwoThirdsAllowance, ← he]
  ring

/-- The explicit enlarged-divisor allowance tends to zero for every hypothetical right-half zero, retaining the full physical-window loss. -/
theorem pairedEtaMoebiusTwoThirdsAllowance_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (pairedEtaMoebiusTwoThirdsAllowance rho) atTop (𝓝 0) := by
  have he : 0 < 6 * rho.1.re - 3 := by linarith
  have hp : Tendsto (fun D : ℕ ↦ (D : ℝ) ^ (3 - 6 * rho.1.re)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop he).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun D : ℕ ↦ Real.log D / (D : ℝ) ^ (6 * rho.1.re - 3)) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (isLittleO_log_rpow_atTop he).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hz := (hp.add hl).const_mul (11 * pairedEtaCompletedMoebiusOriginalQuadraticConstant rho)
  simp only [add_zero, mul_zero] at hz
  apply hz.congr'
  filter_upwards [eventually_ge_atTop 1] with D hD
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  rw [pairedEtaMoebiusTwoThirdsAllowance, show 3 - 6 * rho.1.re = -(6 * rho.1.re - 3) by ring,
    Real.rpow_neg hDR.le]
  ring

/-- The whole original small-divisor mean square now vanishes through `D²` on `[D³,2D³)` under the right-half-zero hypothesis. -/
theorem pairedEtaCompletedMoebiusOriginalMeanSquare_twoThirds_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun D : ℕ ↦ pairedEtaCompletedMoebiusOriginalMeanSquare rho (D ^ 3) (D ^ 3) (D ^ 2))
      atTop (𝓝 0) := by
  exact squeeze_zero' (Eventually.of_forall (fun D ↦
    pairedEtaCompletedMoebiusOriginalMeanSquare_nonneg rho (D ^ 3) (D ^ 3) (D ^ 2)))
    ((eventually_ge_atTop 1).mono fun _ hD ↦ pairedEtaCompletedMoebiusOriginalMeanSquare_twoThirds_le rho hD)
    (pairedEtaMoebiusTwoThirdsAllowance_tendsto_zero rho hrho)

/-- The enlarged small-divisor range decays on the actual dyadic cubic schedule `A=8^k`, with divisor cutoff `4^k`. -/
theorem pairedEtaCompletedMoebiusOriginalMeanSquare_twoThirds_dyadic_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 2 < rho.1.re) :
    Tendsto (fun k ↦ pairedEtaCompletedMoebiusOriginalMeanSquare rho
      (pairedEtaMoebiusHyperbolaCutoff k ^ 3) (pairedEtaMoebiusHyperbolaCutoff k ^ 3)
      (pairedEtaMoebiusHyperbolaCutoff k ^ 2)) atTop (𝓝 0) :=
  (pairedEtaCompletedMoebiusOriginalMeanSquare_twoThirds_tendsto_zero rho hrho).comp
    pairedEtaMoebiusHyperbolaCutoff_tendsto_atTop

end

end RiemannGaussian
