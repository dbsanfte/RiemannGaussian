import RiemannGaussian.EtaMoebiusHyperbolaSchedule
import RiemannGaussian.EtaMoebiusOriginalQuadraticFamily
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Decay of the original small-divisor half on square windows

The existing quadratic-window Fourier theorem applies at its exact
boundary `A = L = D²`. Its bound is `C (1 + log D) D^(1 - 4 Re rho)`.
Consequently this half tends to zero already when `Re rho > 1/4`,
including at a hypothetical right-half zero. No large-divisor estimate
or conclusion about the location of a zero is supplied by this result.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The existing mean square of the actual small-divisor aggregate is nonnegative. -/
theorem pairedEtaCompletedMoebiusOriginalMeanSquare_nonneg
    (rho : NontrivialZetaZero) (A L D : ℕ) :
    0 ≤ pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D := by
  exact div_nonneg (Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)) (Nat.cast_nonneg L)

/-- The original small half has its explicit power bound on the exact square-window boundary of the existing sampler. -/
theorem pairedEtaCompletedMoebiusOriginalMeanSquare_square_le
    (rho : NontrivialZetaZero) {D : ℕ} (hD : 1 ≤ D) :
    pairedEtaCompletedMoebiusOriginalMeanSquare rho (D ^ 2) (D ^ 2) D ≤
      pairedEtaCompletedMoebiusOriginalQuadraticConstant rho * (1 + Real.log D) *
        (D : ℝ) ^ (1 - 4 * rho.1.re) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hp : ((D : ℝ) ^ 2) ^ (-2 * rho.1.re) = (D : ℝ) ^ (2 * (-2 * rho.1.re)) := by
    simpa only [Real.rpow_two] using (Real.rpow_mul hDR.le 2 (-2 * rho.1.re)).symm
  have he : (D : ℝ) * ((D : ℝ) ^ 2) ^ (-2 * rho.1.re) = (D : ℝ) ^ (1 - 4 * rho.1.re) := by
    rw [hp, show 1 - 4 * rho.1.re = 1 + 2 * (-2 * rho.1.re) by ring,
      Real.rpow_add hDR, Real.rpow_one]
  apply (pairedEtaCompletedMoebiusOriginalMeanSquare_le_quadratic rho hD le_rfl le_rfl).trans_eq
  rw [Nat.cast_pow, ← he]
  ring

/-- The entire growing small-divisor half has vanishing mean square whenever the real part exceeds one quarter. -/
theorem pairedEtaCompletedMoebiusOriginalMeanSquare_square_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 4 < rho.1.re) :
    Tendsto (fun D : ℕ ↦ pairedEtaCompletedMoebiusOriginalMeanSquare rho (D ^ 2) (D ^ 2) D)
      atTop (𝓝 0) := by
  have he : 0 < 4 * rho.1.re - 1 := by linarith
  have hp : Tendsto (fun D : ℕ ↦ (D : ℝ) ^ (1 - 4 * rho.1.re)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_sub] using
      (tendsto_rpow_neg_atTop he).comp tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun D : ℕ ↦ Real.log D / (D : ℝ) ^ (4 * rho.1.re - 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop 1 he).tendsto_div_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun D : ℕ ↦ pairedEtaCompletedMoebiusOriginalQuadraticConstant rho *
      (1 + Real.log D) * (D : ℝ) ^ (1 - 4 * rho.1.re)) atTop (𝓝 0) := by
    have hz := (hp.add hl).const_mul (pairedEtaCompletedMoebiusOriginalQuadraticConstant rho)
    simp only [add_zero, mul_zero] at hz
    apply hz.congr'
    filter_upwards [eventually_ge_atTop 1] with D hD
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    rw [show 1 - 4 * rho.1.re = -(4 * rho.1.re - 1) by ring, Real.rpow_neg hDR.le]
    ring
  exact squeeze_zero' (Eventually.of_forall (fun D ↦
    pairedEtaCompletedMoebiusOriginalMeanSquare_nonneg rho (D ^ 2) (D ^ 2) D))
    ((eventually_ge_atTop 1).mono fun _ hD ↦ pairedEtaCompletedMoebiusOriginalMeanSquare_square_le rho hD) hlim

/-- The actual small half tends to zero on the scheduled dyadic square windows, with the stronger one-quarter threshold retained. -/
theorem pairedEtaCompletedMoebiusOriginalMeanSquare_hyperbola_tendsto_zero
    (rho : NontrivialZetaZero) (hrho : (1 : ℝ) / 4 < rho.1.re) :
    Tendsto (fun k ↦ pairedEtaCompletedMoebiusOriginalMeanSquare rho
      (pairedEtaMoebiusHyperbolaScale k) (pairedEtaMoebiusHyperbolaScale k)
      (pairedEtaMoebiusHyperbolaCutoff k)) atTop (𝓝 0) :=
  (pairedEtaCompletedMoebiusOriginalMeanSquare_square_tendsto_zero rho hrho).comp
    pairedEtaMoebiusHyperbolaCutoff_tendsto_atTop

end

end RiemannGaussian
