import RiemannGaussian.EtaMoebiusPrimeVariance

/-!
# Decay on every fixed arithmetic cell

The exact prime-shell formula and the previously proved Möbius harmonic
cancellation give actual residual decay on each fixed physical cell and
each fixed finite union of cells. These statements do not exchange a
growing arithmetic cutoff with an infinite sum. Uniform control of the
growing prime variance and the exterior squares remains necessary.
-/

open Filter
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The actual logarithmic divisor residual tends to zero on every fixed positive physical cell, including cells outside the compact target support. -/
theorem pairedEtaMoebiusArithmeticCellResidual_tendsto_zero {L : ℕ} (hL : 1 ≤ L) :
    Tendsto (fun M : ℕ ↦ pairedEtaMoebiusArithmeticCellResidual M
      (pairedEtaMoebiusTrialLogWeight M) L) atTop (𝓝 0) := by
  have hlog : Tendsto (fun M : ℕ ↦ Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun M : ℕ ↦ pairedEtaPrimeHarmonicShell L / Real.log M) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  have hh := (pairedEtaMoebiusLogHarmonic_tendsto_zero.mul_const
    (pairedEtaArithmeticHarmonicPrefix L)).sub hp
  simp only [zero_mul, sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop L] with M hM hML
  exact (pairedEtaMoebiusArithmeticCellResidual_log_eq_primeShell (by omega) hL hML).symm

/-- The actual signed residual square sum on every fixed finite collection of initial physical cells tends to zero; the physical cutoff here is fixed before the arithmetic cutoff grows. -/
theorem pairedEtaMoebiusArithmeticSquarePrefix_tendsto_zero (R : ℕ) :
    Tendsto (fun M : ℕ ↦ pairedEtaMoebiusArithmeticSquarePrefix M R
      (pairedEtaMoebiusTrialLogWeight M)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range R) (fun n _ ↦
    (pairedEtaMoebiusArithmeticCellResidual_tendsto_zero (Nat.succ_pos n)).pow 2)
  simpa only [pairedEtaMoebiusArithmeticSquarePrefix, zero_pow (by decide : 2 ≠ 0),
    Finset.sum_const_zero] using h

end

end RiemannGaussian
