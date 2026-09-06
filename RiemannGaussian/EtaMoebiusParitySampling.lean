import RiemannGaussian.EtaMoebiusParityEnergy
import RiemannGaussian.FiniteCircleDualSampling

/-!
# Square-scale sampling for the actual eta divisor family

The literal quotient phases have proved separated Fourier support and an
exact signed gcd energy. Finite dual sampling combines these facts with
every Möbius coefficient and completion factor retained upstream. The
auxiliary grid disappears from the resulting physical-window estimate.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The leading parity family's actual energy on a finite physical window. -/
def pairedEtaCompletedMoebiusParityMeanSquare (rho : NontrivialZetaZero) (A L D : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L, ‖pairedEtaCompletedMoebiusParityFamily rho (A + n) D‖ ^ 2) / L

/-- Exact spectral separation and the full gcd covariance bound the
literal completed eta family with square-scale window cost. -/
theorem pairedEtaCompletedMoebiusParityFamily_window_sq_le
    (rho : NontrivialZetaZero) (A : ℕ) {D L : ℕ} (hD : 1 ≤ D) (hL : 0 < L) :
    (∑ n ∈ Finset.range L, ‖pairedEtaCompletedMoebiusParityFamily rho (A + n) D‖ ^ 2) ≤
      finiteCircleSamplingConstant * (4 * (D : ℝ) ^ 2 + L) *
        (‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2 * D * (1 + Real.log D)) := by
  let Q := pairedEtaDivisorFourierGrid D L
  have hQpos : 0 < Q := pairedEtaDivisorFourierGrid_pos D hL
  let : NeZero Q := ⟨hQpos.ne'⟩
  have hperiod : ∀ d ∈ Finset.Icc 1 D, ∀ e ∈ Finset.Icc 1 D, 2 * d * e ∣ Q := by
    intro d hd e he
    exact (pairedEtaDivisorPairPeriod_dvd_block hd he).trans (dvd_mul_right _ _)
  have hsingle : ∀ d ∈ Finset.Icc 1 D, 2 * d ∣ Q := by
    intro d hd
    exact (pairedEtaDivisorPeriod_dvd_block hd).trans (dvd_mul_right _ _)
  have hscale : 4 * D ^ 2 * pairedEtaDivisorFourierBlock D ≤ Q := by
    dsimp [Q, pairedEtaDivisorFourierGrid, pairedEtaDivisorFourierBudget]
    nlinarith
  have hs := sum_range_finiteCircleSynthesis_separated_le
    (pairedEtaDivisorFourierSpectrum D Q)
    (finitePeriodicFourierCoefficient
      (fun n ↦ pairedEtaCompletedMoebiusParityFamily rho (A + n) D))
    (pairedEtaDivisorFourierBlock_pos D)
    (by unfold pairedEtaDivisorFourierBudget; omega : 0 < pairedEtaDivisorFourierBudget D L)
    (rfl : Q = pairedEtaDivisorFourierBlock D * pairedEtaDivisorFourierBudget D L)
    (by unfold pairedEtaDivisorFourierBudget; omega : L ≤ pairedEtaDivisorFourierBudget D L)
    (pairedEtaDivisorFourierSpectrum_separated hD hscale)
  simp_rw [pairedEtaCompletedMoebiusParityFamily_eq_fourier rho A D hsingle] at hs
  rw [pairedEtaCompletedMoebiusParityFamily_fourier_energy rho A D hsingle] at hs
  apply hs.trans
  have h := mul_le_mul_of_nonneg_left
    (pairedEtaCompletedMoebiusParityFamily_period_energy_le rho A D hQpos hperiod)
    (mul_nonneg finiteCircleSamplingConstant_pos.le
      (Nat.cast_nonneg (α := ℝ) (pairedEtaDivisorFourierBudget D L)))
  simpa only [pairedEtaDivisorFourierBudget, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_pow] using h

/-- The actual leading eta family has linear logarithmic mean-square
cost throughout the quadratic divisor range, with an explicit constant. -/
theorem pairedEtaCompletedMoebiusParityMeanSquare_le_quadratic
    (rho : NontrivialZetaZero) (A : ℕ) {D L : ℕ} (hD : 1 ≤ D) (hDL : D ^ 2 ≤ L) :
    pairedEtaCompletedMoebiusParityMeanSquare rho A L D ≤
      (5 * finiteCircleSamplingConstant * ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2) *
        D * (1 + Real.log D) := by
  have hL : 0 < L := (pow_pos hD 2).trans_le hDL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlog : 0 ≤ 1 + Real.log D := by linarith [Real.log_nonneg hDR]
  have hDLR : (D : ℝ) ^ 2 ≤ L := by exact_mod_cast hDL
  have hbudget : 4 * (D : ℝ) ^ 2 + L ≤ 5 * L := by linarith
  unfold pairedEtaCompletedMoebiusParityMeanSquare
  apply (div_le_iff₀ hLR).mpr
  apply (pairedEtaCompletedMoebiusParityFamily_window_sq_le rho A hD hL).trans
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbudget finiteCircleSamplingConstant_pos.le)
    (by positivity : 0 ≤ ‖pairedEtaXiCompletionFactor rho.1‖ ^ 2 / 2 * D * (1 + Real.log D))
  convert h using 1
  ring

end

end RiemannGaussian
