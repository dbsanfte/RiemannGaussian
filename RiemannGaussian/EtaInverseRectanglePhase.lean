import RiemannGaussian.EtaInverseProductCoefficients
import RiemannGaussian.EtaWeightedDivisorSampling

/-!
# The coupled parity estimate for the actual inverse rectangle

The complete rectangular inverse phase is grouped by exact product
divisors, retaining every inner Möbius coefficient. Its proved collision
energy and the literal divisor Fourier support give a mean-square bound
for both divisor sums together.
-/

open Complex
open scoped Classical ArithmeticFunction.Moebius

namespace RiemannGaussian

noncomputable section

/-- The full leading quotient phase of an actual inverse rectangle,
with every signed product fiber kept inside the family. -/
def pairedEtaInverseRectangleParityFamily (M E D : ℕ) : ℂ :=
  pairedEtaWeightedDivisorParityFamily
    (fun n ↦ (pairedEtaInverseProductCoefficient E D n : ℝ)) M (E * D)

/-- The grouped phase is exactly the original double divisor sum,
with the Möbius sign on the inner divisor and the cutoff at their product. -/
theorem pairedEtaInverseRectangleParityFamily_eq_double_sum (M E D : ℕ) :
    pairedEtaInverseRectangleParityFamily M E D =
      ∑ d ∈ Finset.Icc 1 E, ∑ e ∈ Finset.Icc 1 D,
        (μ e : ℂ) * (pairedEtaDirichletSign (M / (d * e)) : ℂ) := by
  unfold pairedEtaInverseRectangleParityFamily pairedEtaWeightedDivisorParityFamily
  simp only [Complex.ofReal_intCast]
  exact sum_pairedEtaInverseProductCoefficient_mul E D
    (fun n ↦ (pairedEtaDirichletSign (M / n) : ℂ))

/-- The original inverse rectangle has a jointly estimated leading
phase. Both divisor lengths enter through their product and the
explicit logarithmic coefficient-energy costs. -/
theorem pairedEtaInverseRectangleParityFamily_meanSquare_le
    (A : ℕ) {E D L : ℕ} (hE : 1 ≤ E) (hD : 1 ≤ D) (hEDL : (E * D) ^ 2 ≤ L) :
    (∑ n ∈ Finset.range L, ‖pairedEtaInverseRectangleParityFamily (A + n) E D‖ ^ 2) / L ≤
      5 * finiteCircleSamplingConstant * ((E : ℝ) * D) *
        (1 + Real.log E) ^ 2 * (1 + Real.log (E * D : ℕ)) ^ 2 := by
  have hED : 1 ≤ E * D := by nlinarith
  have h := pairedEtaWeightedDivisorParityFamily_meanSquare_le_quadratic
    (fun n ↦ (pairedEtaInverseProductCoefficient E D n : ℝ)) A hED hEDL
  apply h.trans
  have hb := mul_le_mul_of_nonneg_left (sum_sq_pairedEtaInverseProductCoefficient_le_log_sq hE D)
    (show 0 ≤ 5 * finiteCircleSamplingConstant * (1 + Real.log (E * D : ℕ)) ^ 2 by
      have hS := finiteCircleSamplingConstant_pos.le
      positivity)
  convert hb using 1
  ring

end

end RiemannGaussian
