import RiemannGaussian.EtaMomentPhysicalFamily
import RiemannGaussian.EtaCurrentMomentMoebiusInverse

/-!
# Quantitative reduction inside the original moment inverse

The inner divisor truncation retains the actual outer inverse weight,
divided physical cutoff, and translated center. Its full inner range is
exactly the existing inverse term. The completed moment reduction applies
with the center condition discharged for every actual outer divisor.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- An actual inverse term with its inner divisor range explicitly truncated. -/
def pairedEtaCompletedMomentInversePartialTerm (rho : NontrivialZetaZero) (k : ℕ)
    (a : ℝ) (M d D : ℕ) : ℂ :=
  (d : ℂ) ^ (-rho.1) * pairedEtaCompletedMomentOriginalFamily rho k (a - Real.log d) (M / d) D

/-- The complete inner range recovers the original inverse term exactly. -/
theorem pairedEtaCompletedMomentInversePartialTerm_full (rho : NontrivialZetaZero)
    (k : ℕ) (a : ℝ) (M d : ℕ) :
    pairedEtaCompletedMomentInversePartialTerm rho k a M d (M / d) =
      pairedEtaCompletedMomentInverseTerm rho k a M d := rfl

/-- The exact inverse reduction retains the outer complex divisor
weight and its actual translated center before estimating either one. -/
theorem pairedEtaCompletedMomentInversePartialTerm_sub_zero_eq
    (rho : NontrivialZetaZero) (k : ℕ) (a : ℝ) (M d D : ℕ) :
    ((M / d : ℕ) : ℂ) ^ rho.1 *
      (pairedEtaCompletedMomentInversePartialTerm rho k a M d D -
        pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMomentInversePartialTerm rho 0 a M d D) =
      (d : ℂ) ^ (-rho.1) * (((M / d : ℕ) : ℂ) ^ rho.1 *
        (pairedEtaCompletedMomentOriginalFamily rho k (a - Real.log d) (M / d) D -
          pairedEtaMomentParityCoefficient rho k * pairedEtaCompletedMoebiusPartialAggregate rho (M / d) D)) := by
  simp only [pairedEtaCompletedMomentInversePartialTerm, pairedEtaCompletedMomentOriginalFamily_zero]
  ring

/-- The actual inverse weight and moving center have a discharged
moment-reduction error with the inner cutoff, outer divisor, and zero's
horizontal coordinate all explicit. -/
theorem norm_pairedEtaCompletedMomentInversePartialTerm_sub_zero_le
    (rho : NontrivialZetaZero) {k M d D : ℕ} (hk : k < analyticZetaZeroMultiplicity rho)
    (hd : d ∈ Finset.Icc 1 M) (hD : D ≤ M / d) :
    ‖((M / d : ℕ) : ℂ) ^ rho.1 *
      (pairedEtaCompletedMomentInversePartialTerm rho k (Real.log (M + 1 : ℝ)) M d D -
        pairedEtaMomentParityCoefficient rho k *
          pairedEtaCompletedMomentInversePartialTerm rho 0 (Real.log (M + 1 : ℝ)) M d D)‖ ≤
      (d : ℝ) ^ (-rho.1.re) * pairedEtaCompletedMomentPhysicalErrorConstant rho k *
        (D : ℝ) ^ 2 / (M / d : ℕ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  have hn : ‖(d : ℂ) ^ (-rho.1)‖ = (d : ℝ) ^ (-rho.1.re) := by
    simpa only [Complex.ofReal_natCast, Complex.neg_re] using
      Complex.norm_cpow_eq_rpow_re_of_pos hdR (-rho.1)
  rw [pairedEtaCompletedMomentInversePartialTerm_sub_zero_eq, norm_mul, hn]
  have h := mul_le_mul_of_nonneg_left
    (norm_pairedEtaCompletedMomentOriginalFamily_physical_sub_zero_le rho hk hD
      (pairedEtaMomentInverseCenter_mem_interval hd))
    (Real.rpow_nonneg hdR.le (-rho.1.re))
  simpa only [mul_div_assoc, mul_assoc] using h

end

end RiemannGaussian
