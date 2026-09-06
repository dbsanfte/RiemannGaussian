import RiemannGaussian.EtaZetaPrimeProduct
import RiemannGaussian.EtaCurrentReturnGrowth

/-!
# An explicit arithmetic zero margin and its return-growth consequence

The original nontrivial zeta zeros lie in a narrower strip whose margin is
an explicit positive function of their ordinate. This follows from prime
positivity and the proved eta bounds, with no assumed zero-free region.
Reflection transports the right-edge exclusion to the left edge. The same
margin bounds the exponent of the unchanged Gaussian return. That exponent
is still positive in this estimate, so cutoff-independent boundedness
remains a separate open objective.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit ordinate-dependent strip margin obtained from the eta
support estimate and the classical prime-product inequality. -/
def etaPrimeProductZeroMargin (y : ℝ) : ℝ :=
  min (1 / 4) (|y| ^ 5 / (16 * 3200 ^ 3 * 64 ^ 4 * (|y| + 21) ^ 10))

/-- The arithmetic strip margin is positive at every nonzero ordinate. -/
theorem etaPrimeProductZeroMargin_pos {y : ℝ} (hy : y ≠ 0) :
    0 < etaPrimeProductZeroMargin y := by
  have ht : 0 < |y| := abs_pos.mpr hy
  unfold etaPrimeProductZeroMargin
  positivity

/-- The formula retains the narrower-strip threshold used in Cauchy's
estimate, even at small ordinates. -/
theorem etaPrimeProductZeroMargin_le_quarter (y : ℝ) : etaPrimeProductZeroMargin y ≤ 1 / 4 :=
  min_le_left _ _

/-- Every actual nontrivial zeta zero has at least the explicit
prime-product distance from the line of real part one. -/
theorem etaPrimeProductZeroMargin_le_one_sub_re (rho : NontrivialZetaZero) :
    etaPrimeProductZeroMargin rho.1.im ≤ 1 - rho.1.re := by
  by_cases hrho : 3 / 4 ≤ rho.1.re
  · refine (min_le_right _ _).trans ?_
    have ht : 0 < |rho.1.im| := abs_pos.mpr (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
    have hc : 0 < 16 * 3200 ^ 3 * 64 ^ 4 * (|rho.1.im| + 21) ^ 10 := by positivity
    rw [div_le_iff₀ hc]
    have h := one_le_etaPrimeProduct_zero_gap rho hrho
    rw [div_mul_eq_mul_div] at h
    have hp := (le_div_iff₀ (pow_pos ht 5)).mp h
    simpa only [one_mul, mul_one, mul_comm] using hp
  · exact (etaPrimeProductZeroMargin_le_quarter rho.1.im).trans (by linarith)

/-- Completed reflection gives the matching left-edge exclusion at the
same actual ordinate. -/
theorem etaPrimeProductZeroMargin_le_re (rho : NontrivialZetaZero) :
    etaPrimeProductZeroMargin rho.1.im ≤ rho.1.re := by
  have h := etaPrimeProductZeroMargin_le_one_sub_re (NontrivialZetaZero.conjugatePartner rho)
  simpa using h

/-- The literal nontrivial zero carrier lies in the explicit narrower
strip. This is a zero-location bound with all analytic inputs discharged. -/
theorem nontrivialZetaZero_mem_etaPrimeProduct_strip (rho : NontrivialZetaZero) :
    rho.1.re ∈ Icc (etaPrimeProductZeroMargin rho.1.im) (1 - etaPrimeProductZeroMargin rho.1.im) := by
  exact ⟨etaPrimeProductZeroMargin_le_re rho, by linarith [etaPrimeProductZeroMargin_le_one_sub_re rho]⟩

/-- The explicit margin bounds the horizontal displacement controlling
the original weighted-current and return growth. -/
theorem pairedEtaCurrentHorizontalDisplacement_le_etaPrimeProduct (rho : NontrivialZetaZero) :
    pairedEtaCurrentHorizontalDisplacement rho ≤ 1 - 2 * etaPrimeProductZeroMargin rho.1.im := by
  have h := nontrivialZetaZero_mem_etaPrimeProduct_strip rho
  unfold pairedEtaCurrentHorizontalDisplacement
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The new arithmetic exponent is uniformly separated from one at each
fixed actual ordinate, while remaining a positive exponent. -/
theorem etaPrimeProduct_return_exponent_bounds (rho : NontrivialZetaZero) :
    1 / 2 ≤ 1 - 2 * etaPrimeProductZeroMargin rho.1.im ∧
      1 - 2 * etaPrimeProductZeroMargin rho.1.im < 1 := by
  have hp := etaPrimeProductZeroMargin_pos (NontrivialZetaZero.im_ne_zero_of_eta_mass rho)
  have hq := etaPrimeProductZeroMargin_le_quarter rho.1.im
  constructor <;> linarith

/-- Prime positivity gives an explicit ordinate-based growth exponent
for the unchanged Gaussian return, in both analytic multiplicity branches.
The right side still depends on the cutoff and does not prove the goal's
uniform weighted bound. -/
theorem pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_le_etaPrimeProduct
    (rho : NontrivialZetaZero) (K : ℕ) :
    (∑ N ∈ Finset.range K, (2 * N + 1 : ℝ) * ‖pairedEtaLeadingCurrentLinearHeatReturn rho N‖) ≤
      pairedEtaCurrentReturnGrowthConstant rho *
        (K + 1 : ℝ) ^ (1 - 2 * etaPrimeProductZeroMargin rho.1.im) := by
  apply (pairedEtaLeadingCurrentLinearHeatReturn_firstMoment_growth_le rho K).trans
  apply mul_le_mul_of_nonneg_left _ (pairedEtaCurrentReturnGrowthConstant_nonneg rho)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) K])
    (pairedEtaCurrentHorizontalDisplacement_le_etaPrimeProduct rho)

end

end RiemannGaussian
