import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaCompletionReflectionMaximumRigidity

/-!
# Exact leading-coefficient gain across complementary zeros

The maximum-modulus argument proves that the eta reflection multiplier has
norm below, equal to, or above one exactly according to the horizontal
position relative to the critical line.  This module transfers that complete
sign law to the first nonzero localized Gaussian coefficient at a zeta zero.

Completion symmetry already balances the two positive coefficients after
multiplication by their complementary completion weights.  Dividing that
identity by positive quantities now gives an exact formula: the partner-to-
original coefficient ratio is `‖B(rho)‖²`.  Consequently the raw coefficient
ordering detects which side of the critical line contains `rho`, with no
height or simplicity assumption.

This is an arithmetic-moment interface for the remaining RH problem.  It does
not prove that the two coefficients agree; an independent argument forcing
that equality is still required.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The partner-to-original ratio of the first nonzero localized Gaussian
coefficients is exactly the squared norm of the eta reflection multiplier. -/
theorem
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_reflectionMultiplier_normSq
    (rho : NontrivialZetaZero) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho) /
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho =
      Complex.normSq (pairedEtaLaplaceReflectionMultiplier rho.1) := by
  rw [normSq_pairedEtaLaplaceReflectionMultiplier_eq_weight_div]
  have hcoefficient :
      pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho ≠ 0 :=
    (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_pos rho).ne'
  have hpartnerWeight :
      pairedEtaCompletedLaplaceWeight
          (NontrivialZetaZero.conjugatePartner rho).1 ≠ 0 :=
    (pairedEtaCompletedLaplaceWeight_pos
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho))
      (NontrivialZetaZero.re_lt_one
        (NontrivialZetaZero.conjugatePartner rho))).ne'
  apply (div_eq_div_iff hcoefficient hpartnerWeight).2
  simpa only [mul_comm] using
    pairedEtaCompletedLaplaceWeight_mul_largeTimeLeadingCoefficient_conjugatePartner
      rho

/-- In the open strip, squared multiplier norm below one is equivalent to
lying strictly left of the critical line. -/
theorem normSq_pairedEtaLaplaceReflectionMultiplier_lt_one_iff_re_lt_half
    {s : ℂ} (hspos : 0 < s.re) (hsone : s.re < 1) :
    Complex.normSq (pairedEtaLaplaceReflectionMultiplier s) < 1 ↔
      s.re < 1 / 2 := by
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro hsq
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · exact hlt
    · have hunit :=
        normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_of_re_eq_half heq
      rw [Complex.normSq_eq_norm_sq] at hunit
      nlinarith
    · have hnorm :=
        norm_pairedEtaLaplaceReflectionMultiplier_gt_one_of_half_lt_re
          hgt hsone
      nlinarith [norm_nonneg (pairedEtaLaplaceReflectionMultiplier s)]
  · intro hlt
    have hnorm :=
      norm_pairedEtaLaplaceReflectionMultiplier_lt_one_of_re_lt_half
        hspos hlt
    nlinarith [norm_nonneg (pairedEtaLaplaceReflectionMultiplier s)]

/-- In the open strip, squared multiplier norm above one is equivalent to
lying strictly right of the critical line. -/
theorem normSq_pairedEtaLaplaceReflectionMultiplier_gt_one_iff_half_lt_re
    {s : ℂ} (hspos : 0 < s.re) (hsone : s.re < 1) :
    1 < Complex.normSq (pairedEtaLaplaceReflectionMultiplier s) ↔
      1 / 2 < s.re := by
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro hsq
    rcases lt_trichotomy s.re (1 / 2) with hlt | heq | hgt
    · have hnorm :=
        norm_pairedEtaLaplaceReflectionMultiplier_lt_one_of_re_lt_half
          hspos hlt
      nlinarith [norm_nonneg (pairedEtaLaplaceReflectionMultiplier s)]
    · have hunit :=
        normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_of_re_eq_half heq
      rw [Complex.normSq_eq_norm_sq] at hunit
      nlinarith
    · exact hgt
  · intro hgt
    have hnorm :=
      norm_pairedEtaLaplaceReflectionMultiplier_gt_one_of_half_lt_re
        hgt hsone
    nlinarith [norm_nonneg (pairedEtaLaplaceReflectionMultiplier s)]

/-- The complementary coefficient is smaller exactly when the original zero
lies left of the critical line. -/
theorem
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_lt_iff_re_lt_half
    (rho : NontrivialZetaZero) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho) <
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho ↔
      rho.1.re < 1 / 2 := by
  rw [← div_lt_one₀
    (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_pos rho),
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_reflectionMultiplier_normSq]
  exact normSq_pairedEtaLaplaceReflectionMultiplier_lt_one_iff_re_lt_half
    (NontrivialZetaZero.zero_lt_re rho)
    (NontrivialZetaZero.re_lt_one rho)

/-- The original coefficient is smaller exactly when the original zero lies
right of the critical line. -/
theorem
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_lt_conjugatePartner_iff_half_lt_re
    (rho : NontrivialZetaZero) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho <
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho) ↔
      1 / 2 < rho.1.re := by
  rw [← one_lt_div₀
    (pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_pos rho),
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_div_eq_reflectionMultiplier_normSq]
  exact normSq_pairedEtaLaplaceReflectionMultiplier_gt_one_iff_half_lt_re
    (NontrivialZetaZero.zero_lt_re rho)
    (NontrivialZetaZero.re_lt_one rho)

/-- The signed coefficient distortion is positive exactly for zeros left of
the critical line. -/
theorem
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_sub_conjugatePartner_pos_iff_re_lt_half
    (rho : NontrivialZetaZero) :
    0 < pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho -
        pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho) ↔
      rho.1.re < 1 / 2 := by
  rw [sub_pos]
  exact
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_conjugatePartner_lt_iff_re_lt_half
      rho

/-- The signed coefficient distortion is negative exactly for zeros right of
the critical line. -/
theorem
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_sub_conjugatePartner_neg_iff_half_lt_re
    (rho : NontrivialZetaZero) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho -
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho) < 0 ↔
      1 / 2 < rho.1.re := by
  rw [sub_neg]
  exact
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_lt_conjugatePartner_iff_half_lt_re
      rho

end
end RiemannGaussian
