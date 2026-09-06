import RiemannGaussian.EtaMoebiusPhysicalMeanSquare

/-!
# Signed growing-family bounds without individual endpoint powers

The original completed Möbius terms retain the repository's signed reflected
pair orientation. Their exact double sum precedes the first absolute average
bound, whose two physical decay rates are the complementary zero coordinates.
The finite divisor range remains cubic, and these forward Möbius families do
not replace the inverse-weighted head or adjacent moments of the current.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The original signed completed pair of the two unmodified Möbius
families, with no individual endpoint powers attached. -/
def pairedEtaSignedCompletedMoebiusOriginalPair (rho : NontrivialZetaZero) (M D : ℕ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaCompletedMoebiusPartialAggregate (NontrivialZetaZero.conjugatePartner rho) M D)
    (pairedEtaCompletedMoebiusPartialAggregate (NontrivialZetaZero.conjugatePartner rho) M D)
    (pairedEtaCompletedMoebiusPartialAggregate rho M D)
    (pairedEtaCompletedMoebiusPartialAggregate rho M D)

/-- Every original completed divisor pair survives in the signed double
sum, including its two arithmetic coefficients and completion phases. -/
theorem pairedEtaSignedCompletedMoebiusOriginalPair_eq_double_sum
    (rho : NontrivialZetaZero) (M D : ℕ) :
    pairedEtaSignedCompletedMoebiusOriginalPair rho M D =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, etaSignedCompletedPair
        (pairedEtaCompletedMoebiusTerm (NontrivialZetaZero.conjugatePartner rho) M d)
        (pairedEtaCompletedMoebiusTerm (NontrivialZetaZero.conjugatePartner rho) M e)
        (pairedEtaCompletedMoebiusTerm rho M d)
        (pairedEtaCompletedMoebiusTerm rho M e) := by
  simp only [pairedEtaSignedCompletedMoebiusOriginalPair, pairedEtaCompletedMoebiusPartialAggregate,
    etaSignedCompletedPair, map_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1 <;> rw [Finset.sum_comm]

/-- The exact signed self-pair is the oriented difference of the two
original family squares, before taking an absolute value. -/
theorem pairedEtaSignedCompletedMoebiusOriginalPair_eq_channels
    (rho : NontrivialZetaZero) (M D : ℕ) :
    pairedEtaSignedCompletedMoebiusOriginalPair rho M D =
      ((‖pairedEtaCompletedMoebiusPartialAggregate (NontrivialZetaZero.conjugatePartner rho) M D‖ ^ 2 -
        ‖pairedEtaCompletedMoebiusPartialAggregate rho M D‖ ^ 2 : ℝ) : ℂ) := by
  simp only [pairedEtaSignedCompletedMoebiusOriginalPair, etaSignedCompletedPair,
    Complex.mul_conj', Complex.conj_mul', Complex.ofReal_sub, Complex.ofReal_pow]

/-- Averaging retains the exact difference of the two original completed
family mean squares on one identical physical window. -/
theorem pairedEtaSignedCompletedMoebiusOriginalPair_average_eq_channels
    (rho : NontrivialZetaZero) (A L D : ℕ) :
    (∑ r ∈ Finset.range L, pairedEtaSignedCompletedMoebiusOriginalPair rho (A + r) D) / (L : ℂ) =
      ((pairedEtaCompletedMoebiusOriginalMeanSquare (NontrivialZetaZero.conjugatePartner rho) A L D -
        pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D : ℝ) : ℂ) := by
  simp_rw [pairedEtaSignedCompletedMoebiusOriginalPair_eq_channels]
  unfold pairedEtaCompletedMoebiusOriginalMeanSquare
  push_cast
  rw [Finset.sum_sub_distrib, sub_div]

/-- The first absolute window average of the original signed completed
Möbius family, with all individual endpoint powers removed. -/
def pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute (rho : NontrivialZetaZero) (A L D : ℕ) : ℝ :=
  (∑ r ∈ Finset.range L, ‖pairedEtaSignedCompletedMoebiusOriginalPair rho (A + r) D‖) / L

/-- The signed first absolute average is bounded by the two original
mean squares after preserving the exact signed identity. -/
theorem pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute_le_channels
    (rho : NontrivialZetaZero) (A L D : ℕ) :
    pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute rho A L D ≤
      pairedEtaCompletedMoebiusOriginalMeanSquare (NontrivialZetaZero.conjugatePartner rho) A L D +
        pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D := by
  unfold pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute pairedEtaCompletedMoebiusOriginalMeanSquare
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
  apply Finset.sum_le_sum
  intro r hr
  rw [pairedEtaSignedCompletedMoebiusOriginalPair_eq_channels, Complex.norm_real, Real.norm_eq_abs]
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]

/-- The two original completion channels have their complementary
physical decay rates in a proved first absolute average bound. The actual
terms are unmodified, and no simplicity or critical-line premise is assumed. -/
theorem pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute_le_growing
    (rho : NontrivialZetaZero) {A L D : ℕ} (hD : 1 ≤ D)
    (hDA : D ^ 3 ≤ A) (hDL : D ^ 3 ≤ L) :
    pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute rho A L D ≤
      (D : ℝ) * (1 + Real.log D) *
        (pairedEtaCompletedMoebiusOriginalFamilyConstant (NontrivialZetaZero.conjugatePartner rho) *
            (A : ℝ) ^ (-2 * (1 - rho.1.re)) +
          pairedEtaCompletedMoebiusOriginalFamilyConstant rho * (A : ℝ) ^ (-2 * rho.1.re)) := by
  apply (pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute_le_channels rho A L D).trans
  have h := add_le_add
    (pairedEtaCompletedMoebiusOriginalMeanSquare_le_growing
      (NontrivialZetaZero.conjugatePartner rho) hD hDA hDL)
    (pairedEtaCompletedMoebiusOriginalMeanSquare_le_growing rho hD hDA hDL)
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re, Complex.conj_re] at h
  convert h using 1
  ring

end

end RiemannGaussian
