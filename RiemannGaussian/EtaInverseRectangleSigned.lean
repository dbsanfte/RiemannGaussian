import RiemannGaussian.EtaInverseRectangleMeanSquare

/-!
# Signed mixed estimates for the actual inverse rectangle

Both reflected completed channels retain the same actual outer and inner
divisor ranges, moving center, and moment orders. Their complete complex
pair precedes the first absolute average. The joint rectangle estimate
then applies below the full analytic multiplicity, including its two
adjacent repeated-zero orders.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The actual signed mixed inverse rectangle at the next physical logarithmic endpoint. -/
def pairedEtaSignedCompletedMomentInverseRectanglePair
    (rho : NontrivialZetaZero) (k l M E D : ℕ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaCompletedMomentInverseRectangle (NontrivialZetaZero.conjugatePartner rho) k
      (Real.log (M + 1 : ℝ)) M E D)
    (pairedEtaCompletedMomentInverseRectangle (NontrivialZetaZero.conjugatePartner rho) l
      (Real.log (M + 1 : ℝ)) M E D)
    (pairedEtaCompletedMomentInverseRectangle rho k (Real.log (M + 1 : ℝ)) M E D)
    (pairedEtaCompletedMomentInverseRectangle rho l (Real.log (M + 1 : ℝ)) M E D)

/-- The full signed rectangle pair retains every original outer
inverse pair, with both complete inner sums and their translated centers. -/
theorem pairedEtaSignedCompletedMomentInverseRectanglePair_eq_double_sum
    (rho : NontrivialZetaZero) (k l M E D : ℕ) :
    pairedEtaSignedCompletedMomentInverseRectanglePair rho k l M E D =
      ∑ d ∈ Finset.Icc 1 E, ∑ e ∈ Finset.Icc 1 E, etaSignedCompletedPair
        (pairedEtaCompletedMomentInversePartialTerm (NontrivialZetaZero.conjugatePartner rho) k
          (Real.log (M + 1 : ℝ)) M d D)
        (pairedEtaCompletedMomentInversePartialTerm (NontrivialZetaZero.conjugatePartner rho) l
          (Real.log (M + 1 : ℝ)) M e D)
        (pairedEtaCompletedMomentInversePartialTerm rho k (Real.log (M + 1 : ℝ)) M d D)
        (pairedEtaCompletedMomentInversePartialTerm rho l (Real.log (M + 1 : ℝ)) M e D) := by
  simp only [pairedEtaSignedCompletedMomentInverseRectanglePair, pairedEtaCompletedMomentInverseRectangle,
    etaSignedCompletedPair, map_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1 <;> rw [Finset.sum_comm]

/-- The first absolute average of the complete original signed inverse rectangle. -/
def pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute
    (rho : NontrivialZetaZero) (k l A L E D : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L,
    ‖pairedEtaSignedCompletedMomentInverseRectanglePair rho k l (A + n) E D‖) / L

/-- The complete signed first absolute average is estimated only
after preserving its full inverse pairs and both completion channels. -/
theorem pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute_le_channels
    (rho : NontrivialZetaZero) (k l A L E D : ℕ) :
    pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute rho k l A L E D ≤
      (pairedEtaCompletedMomentInverseRectangleMeanSquare (NontrivialZetaZero.conjugatePartner rho) k A L E D +
       pairedEtaCompletedMomentInverseRectangleMeanSquare (NontrivialZetaZero.conjugatePartner rho) l A L E D +
       pairedEtaCompletedMomentInverseRectangleMeanSquare rho k A L E D +
       pairedEtaCompletedMomentInverseRectangleMeanSquare rho l A L E D) / 2 := by
  unfold pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute
    pairedEtaCompletedMomentInverseRectangleMeanSquare
  rw [← add_div, ← add_div, ← add_div, div_right_comm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  unfold pairedEtaSignedCompletedMomentInverseRectanglePair
  apply (norm_etaSignedCompletedPair_le _ _ _ _).trans
  nlinarith [sq_nonneg
    (‖pairedEtaCompletedMomentInverseRectangle (NontrivialZetaZero.conjugatePartner rho) k
      (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) E D‖ -
     ‖pairedEtaCompletedMomentInverseRectangle (NontrivialZetaZero.conjugatePartner rho) l
      (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) E D‖),
    sq_nonneg
    (‖pairedEtaCompletedMomentInverseRectangle rho k (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) E D‖ -
     ‖pairedEtaCompletedMomentInverseRectangle rho l (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) E D‖)]

/-- The explicit signed mixed constant retains both original moment orders. -/
def pairedEtaCompletedMixedMomentInverseRectangleConstant
    (rho : NontrivialZetaZero) (k l : ℕ) : ℝ :=
  (pairedEtaCompletedMomentInverseRectangleConstant rho k +
    pairedEtaCompletedMomentInverseRectangleConstant rho l) / 2

/-- The original signed inverse rectangle has a joint first absolute
bound with both complementary physical decay rates, throughout the
proved quadratic product range and below the actual zero multiplicity. -/
theorem pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute_le_quadratic
    (rho : NontrivialZetaZero) {k l A L E D : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (hl : l < analyticZetaZeroMultiplicity rho)
    (hE : 1 ≤ E) (hD : 1 ≤ D) (hEDA : (E * D) ^ 2 ≤ A) (hEDL : (E * D) ^ 2 ≤ L) :
    pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute rho k l A L E D ≤
      pairedEtaInverseRectangleBudget E D *
        (pairedEtaCompletedMixedMomentInverseRectangleConstant (NontrivialZetaZero.conjugatePartner rho) k l *
            (A : ℝ) ^ (-2 * (1 - rho.1.re)) +
          pairedEtaCompletedMixedMomentInverseRectangleConstant rho k l * (A : ℝ) ^ (-2 * rho.1.re)) := by
  have hkp : k < analyticZetaZeroMultiplicity (NontrivialZetaZero.conjugatePartner rho) := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hk
  have hlp : l < analyticZetaZeroMultiplicity (NontrivialZetaZero.conjugatePartner rho) := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hl
  have h := div_le_div_of_nonneg_right (add_le_add (add_le_add (add_le_add
    (pairedEtaCompletedMomentInverseRectangleMeanSquare_le_quadratic
      (NontrivialZetaZero.conjugatePartner rho) hkp hE hD hEDA hEDL)
    (pairedEtaCompletedMomentInverseRectangleMeanSquare_le_quadratic
      (NontrivialZetaZero.conjugatePartner rho) hlp hE hD hEDA hEDL))
    (pairedEtaCompletedMomentInverseRectangleMeanSquare_le_quadratic rho hk hE hD hEDA hEDL))
    (pairedEtaCompletedMomentInverseRectangleMeanSquare_le_quadratic rho hl hE hD hEDA hEDL))
    (by norm_num : (0 : ℝ) ≤ 2)
  apply (pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute_le_channels rho k l A L E D).trans
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re, Complex.conj_re] at h
  convert h using 1
  unfold pairedEtaCompletedMixedMomentInverseRectangleConstant
  ring

/-- The two adjacent orders in the original repeated-zero current
satisfy the joint signed rectangle bound, with their index conditions
discharged from the actual analytic multiplicity. -/
theorem pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute_adjacent_le_quadratic
    (rho : NontrivialZetaZero) (hm : 2 ≤ analyticZetaZeroMultiplicity rho)
    {A L E D : ℕ} (hE : 1 ≤ E) (hD : 1 ≤ D) (hEDA : (E * D) ^ 2 ≤ A) (hEDL : (E * D) ^ 2 ≤ L) :
    pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute rho
      (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) A L E D ≤
      pairedEtaInverseRectangleBudget E D *
        (pairedEtaCompletedMixedMomentInverseRectangleConstant (NontrivialZetaZero.conjugatePartner rho)
            (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) *
              (A : ℝ) ^ (-2 * (1 - rho.1.re)) +
          pairedEtaCompletedMixedMomentInverseRectangleConstant rho
            (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) *
              (A : ℝ) ^ (-2 * rho.1.re)) :=
  pairedEtaSignedCompletedMomentInverseRectangleMeanAbsolute_le_quadratic rho
    (by omega) (by omega) hE hD hEDA hEDL

end

end RiemannGaussian
