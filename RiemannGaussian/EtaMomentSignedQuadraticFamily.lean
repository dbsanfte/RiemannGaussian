import RiemannGaussian.EtaMomentQuadraticMeanSquare

/-!
# Signed mixed moment families at the actual moving center

Both original completed channels and every mixed divisor pair are retained
before taking the first absolute average. The quadratic family estimate
applies at every order below the actual zero multiplicity, including the
two adjacent orders in the repeated-zero current reconstruction.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The original signed mixed moment family at the next physical logarithmic endpoint. -/
def pairedEtaSignedCompletedMomentOriginalPair (rho : NontrivialZetaZero) (k l M D : ℕ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaCompletedMomentOriginalFamily (NontrivialZetaZero.conjugatePartner rho) k
      (Real.log (M + 1 : ℝ)) M D)
    (pairedEtaCompletedMomentOriginalFamily (NontrivialZetaZero.conjugatePartner rho) l
      (Real.log (M + 1 : ℝ)) M D)
    (pairedEtaCompletedMomentOriginalFamily rho k (Real.log (M + 1 : ℝ)) M D)
    (pairedEtaCompletedMomentOriginalFamily rho l (Real.log (M + 1 : ℝ)) M D)

/-- Every original mixed divisor pair survives in the exact signed sum,
with both moment orders, completion phases, and translated centers intact. -/
theorem pairedEtaSignedCompletedMomentOriginalPair_eq_double_sum
    (rho : NontrivialZetaZero) (k l M D : ℕ) :
    pairedEtaSignedCompletedMomentOriginalPair rho k l M D =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D, etaSignedCompletedPair
        (pairedEtaCompletedMomentMoebiusTerm (NontrivialZetaZero.conjugatePartner rho) k
          (Real.log (M + 1 : ℝ)) M d)
        (pairedEtaCompletedMomentMoebiusTerm (NontrivialZetaZero.conjugatePartner rho) l
          (Real.log (M + 1 : ℝ)) M e)
        (pairedEtaCompletedMomentMoebiusTerm rho k (Real.log (M + 1 : ℝ)) M d)
        (pairedEtaCompletedMomentMoebiusTerm rho l (Real.log (M + 1 : ℝ)) M e) := by
  simp only [pairedEtaSignedCompletedMomentOriginalPair, pairedEtaCompletedMomentOriginalFamily,
    etaSignedCompletedPair, map_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  congr 1 <;> rw [Finset.sum_comm]

/-- The first absolute average of the original signed mixed moment family. -/
def pairedEtaSignedCompletedMomentOriginalMeanAbsolute (rho : NontrivialZetaZero)
    (k l A L D : ℕ) : ℝ :=
  (∑ n ∈ Finset.range L, ‖pairedEtaSignedCompletedMomentOriginalPair rho k l (A + n) D‖) / L

/-- The signed mixed first absolute average is bounded only after
preserving its full complex double sum and both channel orientations. -/
theorem pairedEtaSignedCompletedMomentOriginalMeanAbsolute_le_channels
    (rho : NontrivialZetaZero) (k l A L D : ℕ) :
    pairedEtaSignedCompletedMomentOriginalMeanAbsolute rho k l A L D ≤
      (pairedEtaCompletedMomentOriginalMeanSquare (NontrivialZetaZero.conjugatePartner rho) k A L D +
       pairedEtaCompletedMomentOriginalMeanSquare (NontrivialZetaZero.conjugatePartner rho) l A L D +
       pairedEtaCompletedMomentOriginalMeanSquare rho k A L D +
       pairedEtaCompletedMomentOriginalMeanSquare rho l A L D) / 2 := by
  unfold pairedEtaSignedCompletedMomentOriginalMeanAbsolute pairedEtaCompletedMomentOriginalMeanSquare
  rw [← add_div, ← add_div, ← add_div, div_right_comm]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg L)
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_le_sum
  intro n hn
  unfold pairedEtaSignedCompletedMomentOriginalPair
  apply (norm_etaSignedCompletedPair_le _ _ _ _).trans
  nlinarith [sq_nonneg
    (‖pairedEtaCompletedMomentOriginalFamily (NontrivialZetaZero.conjugatePartner rho) k
      (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) D‖ -
     ‖pairedEtaCompletedMomentOriginalFamily (NontrivialZetaZero.conjugatePartner rho) l
      (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) D‖),
    sq_nonneg
    (‖pairedEtaCompletedMomentOriginalFamily rho k (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) D‖ -
     ‖pairedEtaCompletedMomentOriginalFamily rho l (Real.log ((A + n : ℕ) + 1 : ℝ)) (A + n) D‖)]

/-- The explicit mixed moment coefficient retains both actual orders. -/
def pairedEtaCompletedMixedMomentQuadraticConstant (rho : NontrivialZetaZero) (k l : ℕ) : ℝ :=
  (pairedEtaCompletedMomentQuadraticConstant rho k + pairedEtaCompletedMomentQuadraticConstant rho l) / 2

/-- The original signed mixed family has complementary physical decay
rates throughout the quadratic divisor range, at any two orders below
the zero's actual multiplicity. -/
theorem pairedEtaSignedCompletedMomentOriginalMeanAbsolute_le_quadratic
    (rho : NontrivialZetaZero) {k l A L D : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (hl : l < analyticZetaZeroMultiplicity rho)
    (hD : 1 ≤ D) (hDA : D ^ 2 ≤ A) (hDL : D ^ 2 ≤ L) :
    pairedEtaSignedCompletedMomentOriginalMeanAbsolute rho k l A L D ≤
      (D : ℝ) * (1 + Real.log D) *
        (pairedEtaCompletedMixedMomentQuadraticConstant (NontrivialZetaZero.conjugatePartner rho) k l *
            (A : ℝ) ^ (-2 * (1 - rho.1.re)) +
          pairedEtaCompletedMixedMomentQuadraticConstant rho k l * (A : ℝ) ^ (-2 * rho.1.re)) := by
  have hkp : k < analyticZetaZeroMultiplicity (NontrivialZetaZero.conjugatePartner rho) := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hk
  have hlp : l < analyticZetaZeroMultiplicity (NontrivialZetaZero.conjugatePartner rho) := by
    simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hl
  have h := div_le_div_of_nonneg_right (add_le_add (add_le_add (add_le_add
    (pairedEtaCompletedMomentOriginalMeanSquare_le_quadratic
      (NontrivialZetaZero.conjugatePartner rho) hkp hD hDA hDL)
    (pairedEtaCompletedMomentOriginalMeanSquare_le_quadratic
      (NontrivialZetaZero.conjugatePartner rho) hlp hD hDA hDL))
    (pairedEtaCompletedMomentOriginalMeanSquare_le_quadratic rho hk hD hDA hDL))
    (pairedEtaCompletedMomentOriginalMeanSquare_le_quadratic rho hl hD hDA hDL))
    (by norm_num : (0 : ℝ) ≤ 2)
  apply (pairedEtaSignedCompletedMomentOriginalMeanAbsolute_le_channels rho k l A L D).trans
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re, Complex.conj_re] at h
  convert h using 1
  unfold pairedEtaCompletedMixedMomentQuadraticConstant
  ring

/-- The exact adjacent orders used by the original repeated-zero
current satisfy the signed quadratic-family bound, with both index
conditions discharged from the actual analytic multiplicity. -/
theorem pairedEtaSignedCompletedMomentOriginalMeanAbsolute_adjacent_le_quadratic
    (rho : NontrivialZetaZero) (hm : 2 ≤ analyticZetaZeroMultiplicity rho)
    {A L D : ℕ} (hD : 1 ≤ D) (hDA : D ^ 2 ≤ A) (hDL : D ^ 2 ≤ L) :
    pairedEtaSignedCompletedMomentOriginalMeanAbsolute rho
      (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) A L D ≤
      (D : ℝ) * (1 + Real.log D) *
        (pairedEtaCompletedMixedMomentQuadraticConstant (NontrivialZetaZero.conjugatePartner rho)
            (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) *
              (A : ℝ) ^ (-2 * (1 - rho.1.re)) +
          pairedEtaCompletedMixedMomentQuadraticConstant rho
            (analyticZetaZeroMultiplicity rho - 2) (analyticZetaZeroMultiplicity rho - 1) *
              (A : ℝ) ^ (-2 * rho.1.re)) :=
  pairedEtaSignedCompletedMomentOriginalMeanAbsolute_le_quadratic rho (by omega) (by omega) hD hDA hDL

end

end RiemannGaussian
