import RiemannGaussian.RiemannXiHyperbolicDefectHeight

/-!
# Spectral height as critical-line displacement

The extended upper spectral height mass is rewritten here in the original
zeta coordinate.  Functional-equation symmetry preserves analytic
multiplicity and pairs positive and negative spectral heights.  Consequently
twice the upper height mass is exactly the full multiplicity-counted absolute
horizontal displacement of nontrivial zeta zeros from `Re(s) = 1/2`.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The multiplicity-counted absolute spectral height of one distinct
nontrivial zeta zero. -/
def zetaAbsoluteSpectralHeightSummand (rho : NontrivialZetaZero) : ℝ :=
  (analyticZetaZeroMultiplicity rho : ℝ) *
    |(zetaSpectralCoordinate rho.1).im|

/-- In the original zeta coordinate, absolute spectral height is exactly
absolute horizontal displacement from the critical line. -/
theorem zetaAbsoluteSpectralHeightSummand_eq_criticalLineDeviation
    (rho : NontrivialZetaZero) :
    zetaAbsoluteSpectralHeightSummand rho =
      (analyticZetaZeroMultiplicity rho : ℝ) * |rho.1.re - 1 / 2| := by
  unfold zetaAbsoluteSpectralHeightSummand
  rw [zetaSpectralCoordinate_im]
  congr 1
  rw [abs_sub_comm]

/-- The full extended multiplicity-counted absolute displacement from the
critical line. -/
def riemannXiAbsoluteCriticalLineDeviationMass : ℝ≥0∞ :=
  ∑' rho : NontrivialZetaZero,
    ENNReal.ofReal (zetaAbsoluteSpectralHeightSummand rho)

/-- Literal original-coordinate form of the full deviation mass. -/
theorem riemannXiAbsoluteCriticalLineDeviationMass_eq_tsum :
    riemannXiAbsoluteCriticalLineDeviationMass =
      ∑' rho : NontrivialZetaZero,
        ENNReal.ofReal
          ((analyticZetaZeroMultiplicity rho : ℝ) *
            |rho.1.re - 1 / 2|) := by
  unfold riemannXiAbsoluteCriticalLineDeviationMass
  apply tsum_congr
  intro rho
  rw [zetaAbsoluteSpectralHeightSummand_eq_criticalLineDeviation]

/-- One zero and its critical-line reflection split absolute spectral height
into the two upper-height positive parts. -/
theorem upperHeight_add_conjugatePartner_eq_absoluteSpectralHeight
    (rho : NontrivialZetaZero) :
    zetaUpperSpectralHeightSummand rho +
        zetaUpperSpectralHeightSummand
          (NontrivialZetaZero.conjugatePartner rho) =
      zetaAbsoluteSpectralHeightSummand rho := by
  let y : ℝ := (zetaSpectralCoordinate rho.1).im
  have hpartnerIm :
      (zetaSpectralCoordinate
        (NontrivialZetaZero.conjugatePartner rho).1).im = -y := by
    dsimp [y]
    rw [zetaSpectralCoordinate_one_sub_conj]
    simp
  by_cases hy : 0 < y
  · have hnpartner : ¬0 <
        (zetaSpectralCoordinate
          (NontrivialZetaZero.conjugatePartner rho).1).im := by
      rw [hpartnerIm]
      linarith
    rw [zetaUpperSpectralHeightSummand, if_pos hy,
      zetaUpperSpectralHeightSummand, if_neg hnpartner, add_zero]
    unfold zetaAbsoluteSpectralHeightSummand
    rw [show (zetaSpectralCoordinate rho.1).im = y by rfl,
      abs_of_pos hy]
  · by_cases hyzero : y = 0
    · have hbaseZero :
          (zetaSpectralCoordinate rho.1).im = 0 := hyzero
      have hpartnerZero :
          (zetaSpectralCoordinate
            (NontrivialZetaZero.conjugatePartner rho).1).im = 0 := by
        rw [hpartnerIm, hyzero, neg_zero]
      rw [zetaUpperSpectralHeightSummand,
        if_neg (by linarith : ¬0 < (zetaSpectralCoordinate rho.1).im),
        zetaUpperSpectralHeightSummand,
        if_neg (by linarith : ¬0 <
          (zetaSpectralCoordinate
            (NontrivialZetaZero.conjugatePartner rho).1).im)]
      rw [zero_add, zetaAbsoluteSpectralHeightSummand,
        hbaseZero, abs_zero, mul_zero]
    · have hyneg : y < 0 := lt_of_le_of_ne (not_lt.mp hy) hyzero
      have hpartnerPos : 0 <
          (zetaSpectralCoordinate
            (NontrivialZetaZero.conjugatePartner rho).1).im := by
        rw [hpartnerIm]
        linarith
      rw [zetaUpperSpectralHeightSummand, if_neg hy,
        zetaUpperSpectralHeightSummand, if_pos hpartnerPos,
        analyticZetaZeroMultiplicity_conjugatePartner, zero_add,
        hpartnerIm]
      unfold zetaAbsoluteSpectralHeightSummand
      rw [show (zetaSpectralCoordinate rho.1).im = y by rfl,
        abs_of_neg hyneg]

/-- The full absolute critical-line displacement is exactly twice the upper
spectral height mass, with both sides allowed to be infinite. -/
theorem riemannXiAbsoluteCriticalLineDeviationMass_eq_two_mul_upperHeightMass :
    riemannXiAbsoluteCriticalLineDeviationMass =
      2 * riemannXiUpperSpectralHeightMass := by
  unfold riemannXiAbsoluteCriticalLineDeviationMass
    riemannXiUpperSpectralHeightMass
  calc
    (∑' rho : NontrivialZetaZero,
        ENNReal.ofReal (zetaAbsoluteSpectralHeightSummand rho)) =
        ∑' rho : NontrivialZetaZero,
          (ENNReal.ofReal (zetaUpperSpectralHeightSummand rho) +
            ENNReal.ofReal
              (zetaUpperSpectralHeightSummand
                (NontrivialZetaZero.conjugatePartner rho))) := by
      apply tsum_congr
      intro rho
      rw [← ENNReal.ofReal_add
        (zetaUpperSpectralHeightSummand_nonneg rho)
        (zetaUpperSpectralHeightSummand_nonneg
          (NontrivialZetaZero.conjugatePartner rho)),
        upperHeight_add_conjugatePartner_eq_absoluteSpectralHeight]
    _ = (∑' rho : NontrivialZetaZero,
          ENNReal.ofReal (zetaUpperSpectralHeightSummand rho)) +
        ∑' rho : NontrivialZetaZero,
          ENNReal.ofReal
            (zetaUpperSpectralHeightSummand
              (NontrivialZetaZero.conjugatePartner rho)) :=
      ENNReal.tsum_add
    _ = (∑' rho : NontrivialZetaZero,
          ENNReal.ofReal (zetaUpperSpectralHeightSummand rho)) +
        ∑' rho : NontrivialZetaZero,
          ENNReal.ofReal (zetaUpperSpectralHeightSummand rho) := by
      congr 1
      simpa only [NontrivialZetaZero.conjugatePartnerEquiv_apply] using
        (NontrivialZetaZero.conjugatePartnerEquiv.tsum_eq
          (fun rho : NontrivialZetaZero ↦
            ENNReal.ofReal (zetaUpperSpectralHeightSummand rho)))
    _ = 2 * ∑' rho : NontrivialZetaZero,
          ENNReal.ofReal (zetaUpperSpectralHeightSummand rho) := by
      ring

/-- Vanishing of the full absolute critical-line displacement is exactly RH.
-/
theorem riemannXiAbsoluteCriticalLineDeviationMass_eq_zero_iff_riemannHypothesis :
    riemannXiAbsoluteCriticalLineDeviationMass = 0 ↔
      RiemannHypothesis := by
  rw [riemannXiAbsoluteCriticalLineDeviationMass_eq_two_mul_upperHeightMass]
  constructor
  · intro hzero
    have hupper : riemannXiUpperSpectralHeightMass = 0 := by
      by_contra hne
      have htwo : (2 : ℝ≥0∞) ≠ 0 := by norm_num
      exact (mul_ne_zero htwo hne) hzero
    exact
      riemannXiUpperSpectralHeightMass_eq_zero_iff_riemannHypothesis.mp hupper
  · intro hRH
    rw [(riemannXiUpperSpectralHeightMass_eq_zero_iff_riemannHypothesis.mpr
      hRH), mul_zero]

end

end RiemannGaussian
