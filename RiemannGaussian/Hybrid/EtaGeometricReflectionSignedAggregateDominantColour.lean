import RiemannGaussian.Hybrid.EtaGeometricReflectionSignedAggregate

/-!
# Dominant-colour asymptotics of the signed eta aggregate

The exact signed reserve retains four reflected/original colour terms, but
the moving completion coefficients have different exponential scales away
from the critical line.  This module determines that information flow
exactly for every upper-window representative.

The reflected-partner/original coefficient ratio is a fixed nonzero constant
times a geometric base of norm `q^(2*Re rho-1) < 1`, and hence tends to zero.
After dividing each upper coefficient vector by its original-colour entry,
the vector converges to the original-colour basis vector.  The complete
four-colour metric contraction factors exactly into the two original
coefficients times an original--original matrix entry plus a complex
remainder.  That remainder tends to zero uniformly over the complete finite
upper window at every fixed block length.

Thus the sixteen-interaction carrier is exact at finite cutoff, but its
natural late-start normalization asymptotically selects one colour.  This is
not a bound on the reserve and proves no zero proportion.  It identifies the
next design constraint rigorously: exploit the signed carrier at finite
start, or introduce an exact colour balancing that prevents this second
information collapse.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Geometric base governing the reflected-partner/original completion-
coefficient ratio. -/
def pairedEtaGeometricUpperPartnerToOriginalRatioBase
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T)) : ℂ :=
  ((q : ℂ) ^ rho.1.val) /
    ((q : ℂ) ^ (NontrivialZetaZero.conjugatePartner rho.1).val)

/-- The ratio base has exact norm `q^(2*Re rho-1)`. -/
theorem norm_pairedEtaGeometricUpperPartnerToOriginalRatioBase
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) :
    ‖pairedEtaGeometricUpperPartnerToOriginalRatioBase q rho‖ =
      (q : ℝ) ^ (2 * rho.1.val.re - 1) := by
  unfold pairedEtaGeometricUpperPartnerToOriginalRatioBase
  rw [norm_div]
  change
    ‖(((q : ℝ) : ℂ) ^ rho.1.val)‖ /
      ‖(((q : ℝ) : ℂ) ^
        (NontrivialZetaZero.conjugatePartner rho.1).val)‖ = _
  rw [
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hq.le),
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hq.le)]
  rw [← Real.rpow_sub (by exact_mod_cast (show 0 < q by omega))]
  congr 1
  simp [NontrivialZetaZero.conjugatePartner_coe]
  ring

/-- Every upper-window ratio base lies strictly inside the unit disk. -/
theorem norm_pairedEtaGeometricUpperPartnerToOriginalRatioBase_lt_one
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) :
    ‖pairedEtaGeometricUpperPartnerToOriginalRatioBase q rho‖ < 1 := by
  rw [norm_pairedEtaGeometricUpperPartnerToOriginalRatioBase hq]
  apply Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq)
  have hupper := (mem_spectralUpperZetaZeroWindow.mp rho.2).2
  rw [zetaSpectralCoordinate_im] at hupper
  linarith

/-- The cutoff-independent nonzero factor in a completed-prefix
coefficient. -/
def pairedEtaGeometricCompletedPrefixLeadingCoefficient
    (rho : NontrivialZetaZero) : ℂ :=
  pairedEtaTopPrefixFiniteCompletionWeight rho *
    pairedEtaLowerMomentGeometricLimit rho

/-- A completed-prefix coefficient is its leading factor times one inverse
geometric power. -/
theorem pairedEtaGeometricCompletedPrefixCoefficient_eq_leading_mul_inv_pow
    (q : ℕ) (rho : NontrivialZetaZero) (n : ℕ) :
    pairedEtaGeometricCompletedPrefixCoefficient q rho n =
      pairedEtaGeometricCompletedPrefixLeadingCoefficient rho *
        ((((q : ℂ) ^ rho.val) ^ n)⁻¹) := by
  rfl

/-- Exact moving reflected-partner/original coefficient ratio. -/
def pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) : ℂ :=
  pairedEtaGeometricUpperCompletionCoefficientVector q rho n 0 /
    pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1

/-- The moving coefficient ratio is a fixed leading ratio times a power of
the strict-contraction base. -/
theorem pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio_eq
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio q rho n =
      (pairedEtaGeometricCompletedPrefixLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho.1) /
        pairedEtaGeometricCompletedPrefixLeadingCoefficient rho.1) *
      pairedEtaGeometricUpperPartnerToOriginalRatioBase q rho ^ n := by
  unfold pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio
    pairedEtaGeometricUpperCompletionCoefficientVector
    pairedEtaGeometricUpperReflectionPairZero
  change
    pairedEtaGeometricCompletedPrefixCoefficient q
          (NontrivialZetaZero.conjugatePartner rho.1) n /
        pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n = _
  rw [pairedEtaGeometricCompletedPrefixCoefficient_eq_leading_mul_inv_pow,
    pairedEtaGeometricCompletedPrefixCoefficient_eq_leading_mul_inv_pow]
  unfold pairedEtaGeometricUpperPartnerToOriginalRatioBase
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hrho : (q : ℂ) ^ rho.1.val ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hq0)
  have hpartner :
      (q : ℂ) ^ (NontrivialZetaZero.conjugatePartner rho.1).val ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hq0)
  have hleadRho :
      pairedEtaGeometricCompletedPrefixLeadingCoefficient rho.1 ≠ 0 := by
    unfold pairedEtaGeometricCompletedPrefixLeadingCoefficient
    exact mul_ne_zero
      (by
        unfold pairedEtaTopPrefixFiniteCompletionWeight
        exact mul_ne_zero
          (pairedEtaXiCompletionFactor_ne_zero
            (NontrivialZetaZero.zero_lt_re rho.1)
            (NontrivialZetaZero.re_lt_one rho.1))
          (NontrivialZetaZero.coe_ne_zero rho.1))
      (pairedEtaLowerMomentGeometricLimit_ne_zero rho.1)
  rw [div_pow]
  field_simp [hleadRho, hrho, hpartner]

/-- The reflected-partner/original coefficient ratio tends to zero. -/
theorem tendsto_pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) :
    Tendsto
      (pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio q rho)
      atTop (nhds 0) := by
  rw [show pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio q rho =
      fun n ↦
        (pairedEtaGeometricCompletedPrefixLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho.1) /
          pairedEtaGeometricCompletedPrefixLeadingCoefficient rho.1) *
        pairedEtaGeometricUpperPartnerToOriginalRatioBase q rho ^ n by
    funext n
    exact pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio_eq
      hq rho n]
  have hlimit := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    (norm_pairedEtaGeometricUpperPartnerToOriginalRatioBase_lt_one
      hq rho)).const_mul
        (pairedEtaGeometricCompletedPrefixLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho.1) /
          pairedEtaGeometricCompletedPrefixLeadingCoefficient rho.1)
  simpa using hlimit

/-- The two completion coefficients divided by the nonzero original-colour
coefficient. -/
def pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) : Fin 2 → ℂ := fun i ↦
  pairedEtaGeometricUpperCompletionCoefficientVector q rho n i /
    pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1

/-- Basis vector selecting the original upper-window colour. -/
def pairedEtaGeometricUpperOriginalColourBasis : Fin 2 → ℂ :=
  ![0, 1]

/-- Original normalization sends the two-colour coefficient vector to the
original-colour basis vector. -/
theorem tendsto_pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) :
    Tendsto
      (pairedEtaGeometricUpperOriginalNormalizedCoefficientVector q rho)
      atTop (nhds pairedEtaGeometricUpperOriginalColourBasis) := by
  rw [tendsto_pi_nhds]
  intro i
  fin_cases i
  · change Tendsto
      (pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio q rho)
      atTop (nhds 0)
    exact tendsto_pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio
      hq rho
  · have hden : ∀ n,
        pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1 ≠ 0 := by
      intro n
      unfold pairedEtaGeometricUpperCompletionCoefficientVector
        pairedEtaGeometricUpperReflectionPairZero
      exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq.le rho.1 n
    have hone :
        (fun n ↦ pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
            q rho n 1) = fun _n ↦ (1 : ℂ) := by
      funext n
      unfold pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
      exact div_self (hden n)
    change Tendsto
      (fun n ↦ pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
        q rho n 1) atTop (nhds 1)
    rw [hone]
    exact tendsto_const_nhds

/-- Four-colour metric contraction after dividing both coefficient vectors by
their original entries. -/
def pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    star (pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
        q zeta n i) *
      pairedEtaGeometricUpperOriginalNormalizedCoefficientVector q rho n j *
        pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
          q zeta rho n M i j

/-- One signed colour contribution after original-coefficient
normalization. -/
def pairedEtaGeometricCriticalUpperOriginalNormalizedColourContribution
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) (i j : Fin 2) : ℝ :=
  (star (pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
        q zeta n i) *
      pairedEtaGeometricUpperOriginalNormalizedCoefficientVector q rho n j *
        pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
          q zeta rho n M i j).re

/-- All sixteen signed ordered products after original-coefficient
normalization. -/
def pairedEtaGeometricCriticalUpperOriginalNormalizedOrderedColourInteraction
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
    pairedEtaGeometricCriticalUpperOriginalNormalizedColourContribution
        q zeta rho n M i j *
      pairedEtaGeometricCriticalUpperOriginalNormalizedColourContribution
        q zeta rho n M k l

/-- The normalized ordered interaction is exactly the real square of the
normalized four-colour contraction. -/
theorem pairedEtaGeometricCriticalUpperOriginalNormalizedOrderedColourInteraction_eq_re_sq
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricCriticalUpperOriginalNormalizedOrderedColourInteraction
        q zeta rho n M =
      (pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
        q zeta rho n M).re ^ 2 := by
  have hre :
      (pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
          q zeta rho n M).re =
        ∑ i : Fin 2, ∑ j : Fin 2,
          pairedEtaGeometricCriticalUpperOriginalNormalizedColourContribution
            q zeta rho n M i j := by
    unfold pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
      pairedEtaGeometricCriticalUpperOriginalNormalizedColourContribution
    simp
    ring
  rw [hre]
  unfold
    pairedEtaGeometricCriticalUpperOriginalNormalizedOrderedColourInteraction
  simp only [Fin.sum_univ_two]
  ring

/-- Exact factorization of the raw contraction into its two original
coefficients and the normalized four-colour contraction. -/
theorem pairedEtaGeometricCriticalUpperMetricCoefficientContraction_eq_original_mul_normalized
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricCriticalUpperMetricCoefficientContraction
        q zeta rho n M =
      star (pairedEtaGeometricUpperCompletionCoefficientVector q zeta n 1) *
        pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1 *
          pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
            q zeta rho n M := by
  have hzeta :
      pairedEtaGeometricUpperCompletionCoefficientVector q zeta n 1 ≠ 0 := by
    unfold pairedEtaGeometricUpperCompletionCoefficientVector
      pairedEtaGeometricUpperReflectionPairZero
    exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq.le zeta.1 n
  have hrho :
      pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1 ≠ 0 := by
    unfold pairedEtaGeometricUpperCompletionCoefficientVector
      pairedEtaGeometricUpperReflectionPairZero
    exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq.le rho.1 n
  have hzetaFactor (i : Fin 2) :
      pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i =
        pairedEtaGeometricUpperCompletionCoefficientVector q zeta n 1 *
          pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
            q zeta n i := by
    unfold pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
    field_simp
  have hzetaStarFactor (i : Fin 2) :
      star (pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i) =
        star (pairedEtaGeometricUpperCompletionCoefficientVector q zeta n 1) *
          star (pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
            q zeta n i) := by
    rw [hzetaFactor i, star_mul]
    ring
  have hrhoFactor (j : Fin 2) :
      pairedEtaGeometricUpperCompletionCoefficientVector q rho n j =
        pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1 *
          pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
            q rho n j := by
    unfold pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
    field_simp
  have hzetaNormOne :
      pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
        q zeta n 1 = 1 := by
    unfold pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
    exact div_self hzeta
  have hrhoNormOne :
      pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
        q rho n 1 = 1 := by
    unfold pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
    exact div_self hrho
  unfold pairedEtaGeometricCriticalUpperMetricCoefficientContraction
    pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
  simp only [Fin.sum_univ_two]
  rw [hzetaStarFactor 0, hzetaStarFactor 1,
    hrhoFactor 0, hrhoFactor 1]
  simp [hzetaNormOne, hrhoNormOne]
  ring

/-- The normalized four-colour contraction converges to the single
original--original limiting metric-mode entry. -/
theorem tendsto_pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T)) (M : ℕ) :
    Tendsto
      (fun n : ℕ ↦
        pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
          q zeta rho n M)
      atTop
      (nhds (pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
        q zeta rho M 1 1)) := by
  have hzeta :=
    tendsto_pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
      hq zeta
  have hrho :=
    tendsto_pairedEtaGeometricUpperOriginalNormalizedCoefficientVector
      hq rho
  have hmatrix :=
    tendsto_pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
      hqOdd hq zeta rho M
  unfold pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin 2)) fun i _hi ↦
    tendsto_finsetSum (Finset.univ : Finset (Fin 2)) fun j _hj ↦
      ((tendsto_pi_nhds.mp hzeta i).star.mul
        (tendsto_pi_nhds.mp hrho j)).mul
          (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hmatrix i) j)
  convert hsum using 1
  simp [pairedEtaGeometricUpperOriginalColourBasis]

/-- The full normalized sixteen-interaction sum converges to the square of
the single original--original limiting entry. -/
theorem tendsto_pairedEtaGeometricCriticalUpperOriginalNormalizedOrderedColourInteraction
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T)) (M : ℕ) :
    Tendsto
      (fun n : ℕ ↦
        pairedEtaGeometricCriticalUpperOriginalNormalizedOrderedColourInteraction
          q zeta rho n M)
      atTop
      (nhds ((pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
        q zeta rho M 1 1).re ^ 2)) := by
  rw [show
    (fun n : ℕ ↦
      pairedEtaGeometricCriticalUpperOriginalNormalizedOrderedColourInteraction
        q zeta rho n M) =
      fun n ↦
        (pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
          q zeta rho n M).re ^ 2 by
    funext n
    exact
      pairedEtaGeometricCriticalUpperOriginalNormalizedOrderedColourInteraction_eq_re_sq
        q zeta rho n M]
  have hre := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
      hqOdd hq zeta rho M)
  exact hre.pow 2

/-- Dividing the raw contraction by the two original coefficients exposes the
same single-colour limit. -/
theorem tendsto_pairedEtaGeometricCriticalUpperMetricCoefficientContraction_div_original
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T)) (M : ℕ) :
    Tendsto
      (fun n : ℕ ↦
        pairedEtaGeometricCriticalUpperMetricCoefficientContraction
            q zeta rho n M /
          (star (pairedEtaGeometricUpperCompletionCoefficientVector
              q zeta n 1) *
            pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1))
      atTop
      (nhds (pairedEtaGeometricCriticalUpperMetricModeCorrelationMatrix
        q zeta rho M 1 1)) := by
  apply
    (tendsto_pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
      hqOdd hq zeta rho M).congr'
  filter_upwards with n
  rw [pairedEtaGeometricCriticalUpperMetricCoefficientContraction_eq_original_mul_normalized
    hq zeta rho n M]
  have hzeta :
      pairedEtaGeometricUpperCompletionCoefficientVector q zeta n 1 ≠ 0 := by
    unfold pairedEtaGeometricUpperCompletionCoefficientVector
      pairedEtaGeometricUpperReflectionPairZero
    exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq.le zeta.1 n
  have hrho :
      pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1 ≠ 0 := by
    unfold pairedEtaGeometricUpperCompletionCoefficientVector
      pairedEtaGeometricUpperReflectionPairZero
    exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq.le rho.1 n
  field_simp [hzeta, hrho, star_ne_zero.mpr hzeta]

/-- Complex remainder after removing the literal original--original metric
entry from the normalized four-colour contraction. -/
def pairedEtaGeometricCriticalUpperOriginalDominantColourRemainder
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℂ :=
  pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
      q zeta rho n M -
    pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
      q zeta rho n M 1 1

/-- The nondominant-colour complex remainder tends to zero. -/
theorem tendsto_pairedEtaGeometricCriticalUpperOriginalDominantColourRemainder
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T)) (M : ℕ) :
    Tendsto
      (fun n : ℕ ↦
        pairedEtaGeometricCriticalUpperOriginalDominantColourRemainder
          q zeta rho n M)
      atTop (nhds 0) := by
  have hcontraction :=
    tendsto_pairedEtaGeometricCriticalUpperOriginalNormalizedMetricContraction
      hqOdd hq zeta rho M
  have hmatrix :=
    tendsto_pi_nhds.mp
      (tendsto_pi_nhds.mp
        (tendsto_pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
          hqOdd hq zeta rho M) 1) 1
  unfold pairedEtaGeometricCriticalUpperOriginalDominantColourRemainder
  simpa using hcontraction.sub hmatrix

/-- Exact dominant-colour-plus-remainder factorization of every raw metric
contraction. -/
theorem pairedEtaGeometricCriticalUpperMetricCoefficientContraction_eq_original_mul_dominant_add_remainder
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricCriticalUpperMetricCoefficientContraction
        q zeta rho n M =
      star (pairedEtaGeometricUpperCompletionCoefficientVector q zeta n 1) *
        pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1 *
          (pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
              q zeta rho n M 1 1 +
            pairedEtaGeometricCriticalUpperOriginalDominantColourRemainder
              q zeta rho n M) := by
  rw [pairedEtaGeometricCriticalUpperMetricCoefficientContraction_eq_original_mul_normalized
    hq zeta rho n M]
  unfold pairedEtaGeometricCriticalUpperOriginalDominantColourRemainder
  ring

/-- At fixed block length, every nondominant-colour remainder in the complete
finite upper window is eventually smaller than any positive tolerance. -/
theorem eventually_forall_pairedEtaGeometricCriticalUpperOriginalDominantColourRemainder_norm_lt
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∀ zeta rho : ↑(spectralUpperZetaZeroWindow T),
        ‖pairedEtaGeometricCriticalUpperOriginalDominantColourRemainder
          q zeta rho n M‖ < ε := by
  apply Filter.eventually_all.mpr
  intro zeta
  apply Filter.eventually_all.mpr
  intro rho
  have hlimit :=
    (tendsto_pairedEtaGeometricCriticalUpperOriginalDominantColourRemainder
      hqOdd hq zeta rho M).norm
  simpa using (tendsto_order.1 hlimit).2 ε (by simpa using hε)

end
end RiemannGaussian
