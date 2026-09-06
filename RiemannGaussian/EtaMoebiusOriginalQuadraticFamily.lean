import RiemannGaussian.EtaMoebiusQuadraticFamily
import RiemannGaussian.EtaMoebiusOriginalSignedFamily

/-!
# Quadratic-range bounds for the original completed signed family

The finite Fourier estimate transfers through the already proved exact
physical normalization to the unmodified completed Möbius terms. Both
reflected completion channels retain their complementary physical decay
rates. This enlarges the proved forward divisor range; the original
inverse-weighted current and its uniform weighted bound remain separate.
-/

open Complex
open scoped Classical ComplexConjugate

namespace RiemannGaussian

noncomputable section

/-- The explicit original-family constant in the quadratic divisor range. -/
def pairedEtaCompletedMoebiusOriginalQuadraticConstant (rho : NontrivialZetaZero) : ℝ :=
  2 * pairedEtaCompletedMoebiusQuadraticFamilyConstant rho +
    2 * pairedEtaCompletedMoebiusPhysicalErrorConstant rho ^ 2

/-- The original quadratic-range constant is nonnegative. -/
theorem pairedEtaCompletedMoebiusOriginalQuadraticConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCompletedMoebiusOriginalQuadraticConstant rho := by
  have h := pairedEtaCompletedMoebiusQuadraticFamilyConstant_nonneg rho
  unfold pairedEtaCompletedMoebiusOriginalQuadraticConstant
  positivity

/-- The original family with its common physical power has linear
logarithmic mean square in the quadratic divisor range. -/
theorem pairedEtaCompletedMoebiusPhysicalMeanSquare_le_quadratic
    (rho : NontrivialZetaZero) {A L D : ℕ} (hD : 1 ≤ D)
    (hDA : D ^ 2 ≤ A) (hDL : D ^ 2 ≤ L) :
    pairedEtaCompletedMoebiusPhysicalMeanSquare rho A L D ≤
      pairedEtaCompletedMoebiusOriginalQuadraticConstant rho * D * (1 + Real.log D) := by
  have hA : 1 ≤ A := (pow_pos hD 2).trans_le hDA
  have hL : 0 < L := (pow_pos hD 2).trans_le hDL
  have hDle : D ≤ A := (Nat.le_self_pow (by decide : 2 ≠ 0) D).trans hDA
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlog : 1 ≤ 1 + Real.log D := by linarith [Real.log_nonneg hDR]
  have hcost : 1 ≤ (D : ℝ) * (1 + Real.log D) := by nlinarith
  have he := mul_le_mul_of_nonneg_left
    ((divisor_fourth_div_cutoff_sq_le_one hA hDA).trans hcost)
    (by positivity : 0 ≤ 2 * pairedEtaCompletedMoebiusPhysicalErrorConstant rho ^ 2)
  have hm := mul_le_mul_of_nonneg_left
    (pairedEtaCompletedMoebiusFamilyMeanSquare_le_quadratic rho hD hDA hDL)
    (by norm_num : (0 : ℝ) ≤ 2)
  apply (pairedEtaCompletedMoebiusPhysicalMeanSquare_le_endpoint rho hA hL hDle).trans
  unfold pairedEtaCompletedMoebiusOriginalQuadraticConstant
  simp only [← mul_div_assoc] at he
  nlinarith

/-- The unmodified completed Möbius terms have their original physical
decay throughout the quadratic divisor range, with no zero-location or
simplicity premise. -/
theorem pairedEtaCompletedMoebiusOriginalMeanSquare_le_quadratic
    (rho : NontrivialZetaZero) {A L D : ℕ} (hD : 1 ≤ D)
    (hDA : D ^ 2 ≤ A) (hDL : D ^ 2 ≤ L) :
    pairedEtaCompletedMoebiusOriginalMeanSquare rho A L D ≤
      pairedEtaCompletedMoebiusOriginalQuadraticConstant rho * D * (1 + Real.log D) *
        (A : ℝ) ^ (-2 * rho.1.re) := by
  have hA : 1 ≤ A := (pow_pos hD 2).trans_le hDA
  apply (pairedEtaCompletedMoebiusOriginalMeanSquare_le_physical rho hA L D).trans
  have h := mul_le_mul_of_nonneg_left
    (pairedEtaCompletedMoebiusPhysicalMeanSquare_le_quadratic rho hD hDA hDL)
    (Real.rpow_nonneg (Nat.cast_nonneg A) (-2 * rho.1.re))
  convert h using 1
  ring

/-- Both original signed completion channels obey the enlarged
quadratic-range first absolute average bound, retaining their exact
complementary decay exponents and physical cutoff. -/
theorem pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute_le_quadratic
    (rho : NontrivialZetaZero) {A L D : ℕ} (hD : 1 ≤ D)
    (hDA : D ^ 2 ≤ A) (hDL : D ^ 2 ≤ L) :
    pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute rho A L D ≤
      (D : ℝ) * (1 + Real.log D) *
        (pairedEtaCompletedMoebiusOriginalQuadraticConstant (NontrivialZetaZero.conjugatePartner rho) *
            (A : ℝ) ^ (-2 * (1 - rho.1.re)) +
          pairedEtaCompletedMoebiusOriginalQuadraticConstant rho * (A : ℝ) ^ (-2 * rho.1.re)) := by
  apply (pairedEtaSignedCompletedMoebiusOriginalMeanAbsolute_le_channels rho A L D).trans
  have h := add_le_add
    (pairedEtaCompletedMoebiusOriginalMeanSquare_le_quadratic
      (NontrivialZetaZero.conjugatePartner rho) hD hDA hDL)
    (pairedEtaCompletedMoebiusOriginalMeanSquare_le_quadratic rho hD hDA hDL)
  simp only [NontrivialZetaZero.conjugatePartner_coe, Complex.sub_re, Complex.one_re, Complex.conj_re] at h
  convert h using 1
  ring

end

end RiemannGaussian
