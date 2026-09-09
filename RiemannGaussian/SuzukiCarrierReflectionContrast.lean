/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierContourStrip

/-!
# The reflection difference as a source-preserving contour test

The coefficients of the two-node contrast are fixed by the reflection
involution. The exact mixed form cancels the leading resolvent term,
giving a fourth-order denominator away from the two nodes. Its genuine
real Gram is nonnegative, while an enclosed reflected off-axis source
has the negative sign needed for the contradiction test.
-/

open Complex Filter MeasureTheory Set
namespace RiemannGaussian
noncomputable section

/-- The full two-node quadratic for the canonical coefficients `1,-1`.
Both mixed entries remain present; the second node is the exact partner. -/
def suzukiXiReflectionPairQuadratic (rho : NontrivialZetaZero)
    (K : NontrivialZetaZero → NontrivialZetaZero → ℂ) : ℂ :=
  K rho rho - K rho rho.conjugatePartner - K rho.conjugatePartner rho +
    K rho.conjugatePartner rho.conjugatePartner

/-- The reflection difference of the two original Cauchy resolvents. -/
def suzukiXiReflectionCauchyDifference (rho : NontrivialZetaZero) (z : ℂ) : ℂ :=
  (z - zetaSpectralCoordinate rho.1)⁻¹ -
    (z - starRingEnd ℂ (zetaSpectralCoordinate rho.1))⁻¹

/-- The actual first carrier tested against its reflection contrast. -/
def suzukiXiReflectionCarrierChannel (rho : NontrivialZetaZero) (z : ℂ) : ℂ :=
  suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiMixedCarrierChannel a b z)

/-- Exact resolvent cancellation in the original mixed carrier, including
its totalized values at the nodes. No modulus is taken in this identity. -/
theorem suzukiXiReflectionCarrierChannel_eq_neg_square
    (rho : NontrivialZetaZero) (z : ℂ) :
    suzukiXiReflectionCarrierChannel rho z =
      -suzukiXiZeroCarrier z * suzukiXiReflectionCauchyDifference rho z ^ 2 := by
  simp only [suzukiXiReflectionCarrierChannel, suzukiXiReflectionPairQuadratic,
    suzukiXiMixedCarrierChannel, suzukiXiReflectionCauchyDifference,
    NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_conj, div_eq_mul_inv, mul_inv]
  ring

/-- Away from the two nodes the full reflection contrast has a quartic
denominator and the exact squared vertical-gap numerator. -/
theorem suzukiXiReflectionCarrierChannel_eq_quartic
    (rho : NontrivialZetaZero) {z : ℂ}
    (ha : z ≠ zetaSpectralCoordinate rho.1)
    (hb : z ≠ starRingEnd ℂ (zetaSpectralCoordinate rho.1)) :
    suzukiXiReflectionCarrierChannel rho z =
      4 * ((zetaSpectralCoordinate rho.1).im : ℂ) ^ 2 * suzukiXiZeroCarrier z /
        ((z - zetaSpectralCoordinate rho.1) ^ 2 *
          (z - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) ^ 2) := by
  let a := zetaSpectralCoordinate rho.1
  have hd : a - starRingEnd ℂ a = 2 * I * (a.im : ℂ) := by
    apply Complex.ext
    · simp
    · simp
      ring
  have he : suzukiXiReflectionCauchyDifference rho z =
      (a - starRingEnd ℂ a) / ((z - a) * (z - starRingEnd ℂ a)) := by
    unfold suzukiXiReflectionCauchyDifference
    change (z - a)⁻¹ - (z - starRingEnd ℂ a)⁻¹ = _
    have hza : z - a ≠ 0 := sub_ne_zero.mpr ha
    have hzb : z - starRingEnd ℂ a ≠ 0 := sub_ne_zero.mpr hb
    field_simp [hza, hzb]
    ring
  rw [suzukiXiReflectionCarrierChannel_eq_neg_square, he, hd]
  change -suzukiXiZeroCarrier z * (2 * I * (a.im : ℂ) / _) ^ 2 = _
  simp only [div_pow, mul_pow, I_sq]
  ring

/-- The reflection quadratic commutes with an interval integral when
all original mixed entries are integrable on that interval. -/
theorem suzukiXiReflectionPairQuadratic_intervalIntegral
    (rho : NontrivialZetaZero) (K : NontrivialZetaZero → NontrivialZetaZero → ℝ → ℂ)
    (l r : ℝ) (hK : ∀ a b, IntervalIntegrable (K a b) volume l r) :
    suzukiXiReflectionPairQuadratic rho (fun a b => ∫ x : ℝ in l..r, K a b x) =
      ∫ x : ℝ in l..r, suzukiXiReflectionPairQuadratic rho (fun a b => K a b x) := by
  unfold suzukiXiReflectionPairQuadratic
  rw [intervalIntegral.integral_add (((hK _ _).sub (hK _ _)).sub (hK _ _)) (hK _ _),
    intervalIntegral.integral_sub ((hK _ _).sub (hK _ _)) (hK _ _),
    intervalIntegral.integral_sub (hK _ _) (hK _ _)]

/-- The actual reflection Gram density is a literal square of the
carrier times the resolvent difference, with all four mixed entries retained. -/
theorem suzukiXiReflectionPairQuadratic_gramIntegrand
    (rho : NontrivialZetaZero) (x : ℝ) :
    suzukiXiReflectionPairQuadratic rho (fun a b => suzukiXiBoundaryCarrierGramIntegrand a b x) =
      starRingEnd ℂ (suzukiRealAxisXiZeroCarrier x * suzukiXiReflectionCauchyDifference rho (x : ℂ)) *
        (suzukiRealAxisXiZeroCarrier x * suzukiXiReflectionCauchyDifference rho (x : ℂ)) := by
  simp only [suzukiXiReflectionPairQuadratic, suzukiXiBoundaryCarrierGramIntegrand,
    suzukiXiReflectionCauchyDifference, NontrivialZetaZero.spectralCoordinate_conjugatePartner,
    map_mul, map_sub, map_inv₀, conj_ofReal, conj_conj, div_eq_mul_inv, mul_inv]
  ring

/-- Every actual truncated reflection Gram has nonnegative real part.
No RH assumption or coefficient optimization is involved. -/
theorem suzukiXiReflectionPairQuadratic_truncatedGram_re_nonneg
    (rho : NontrivialZetaZero) {l r : ℝ} (hlr : l ≤ r) :
    0 ≤ (suzukiXiReflectionPairQuadratic rho
      (fun a b => suzukiXiTruncatedBoundaryCarrierGramKernel a b l r)).re := by
  have hK (a b : NontrivialZetaZero) :=
    (integrable_suzukiXiBoundaryCarrierGramIntegrand a b).intervalIntegrable (a := l) (b := r)
  have hint : IntervalIntegrable (fun x => suzukiXiReflectionPairQuadratic rho
      (fun a b => suzukiXiBoundaryCarrierGramIntegrand a b x)) volume l r :=
    (((hK rho rho).sub (hK rho rho.conjugatePartner)).sub (hK rho.conjugatePartner rho)).add
      (hK rho.conjugatePartner rho.conjugatePartner)
  unfold suzukiXiTruncatedBoundaryCarrierGramKernel
  rw [suzukiXiReflectionPairQuadratic_intervalIntegral rho _ l r hK]
  have hre : (∫ x : ℝ in l..r, suzukiXiReflectionPairQuadratic rho
      (fun a b => suzukiXiBoundaryCarrierGramIntegrand a b x)).re =
      ∫ x : ℝ in l..r, (suzukiXiReflectionPairQuadratic rho
        (fun a b => suzukiXiBoundaryCarrierGramIntegrand a b x)).re := by
    exact (intervalIntegral.intervalIntegral_re hint).symm
  rw [hre]
  apply intervalIntegral.integral_nonneg_of_forall hlr
  intro x
  rw [suzukiXiReflectionPairQuadratic_gramIntegrand]
  simpa only [mul_re, conj_re, conj_im, sub_neg_eq_add, Complex.normSq_apply, neg_mul] using
    Complex.normSq_nonneg (suzukiRealAxisXiZeroCarrier x * suzukiXiReflectionCauchyDifference rho (x : ℂ))

/-- Conjugate transpose commutes with this real-coefficient reflection
quadratic; exchanging the off-diagonal entries is essential. -/
theorem suzukiXiReflectionPairQuadratic_conjugateTranspose
    (rho : NontrivialZetaZero) (K : NontrivialZetaZero → NontrivialZetaZero → ℂ) :
    suzukiXiReflectionPairQuadratic rho (fun a b => starRingEnd ℂ (K b a)) =
      starRingEnd ℂ (suzukiXiReflectionPairQuadratic rho K) := by
  simp only [suzukiXiReflectionPairQuadratic, map_add, map_sub]
  ring

/-- The reflection quadratic commutes with the signed Hermitian
projection, preserving the cancellation before that projection is bounded. -/
theorem suzukiXiReflectionPairQuadratic_signedProjection
    (rho : NontrivialZetaZero) (K : NontrivialZetaZero → NontrivialZetaZero → ℂ) :
    suzukiXiReflectionPairQuadratic rho (fun a b => (K a b - starRingEnd ℂ (K b a)) / (2 * I)) =
      (suzukiXiReflectionPairQuadratic rho K -
        starRingEnd ℂ (suzukiXiReflectionPairQuadratic rho K)) / (2 * I) := by
  simp only [suzukiXiReflectionPairQuadratic, map_add, map_sub]
  ring

/-- When the partner is enclosed and the original node is outside, the
reflection quadratic of the genuine xi source is exactly minus the
inverse analytic multiplicity. This fixes the source without searching weights. -/
theorem suzukiXiReflectionPairQuadratic_source_eq_neg_inv_multiplicity
    (rho : NontrivialZetaZero) (l r b u : ℝ)
    (hp : zetaSpectralCoordinate rho.conjugatePartner.1 ∈ suzukiXiCarrierPoleWindow l r b u)
    (hn : zetaSpectralCoordinate rho.1 ∉ suzukiXiCarrierPoleWindow l r b u) :
    suzukiXiReflectionPairQuadratic rho (fun a d => suzukiXiMixedContourXiSource a d l r b u) =
      -(analyticZetaZeroMultiplicity rho : ℂ)⁻¹ := by
  have hne : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ≠ zetaSpectralCoordinate rho.1 := by
    intro he
    apply hn
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner, he] using hp
  have hp' : starRingEnd ℂ (zetaSpectralCoordinate rho.1) ∈ suzukiXiCarrierPoleWindow l r b u := by
    simpa only [NontrivialZetaZero.spectralCoordinate_conjugatePartner] using hp
  simp only [suzukiXiReflectionPairQuadratic, suzukiXiMixedContourXiSource,
    NontrivialZetaZero.spectralCoordinate_conjugatePartner, conj_conj,
    analyticZetaZeroMultiplicity_conjugatePartner, hne, Ne.symm hne, hn, hp',
    true_and, false_and, and_self, if_false, if_true, sub_zero, zero_sub, add_zero]

end
end RiemannGaussian
