import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaInfiniteGaussianLaplaceGramLocalizedLargeTimeAsymptotic

/-!
# The exact reflection multiplier for the positive eta Laplace partition

The actual localized-Gram asymptotic reduces vanishing of its first
completion distortion to equality of two explicit completion weights.  This
module exposes that remaining comparison as the unit-modulus problem for one
nonvanishing analytic reflection multiplier.

The multiplier is derived from the completed eta identity; it is not an
assumed normalization.  Lean proves the corresponding complex functional
equation for the literal positive-measure Laplace partition, its conjugation
and reciprocal symmetries, and its exact Gamma/eta-factor formula.  At a
nontrivial zero, unit modulus is exactly vanishing of the actual first scaled
distortion coefficient.  Proving that unit modulus forces the critical line
remains open.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The complex amplitude whose squared norm is the existing completed
positive-Laplace weight. -/
def pairedEtaCompletedLaplaceAmplitude (s : ℂ) : ℂ :=
  pairedEtaXiCompletionFactor s * s

/-- The exact analytic multiplier relating the positive eta Laplace partition
at `s` and `1 - s`. -/
def pairedEtaLaplaceReflectionMultiplier (s : ℂ) : ℂ :=
  pairedEtaCompletedLaplaceAmplitude s /
    pairedEtaCompletedLaplaceAmplitude (1 - s)

/-- The completed Laplace amplitude never vanishes in the open critical
strip. -/
theorem pairedEtaCompletedLaplaceAmplitude_ne_zero
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaCompletedLaplaceAmplitude s ≠ 0 := by
  unfold pairedEtaCompletedLaplaceAmplitude
  exact mul_ne_zero (pairedEtaXiCompletionFactor_ne_zero hspos hslt)
    (by
      intro hs
      subst s
      norm_num at hspos)

/-- Consequently the reflection multiplier never vanishes in the open
critical strip. -/
theorem pairedEtaLaplaceReflectionMultiplier_ne_zero
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaLaplaceReflectionMultiplier s ≠ 0 := by
  have hpartnerPos : 0 < (1 - s).re := by simpa using sub_pos.mpr hslt
  have hpartnerLt : (1 - s).re < 1 := by
    simpa using sub_lt_self (1 : ℝ) hspos
  exact div_ne_zero
    (pairedEtaCompletedLaplaceAmplitude_ne_zero hspos hslt)
    (pairedEtaCompletedLaplaceAmplitude_ne_zero hpartnerPos hpartnerLt)

/-- Completed paired eta is the completion amplitude times the literal
positive-measure Laplace partition. -/
theorem pairedEtaCompletedXi_eq_amplitude_mul_laplacePartition
    {s : ℂ} (hspos : 0 < s.re) :
    pairedEtaCompletedXi s =
      pairedEtaCompletedLaplaceAmplitude s * pairedEtaLaplacePartition s := by
  unfold pairedEtaCompletedXi pairedEtaCompletedLaplaceAmplitude
  rw [pairedEtaCore_eq_mul_laplacePartition hspos]
  ring

/-- The literal positive eta Laplace partition respects complex
conjugation. -/
theorem pairedEtaLaplacePartition_conj
    {s : ℂ} (hspos : 0 < s.re) :
    pairedEtaLaplacePartition (starRingEnd ℂ s) =
      starRingEnd ℂ (pairedEtaLaplacePartition s) := by
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hspos
  have hconj0 : starRingEnd ℂ s ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hs0
  have hconjPos : 0 < (starRingEnd ℂ s).re := by simpa using hspos
  apply mul_left_cancel₀ hconj0
  calc
    starRingEnd ℂ s * pairedEtaLaplacePartition (starRingEnd ℂ s) =
        pairedEtaCore (starRingEnd ℂ s) :=
      (pairedEtaCore_eq_mul_laplacePartition hconjPos).symm
    _ = starRingEnd ℂ (pairedEtaCore s) := pairedEtaCore_conj s
    _ = starRingEnd ℂ
        (s * pairedEtaLaplacePartition s) := by
      rw [pairedEtaCore_eq_mul_laplacePartition hspos]
    _ = starRingEnd ℂ s *
        starRingEnd ℂ (pairedEtaLaplacePartition s) :=
      map_mul (starRingEnd ℂ) s (pairedEtaLaplacePartition s)

/-- The reflection multiplier gives the exact complex functional equation of
the literal positive eta Laplace partition throughout the open strip. -/
theorem pairedEtaLaplacePartition_one_sub
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaLaplacePartition (1 - s) =
      pairedEtaLaplaceReflectionMultiplier s * pairedEtaLaplacePartition s := by
  have hpartnerPos : 0 < (1 - s).re := by simpa using sub_pos.mpr hslt
  have hpartnerLt : (1 - s).re < 1 := by
    simpa using sub_lt_self (1 : ℝ) hspos
  have hpartnerAmp : pairedEtaCompletedLaplaceAmplitude (1 - s) ≠ 0 :=
    pairedEtaCompletedLaplaceAmplitude_ne_zero hpartnerPos hpartnerLt
  have hbalance :
      pairedEtaCompletedLaplaceAmplitude (1 - s) *
          pairedEtaLaplacePartition (1 - s) =
        pairedEtaCompletedLaplaceAmplitude s *
          pairedEtaLaplacePartition s := by
    rw [← pairedEtaCompletedXi_eq_amplitude_mul_laplacePartition hpartnerPos,
      ← pairedEtaCompletedXi_eq_amplitude_mul_laplacePartition hspos,
      pairedEtaCompletedXi_eq_riemannXi hpartnerPos hpartnerLt,
      pairedEtaCompletedXi_eq_riemannXi hspos hslt,
      riemannXi_one_sub]
  apply mul_left_cancel₀ hpartnerAmp
  rw [hbalance]
  unfold pairedEtaLaplaceReflectionMultiplier
  field_simp

/-- The elementary eta factor respects complex conjugation. -/
theorem pairedEtaFactor_conj (s : ℂ) :
    pairedEtaFactor (starRingEnd ℂ s) =
      starRingEnd ℂ (pairedEtaFactor s) := by
  unfold pairedEtaFactor
  rw [two_cpow_neg_conj, map_sub, map_one, map_mul, map_ofNat]

/-- The exact eta completion factor respects complex conjugation. -/
theorem pairedEtaXiCompletionFactor_conj (s : ℂ) :
    pairedEtaXiCompletionFactor (starRingEnd ℂ s) =
      starRingEnd ℂ (pairedEtaXiCompletionFactor s) := by
  unfold pairedEtaXiCompletionFactor pairedEtaXiCompletionNumerator
  rw [pairedEtaFactor_conj, Gammaℝ_conj]
  simp

/-- The completed Laplace amplitude respects complex conjugation. -/
theorem pairedEtaCompletedLaplaceAmplitude_conj (s : ℂ) :
    pairedEtaCompletedLaplaceAmplitude (starRingEnd ℂ s) =
      starRingEnd ℂ (pairedEtaCompletedLaplaceAmplitude s) := by
  unfold pairedEtaCompletedLaplaceAmplitude
  rw [pairedEtaXiCompletionFactor_conj]
  simp

/-- The squared norm of the complex amplitude is definitionally the existing
completed Laplace weight. -/
theorem normSq_pairedEtaCompletedLaplaceAmplitude (s : ℂ) :
    Complex.normSq (pairedEtaCompletedLaplaceAmplitude s) =
      pairedEtaCompletedLaplaceWeight s := by
  rfl

/-- The squared norm of the reflection multiplier is exactly the ratio of
the two complementary completion weights. -/
theorem normSq_pairedEtaLaplaceReflectionMultiplier_eq_weight_div
    (s : ℂ) :
    Complex.normSq (pairedEtaLaplaceReflectionMultiplier s) =
      pairedEtaCompletedLaplaceWeight s /
        pairedEtaCompletedLaplaceWeight (1 - starRingEnd ℂ s) := by
  unfold pairedEtaLaplaceReflectionMultiplier
  have hconj : pairedEtaCompletedLaplaceAmplitude
      (1 - starRingEnd ℂ s) =
      starRingEnd ℂ (pairedEtaCompletedLaplaceAmplitude (1 - s)) := by
    rw [show 1 - starRingEnd ℂ s = starRingEnd ℂ (1 - s) by simp,
      pairedEtaCompletedLaplaceAmplitude_conj]
  have hweight :
      pairedEtaCompletedLaplaceWeight (1 - starRingEnd ℂ s) =
        pairedEtaCompletedLaplaceWeight (1 - s) := by
    change Complex.normSq
        (pairedEtaCompletedLaplaceAmplitude (1 - starRingEnd ℂ s)) =
      Complex.normSq (pairedEtaCompletedLaplaceAmplitude (1 - s))
    rw [hconj, Complex.normSq_conj]
  rw [Complex.normSq_div,
    normSq_pairedEtaCompletedLaplaceAmplitude,
    normSq_pairedEtaCompletedLaplaceAmplitude, hweight]

/-- In the open strip, unit norm of the reflection multiplier is equivalent
to equality of the two complementary completion weights. -/
theorem normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_iff_weight_eq
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    Complex.normSq (pairedEtaLaplaceReflectionMultiplier s) = 1 ↔
      pairedEtaCompletedLaplaceWeight s =
        pairedEtaCompletedLaplaceWeight (1 - starRingEnd ℂ s) := by
  rw [normSq_pairedEtaLaplaceReflectionMultiplier_eq_weight_div s]
  have hpartnerPos : 0 < (1 - starRingEnd ℂ s).re := by
    simpa using sub_pos.mpr hslt
  have hpartnerLt : (1 - starRingEnd ℂ s).re < 1 := by
    simpa using sub_lt_self (1 : ℝ) hspos
  have hw := pairedEtaCompletedLaplaceWeight_pos hpartnerPos hpartnerLt
  constructor
  · intro h
    exact (div_eq_one_iff_eq hw.ne').mp h
  · intro h
    exact (div_eq_one_iff_eq hw.ne').mpr h

/-- The reflection multiplier is the explicit product of the spectral,
completed-Gamma, and elementary eta-factor reflection ratios. -/
theorem pairedEtaLaplaceReflectionMultiplier_eq_explicit
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaLaplaceReflectionMultiplier s =
      (s / (1 - s)) *
        (Complex.Gammaℝ s / Complex.Gammaℝ (1 - s)) *
        (pairedEtaFactor (1 - s) / pairedEtaFactor s) := by
  have hpartnerPos : 0 < (1 - s).re := by simpa using sub_pos.mpr hslt
  have hpartnerLt : (1 - s).re < 1 := by
    simpa using sub_lt_self (1 : ℝ) hspos
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    norm_num at hspos
  have h1s : 1 - s ≠ 0 := by
    intro hs
    have h1eq : (1 : ℂ) = s := sub_eq_zero.mp hs
    subst s
    norm_num at hslt
  have hfactorS : pairedEtaFactor s ≠ 0 :=
    pairedEtaFactor_ne_zero_of_re_lt_one hslt
  have hfactorPartner : pairedEtaFactor (1 - s) ≠ 0 :=
    pairedEtaFactor_ne_zero_of_re_lt_one hpartnerLt
  have hgammaPartner : Complex.Gammaℝ (1 - s) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos hpartnerPos
  unfold pairedEtaLaplaceReflectionMultiplier
    pairedEtaCompletedLaplaceAmplitude pairedEtaXiCompletionFactor
    pairedEtaXiCompletionNumerator
  field_simp [hs0, h1s, hfactorS, hfactorPartner, hgammaPartner]
  ring

/-- Reflection sends the multiplier to its reciprocal throughout the open
critical strip. -/
theorem pairedEtaLaplaceReflectionMultiplier_one_sub
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaLaplaceReflectionMultiplier (1 - s) =
      (pairedEtaLaplaceReflectionMultiplier s)⁻¹ := by
  have hpartnerPos : 0 < (1 - s).re := by simpa using sub_pos.mpr hslt
  have hpartnerLt : (1 - s).re < 1 := by
    simpa using sub_lt_self (1 : ℝ) hspos
  have hsAmp := pairedEtaCompletedLaplaceAmplitude_ne_zero hspos hslt
  have hpartnerAmp :=
    pairedEtaCompletedLaplaceAmplitude_ne_zero hpartnerPos hpartnerLt
  unfold pairedEtaLaplaceReflectionMultiplier
  rw [sub_sub_cancel]
  field_simp

/-- Conjugation sends the reflection multiplier to its complex
conjugate. -/
theorem pairedEtaLaplaceReflectionMultiplier_conj (s : ℂ) :
    pairedEtaLaplaceReflectionMultiplier (starRingEnd ℂ s) =
      starRingEnd ℂ (pairedEtaLaplaceReflectionMultiplier s) := by
  unfold pairedEtaLaplaceReflectionMultiplier
  rw [pairedEtaCompletedLaplaceAmplitude_conj]
  have hsub : 1 - starRingEnd ℂ s = starRingEnd ℂ (1 - s) := by simp
  rw [hsub, pairedEtaCompletedLaplaceAmplitude_conj]
  simp

/-- In same-ordinate coordinates, the literal partition at the complementary
tilt is the conjugate of the multiplier-weighted original partition. -/
theorem pairedEtaLaplacePartition_one_sub_conj
    {s : ℂ} (hspos : 0 < s.re) (hslt : s.re < 1) :
    pairedEtaLaplacePartition (1 - starRingEnd ℂ s) =
      starRingEnd ℂ
        (pairedEtaLaplaceReflectionMultiplier s *
          pairedEtaLaplacePartition s) := by
  have h := pairedEtaLaplacePartition_one_sub
    (s := starRingEnd ℂ s) (by simpa using hspos) (by simpa using hslt)
  rw [pairedEtaLaplaceReflectionMultiplier_conj,
    pairedEtaLaplacePartition_conj hspos] at h
  simpa only [map_mul] using h

/-- On the critical line the reflection multiplier has unit squared norm. -/
theorem normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_of_re_eq_half
    {s : ℂ} (hs : s.re = 1 / 2) :
    Complex.normSq (pairedEtaLaplaceReflectionMultiplier s) = 1 := by
  have hspos : 0 < s.re := by rw [hs]; norm_num
  have hslt : s.re < 1 := by rw [hs]; norm_num
  rw [normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_iff_weight_eq
    hspos hslt]
  congr 1
  apply Complex.ext
  · norm_num [hs]
  · simp

/-- At a nontrivial zero, vanishing of the first actual scaled localized
completion-distortion coefficient is exactly the unit-norm equation for the
explicit reflection multiplier. -/
theorem
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_sub_conjugatePartner_eq_zero_iff_reflectionMultiplier_normSq_eq_one
    (rho : NontrivialZetaZero) :
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient rho -
          pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient
            (NontrivialZetaZero.conjugatePartner rho) = 0 ↔
      Complex.normSq (pairedEtaLaplaceReflectionMultiplier rho.1) = 1 := by
  rw [
    pairedEtaLocalizedGaussianLargeTimeLeadingCoefficient_sub_conjugatePartner_eq_zero_iff_weight_eq]
  exact (normSq_pairedEtaLaplaceReflectionMultiplier_eq_one_iff_weight_eq
    (NontrivialZetaZero.zero_lt_re rho)
    (NontrivialZetaZero.re_lt_one rho)).symm

end

end RiemannGaussian
