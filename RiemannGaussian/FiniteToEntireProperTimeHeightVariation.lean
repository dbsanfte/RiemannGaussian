import RiemannGaussian.FiniteToEntireProperTimeSmallBound

/-!
# Root-height variation behind the small-time frontier

The zero-time trace is controlled by the sum of the positive imaginary parts
of the polynomial roots.  For a real polynomial, ordinary signed root moments
cannot see this quantity: conjugate roots cancel exactly.  This file makes
the distinction precise.

The upper-root height mass is exactly half of the total variation of the
imaginary parts of all complex roots, counted with algebraic multiplicity.
The signed imaginary first moment is zero.  Thus the obstruction is an
unsigned `L¹` root statistic rather than the first Vieta moment.  A final
bound places it below half of the total root-norm mass, exposing the kind of
global root control that would suffice.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ComplexConjugate Interval Topology

namespace RiemannGaussian

noncomputable section

/-- On an upper-half-plane multiset, summing absolute imaginary parts is the
same as summing imaginary parts. -/
theorem multiset_sum_abs_im_eq_finiteUpperHeightMass
    {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im) :
    (upper.map fun alpha ↦ |alpha.im|).sum =
      finiteUpperHeightMass upper := by
  induction upper using Multiset.induction_on with
  | empty => simp [finiteUpperHeightMass]
  | @cons alpha upper ih =>
      have halphaHead : 0 < alpha.im := halpha alpha (by simp)
      have halphaTail : ∀ beta ∈ upper, 0 < beta.im := by
        intro beta hbeta
        exact halpha beta (by simp [hbeta])
      simp only [Multiset.map_cons, Multiset.sum_cons,
        finiteUpperHeightMass]
      rw [abs_of_pos halphaHead, ih halphaTail]
      rfl

/-- A conjugate-pair multiset has twice the unsigned height of its chosen
upper representatives. -/
theorem conjugatePairRootMultiset_abs_im_sum
    {upper : Multiset ℂ}
    (halpha : ∀ alpha ∈ upper, 0 < alpha.im) :
    ((conjugatePairRootMultiset upper).map fun z ↦ |z.im|).sum =
      2 * finiteUpperHeightMass upper := by
  rw [conjugatePairRootMultiset, Multiset.map_add, Multiset.sum_add,
    multiset_sum_abs_im_eq_finiteUpperHeightMass halpha]
  have hconj :
      (((upper.map (starRingEnd ℂ)).map fun z ↦ |z.im|).sum) =
        (upper.map fun z ↦ |z.im|).sum := by
    simp only [Multiset.map_map, Function.comp_apply, Complex.conj_im,
      abs_neg]
  rw [hconj, multiset_sum_abs_im_eq_finiteUpperHeightMass halpha]
  ring

/-- A multiset lying on the real axis has zero unsigned imaginary mass. -/
theorem multiset_sum_abs_im_eq_zero_of_im_eq_zero
    {roots : Multiset ℂ}
    (hreal : ∀ z ∈ roots, z.im = 0) :
    (roots.map fun z ↦ |z.im|).sum = 0 := by
  induction roots using Multiset.induction_on with
  | empty => simp
  | @cons z roots ih =>
      have hz : z.im = 0 := hreal z (by simp)
      have htail : ∀ w ∈ roots, w.im = 0 := by
        intro w hw
        exact hreal w (by simp [hw])
      simp [hz, ih htail]

/-- The total variation of the imaginary parts of all complex roots of a
real polynomial, with algebraic multiplicity. -/
def realPolynomialRootImaginaryVariation (A : ℝ[X]) : ℝ :=
  (((A.map Complex.ofRealHom).roots).map fun z ↦ |z.im|).sum

/-- The total norm mass of all complex roots of a real polynomial, with
algebraic multiplicity. -/
def realPolynomialRootNormMass (A : ℝ[X]) : ℝ :=
  (((A.map Complex.ofRealHom).roots).map fun z ↦ ‖z‖).sum

/-- For a real polynomial, total imaginary variation is exactly twice its
upper-root height mass. -/
theorem realPolynomialRootImaginaryVariation_eq_two_mul_upperHeight
    (A : ℝ[X]) :
    realPolynomialRootImaginaryVariation A =
      2 * realPolynomialUpperHeightMass A := by
  rw [realPolynomialRootImaginaryVariation,
    realPolynomial_roots_eq_real_add_conjugatePairs,
    Multiset.map_add, Multiset.sum_add,
    multiset_sum_abs_im_eq_zero_of_im_eq_zero
      (realPolynomialRealRootMultiset_im_eq_zero A),
    conjugatePairRootMultiset_abs_im_sum
      (realPolynomialUpperRootMultiset_im_pos A)]
  simp [realPolynomialUpperHeightMass]

/-- Equivalently, the small-time height statistic is half of the full
unsigned imaginary variation of the root divisor. -/
theorem realPolynomialUpperHeightMass_eq_half_imaginaryVariation
    (A : ℝ[X]) :
    realPolynomialUpperHeightMass A =
      (2 : ℝ)⁻¹ * realPolynomialRootImaginaryVariation A := by
  rw [realPolynomialRootImaginaryVariation_eq_two_mul_upperHeight]
  ring

/-- Conjugate pairing annihilates the signed imaginary first moment. -/
theorem conjugatePairRootMultiset_im_sum (upper : Multiset ℂ) :
    ((conjugatePairRootMultiset upper).map Complex.im).sum = 0 := by
  rw [conjugatePairRootMultiset, Multiset.map_add, Multiset.sum_add]
  have hconj :
      (((upper.map (starRingEnd ℂ)).map Complex.im).sum) =
        -(upper.map Complex.im).sum := by
    simp only [Multiset.map_map, Function.comp_apply, Complex.conj_im,
      Multiset.sum_map_neg]
  rw [hconj]
  ring

/-- A real-axis multiset has zero signed imaginary first moment. -/
theorem multiset_sum_im_eq_zero_of_im_eq_zero
    {roots : Multiset ℂ}
    (hreal : ∀ z ∈ roots, z.im = 0) :
    (roots.map Complex.im).sum = 0 := by
  induction roots using Multiset.induction_on with
  | empty => simp
  | @cons z roots ih =>
      have hz : z.im = 0 := hreal z (by simp)
      have htail : ∀ w ∈ roots, w.im = 0 := by
        intro w hw
        exact hreal w (by simp [hw])
      simp [hz, ih htail]

/-- The signed imaginary first moment of every real polynomial root divisor
is zero.  This is the precise cancellation that makes the ordinary first
Vieta moment blind to the positive upper-root height mass. -/
theorem realPolynomial_roots_im_sum_eq_zero (A : ℝ[X]) :
    (((A.map Complex.ofRealHom).roots).map Complex.im).sum = 0 := by
  rw [realPolynomial_roots_eq_real_add_conjugatePairs,
    Multiset.map_add, Multiset.sum_add,
    multiset_sum_im_eq_zero_of_im_eq_zero
      (realPolynomialRealRootMultiset_im_eq_zero A),
    conjugatePairRootMultiset_im_sum, zero_add]

/-- The unsigned imaginary variation is bounded by the total norm mass of
the complete complex root divisor. -/
theorem realPolynomialRootImaginaryVariation_le_rootNormMass
    (A : ℝ[X]) :
    realPolynomialRootImaginaryVariation A ≤
      realPolynomialRootNormMass A := by
  unfold realPolynomialRootImaginaryVariation realPolynomialRootNormMass
  induction (A.map Complex.ofRealHom).roots using Multiset.induction_on with
  | empty => simp
  | @cons z roots ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact add_le_add (Complex.abs_im_le_norm z) ih

/-- Hence the upper-root height mass is at most half of the total root-norm
mass. -/
theorem realPolynomialUpperHeightMass_le_half_rootNormMass
    (A : ℝ[X]) :
    realPolynomialUpperHeightMass A ≤
      (2 : ℝ)⁻¹ * realPolynomialRootNormMass A := by
  rw [realPolynomialUpperHeightMass_eq_half_imaginaryVariation]
  exact mul_le_mul_of_nonneg_left
    (realPolynomialRootImaginaryVariation_le_rootNormMass A) (by positivity)

/-- Under failure of RH, the small-time obstruction therefore forces a
literal lower bound on both the unsigned imaginary variation and the total
norm mass of the same canonical polynomial root divisors.  The signed first
moment remains zero by the theorem above. -/
theorem exists_canonicalFiniteHardyFrontier_rootVariationObstruction_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      riemannXiSpectral z ≠ 0 ∧ ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
        ∀ (a error : ℝ), 0 < a → 0 < error →
          ∃ T : ℝ, a ≤ T ∧
            ∀ᶠ n in atTop,
              (-2 * Real.log (pairHyperbolicThreshold eta z.im) -
                  (∫ tau in a..T,
                    riemannXiUpperHyperbolicHeatSum z tau) - error) /
                    (2 * a * z.im) <
                  realPolynomialRootImaginaryVariation (B n) ∧
                (-2 * Real.log (pairHyperbolicThreshold eta z.im) -
                    (∫ tau in a..T,
                      riemannXiUpperHyperbolicHeatSum z tau) - error) /
                      (2 * a * z.im) <
                  realPolynomialRootNormMass (B n) := by
  obtain ⟨eta, heta, z, hz, hxi, B, hlimit, hfrontier, hpositive,
      hheight⟩ :=
    exists_canonicalFiniteHardyFrontier_smallTimeHeightObstruction_of_not_rh
      hRH
  refine ⟨eta, heta, z, hz, hxi, B, hlimit, hfrontier, hpositive, ?_⟩
  intro a error ha herror
  obtain ⟨T, haT, hbound⟩ := hheight a error ha herror
  refine ⟨T, haT, ?_⟩
  filter_upwards [hbound] with n hn
  let D : ℝ :=
    -2 * Real.log (pairHyperbolicThreshold eta z.im) -
      (∫ tau in a..T, riemannXiUpperHyperbolicHeatSum z tau) - error
  have hscaled : 2 * (D / (4 * a * z.im)) <
      2 * realPolynomialUpperHeightMass (B n) := by
    have hn' : D / (4 * a * z.im) <
        realPolynomialUpperHeightMass (B n) := by simpa [D] using hn
    linarith
  have hquot : 2 * (D / (4 * a * z.im)) = D / (2 * a * z.im) := by
    field_simp [ne_of_gt ha, ne_of_gt hz]
    ring
  have hvariation : D / (2 * a * z.im) <
      realPolynomialRootImaginaryVariation (B n) := by
    calc
      D / (2 * a * z.im) = 2 * (D / (4 * a * z.im)) := hquot.symm
      _ < 2 * realPolynomialUpperHeightMass (B n) := hscaled
      _ = realPolynomialRootImaginaryVariation (B n) :=
        (realPolynomialRootImaginaryVariation_eq_two_mul_upperHeight
          (B n)).symm
  have hvariation' :
      (-2 * Real.log (pairHyperbolicThreshold eta z.im) -
          (∫ tau in a..T, riemannXiUpperHyperbolicHeatSum z tau) - error) /
            (2 * a * z.im) <
        realPolynomialRootImaginaryVariation (B n) := by
    simpa [D] using hvariation
  exact ⟨hvariation', hvariation'.trans_le
    (realPolynomialRootImaginaryVariation_le_rootNormMass (B n))⟩

end

end RiemannGaussian
