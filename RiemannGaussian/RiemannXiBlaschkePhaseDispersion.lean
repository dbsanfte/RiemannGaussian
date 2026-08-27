import RiemannGaussian.FiniteToEntireBlaschkeRigidityTrichotomy

/-!
# Pairwise phase dispersion behind finite Blaschke cancellation

For a finite family of complex Hilbert-space vectors, the squared difference
between termwise `l1` variation and the norm of the resultant is exactly a
double sum of pairwise angular defects

`norm(u_i) * norm(u_j) - re <u_i, u_j>`.

Every pairwise defect is nonnegative.  Specializing to the signed spectral
Blaschke logarithmic-derivative terms converts the cancellation gap into an
exact nonnegative pair-interaction energy.  A persistent lower bound on the
cancellation gap therefore forces a persistent squared lower bound on this
phase-dispersion energy.
-/

open Complex Filter MeasureTheory Metric Polynomial Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The total pairwise angular defect of a finite family of vectors in a
complex inner-product space. -/
def finiteComplexPhaseDispersion {ι E : Type*}
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (u : ι → E) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s,
    (‖u i‖ * ‖u j‖ - (inner ℂ (u i) (u j)).re)

/-- Pairwise phase dispersion is nonnegative term by term. -/
theorem finiteComplexPhaseDispersion_nonneg {ι E : Type*}
    [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (u : ι → E) :
    0 ≤ finiteComplexPhaseDispersion s u := by
  unfold finiteComplexPhaseDispersion
  apply Finset.sum_nonneg
  intro i _hi
  apply Finset.sum_nonneg
  intro j _hj
  exact sub_nonneg.mpr (re_inner_le_norm (𝕜 := ℂ) (u i) (u j))

/-- Exact finite-family identity: phase dispersion is the squared `l1`
variation minus the squared norm of the resultant. -/
theorem finiteComplexPhaseDispersion_eq_variation_sq_sub_norm_sum_sq
    {ι E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (u : ι → E) :
    finiteComplexPhaseDispersion s u =
      (∑ i ∈ s, ‖u i‖) ^ 2 - ‖∑ i ∈ s, u i‖ ^ 2 := by
  symm
  unfold finiteComplexPhaseDispersion
  rw [@norm_sq_eq_re_inner ℂ E _ _ _]
  rw [sum_inner s u]
  simp_rw [inner_sum s u]
  simp_rw [map_sum]
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  simp [Finset.sum_sub_distrib]

/-- The pairwise phase-dispersion energy of the signed Blaschke terms in one
finite upper spectral window. -/
def riemannXiUpperBlaschkePhaseDispersionWindow (z : ℂ) (T : ℝ) : ℝ :=
  finiteComplexPhaseDispersion (spectralUpperZetaZeroWindow T)
    (zetaUpperBlaschkeLogDerivativeSummand z)

/-- Spectral phase dispersion is nonnegative. -/
theorem riemannXiUpperBlaschkePhaseDispersionWindow_nonneg
    (z : ℂ) (T : ℝ) :
    0 ≤ riemannXiUpperBlaschkePhaseDispersionWindow z T :=
  finiteComplexPhaseDispersion_nonneg _ _

/-- Exact spectral identity between pairwise dispersion, termwise variation,
and the signed Blaschke resultant. -/
theorem riemannXiUpperBlaschkePhaseDispersionWindow_eq_variation_sq_sub_norm_sq
    (z : ℂ) (T : ℝ) :
    riemannXiUpperBlaschkePhaseDispersionWindow z T =
      riemannXiUpperBlaschkeLogDerivativeVariationWindow z T ^ 2 -
        ‖riemannXiUpperBlaschkeLogDerivativeWindow z T‖ ^ 2 := by
  simpa [riemannXiUpperBlaschkePhaseDispersionWindow,
    riemannXiUpperBlaschkeLogDerivativeVariationWindow,
    riemannXiUpperBlaschkeLogDerivativeWindow] using
    (finiteComplexPhaseDispersion_eq_variation_sq_sub_norm_sum_sq
      (spectralUpperZetaZeroWindow T)
      (zetaUpperBlaschkeLogDerivativeSummand z))

/-- The squared dispersion factors exactly into cancellation gap times the
sum of variation and resultant norm. -/
theorem riemannXiUpperBlaschkePhaseDispersionWindow_eq_cancellation_mul_add
    (z : ℂ) (T : ℝ) :
    riemannXiUpperBlaschkePhaseDispersionWindow z T =
      riemannXiUpperBlaschkeLogDerivativeCancellation z T *
        (riemannXiUpperBlaschkeLogDerivativeVariationWindow z T +
          ‖riemannXiUpperBlaschkeLogDerivativeWindow z T‖) := by
  rw [
    riemannXiUpperBlaschkePhaseDispersionWindow_eq_variation_sq_sub_norm_sq]
  unfold riemannXiUpperBlaschkeLogDerivativeCancellation
  ring

/-- At a noncolliding upper point, the same factorization uses the finite
spectral Blaschke product directly. -/
theorem riemannXiUpperBlaschkePhaseDispersionWindow_eq_cancellation_mul_product_add
    {z : ℂ} (hz : 0 < z.im) (hxi : riemannXiSpectral z ≠ 0) (T : ℝ) :
    riemannXiUpperBlaschkePhaseDispersionWindow z T =
      riemannXiUpperBlaschkeLogDerivativeCancellation z T *
        (riemannXiUpperBlaschkeLogDerivativeVariationWindow z T +
          ‖logDeriv (riemannXiUpperBlaschkeProductWindow T) z‖) := by
  rw [
    riemannXiUpperBlaschkePhaseDispersionWindow_eq_cancellation_mul_add,
    logDeriv_riemannXiUpperBlaschkeProductWindow_eq_sum hz hxi T]

/-- The square of the cancellation gap is bounded by the pairwise phase
dispersion energy. -/
theorem riemannXiUpperBlaschkeLogDerivativeCancellation_sq_le_phaseDispersion
    (z : ℂ) (T : ℝ) :
    riemannXiUpperBlaschkeLogDerivativeCancellation z T ^ 2 ≤
      riemannXiUpperBlaschkePhaseDispersionWindow z T := by
  have hnorm : 0 ≤ ‖riemannXiUpperBlaschkeLogDerivativeWindow z T‖ :=
    norm_nonneg _
  have hvariation :
      ‖riemannXiUpperBlaschkeLogDerivativeWindow z T‖ ≤
        riemannXiUpperBlaschkeLogDerivativeVariationWindow z T :=
    norm_riemannXiUpperBlaschkeLogDerivativeWindow_le_variation z T
  rw [
    riemannXiUpperBlaschkePhaseDispersionWindow_eq_variation_sq_sub_norm_sq]
  unfold riemannXiUpperBlaschkeLogDerivativeCancellation
  nlinarith

/-- An eventual cancellation-gap threshold forces its squared threshold into
the pairwise phase-dispersion energy. -/
theorem eventually_phaseDispersion_of_eventually_cancellation
    {z : ℂ} {q : ℝ} (hq : 0 < q)
    (hcancellation : ∀ᶠ T : ℝ in atTop,
      q / 4 ≤ riemannXiUpperBlaschkeLogDerivativeCancellation z T) :
    ∀ᶠ T : ℝ in atTop,
      (q / 4) ^ 2 ≤ riemannXiUpperBlaschkePhaseDispersionWindow z T := by
  filter_upwards [hcancellation] with T hT
  have hqFourth : 0 ≤ q / 4 := by positivity
  have hgap :
      0 ≤ riemannXiUpperBlaschkeLogDerivativeCancellation z T :=
    riemannXiUpperBlaschkeLogDerivativeCancellation_nonneg z T
  have hsquare :
      (q / 4) ^ 2 ≤
        riemannXiUpperBlaschkeLogDerivativeCancellation z T ^ 2 := by
    nlinarith
  exact hsquare.trans
    (riemannXiUpperBlaschkeLogDerivativeCancellation_sq_le_phaseDispersion
      z T)

/-- The residual/cancellation/height trichotomy can therefore be stated using
the concrete pairwise phase-dispersion energy. -/
theorem reflectionResidual_or_phaseDispersion_or_height_unbounded
    {z : ℂ} {q : ℝ} (hq : 0 < q) (height : ℕ → ℝ)
    (htrichotomy :
      (∃ᶠ T : ℝ in atTop,
        q / 4 ≤ ‖riemannXiUpperSpectralReflectionResidual z T‖) ∨
        (∀ᶠ T : ℝ in atTop,
          q / 4 ≤ riemannXiUpperBlaschkeLogDerivativeCancellation z T) ∨
        ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop, M < height n) :
    (∃ᶠ T : ℝ in atTop,
      q / 4 ≤ ‖riemannXiUpperSpectralReflectionResidual z T‖) ∨
      (∀ᶠ T : ℝ in atTop,
        (q / 4) ^ 2 ≤
          riemannXiUpperBlaschkePhaseDispersionWindow z T) ∨
      ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop, M < height n := by
  rcases htrichotomy with hresidual | hcancellation | hunbounded
  · exact Or.inl hresidual
  · exact Or.inr (Or.inl
      (eventually_phaseDispersion_of_eventually_cancellation
        hq hcancellation))
  · exact Or.inr (Or.inr hunbounded)

/-- Under failure of RH, the canonical Hardy frontier forces either a
frequently-large exact xi residual, an eventually-large pairwise Blaschke
phase-dispersion energy, or unbounded polynomial upper-height mass. -/
theorem exists_canonicalFiniteHardyFrontier_residual_or_phaseDispersion_or_height_unbounded_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      riemannXiSpectral z ≠ 0 ∧ ∃ delta : ℝ, 0 < delta ∧
      (∀ rho : NontrivialZetaZero,
        delta ≤ ‖z - zetaSpectralCoordinate rho.1‖) ∧
      ∃ B : ℕ → ℝ[X],
        TendstoLocallyUniformlyOn
          (fun n w ↦ ((B n).map Complex.ofRealHom).eval w)
          riemannXiSpectral atTop Set.univ ∧
        (∀ n, CanonicalFiniteHardyFrontier (B n) eta z) ∧
        0 < -2 * Real.log (pairHyperbolicThreshold eta z.im) ∧
        (∀ (a error : ℝ), 0 < a → 0 < error →
          ∃ T : ℝ, a ≤ T ∧
            ∀ᶠ n in atTop,
              (-2 * Real.log (pairHyperbolicThreshold eta z.im) -
                  (∫ tau in a..T,
                    riemannXiUpperHyperbolicHeatSum z tau) - error) /
                    (4 * a * z.im) <
                realPolynomialUpperHeightMass (B n)) ∧
        0 < riemannXiUpperBlaschkeVariationThreshold
          (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta ∧
        ((∃ᶠ T : ℝ in atTop,
            riemannXiUpperBlaschkeVariationThreshold
                (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta /
                4 ≤
              ‖riemannXiUpperSpectralReflectionResidual z T‖) ∨
          (∀ᶠ T : ℝ in atTop,
            (riemannXiUpperBlaschkeVariationThreshold
                (-2 * Real.log (pairHyperbolicThreshold eta z.im)) z delta /
                4) ^ 2 ≤
              riemannXiUpperBlaschkePhaseDispersionWindow z T) ∨
          ∀ M : ℝ, 0 ≤ M → ∃ᶠ n in atTop,
            M < realPolynomialUpperHeightMass (B n)) := by
  obtain ⟨eta, heta, z, hz, hxi, delta, hdelta, hgap, B,
      hlimit, hfrontier, hpositive, hobstruction, hvariationPositive,
      htrichotomy⟩ :=
    exists_canonicalFiniteHardyFrontier_residual_or_cancellation_or_height_unbounded_of_not_rh
      hRH
  have henergy :=
    reflectionResidual_or_phaseDispersion_or_height_unbounded
      hvariationPositive (fun n ↦ realPolynomialUpperHeightMass (B n))
        htrichotomy
  exact ⟨eta, heta, z, hz, hxi, delta, hdelta, hgap, B, hlimit,
    hfrontier, hpositive, hobstruction, hvariationPositive, henergy⟩

end

end RiemannGaussian
