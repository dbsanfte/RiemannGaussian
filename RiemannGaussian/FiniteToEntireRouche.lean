import RiemannGaussian.FiniteToEntireRadialApproximation
import RiemannGaussian.PolynomialLogDerivativeCircle

/-!
# Rouché comparison on spectral circles

This file turns a strict boundary approximation into equality of
logarithmic-derivative circle integrals.  The proof is direct: on the circle,
the quotient of the approximant by the reference function lies in the open
right half-plane, so its principal complex logarithm is a valid primitive of
the difference of logarithmic derivatives.  Its integral around the closed
circle vanishes.
-/

open Complex Filter Metric Polynomial Set
open scoped Classical Topology

namespace RiemannGaussian

noncomputable section

/-- Strict Rouché domination makes both functions nonzero on the comparison
circle. -/
theorem ne_zero_on_sphere_of_norm_sub_lt
    {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hboundary : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    (∀ z ∈ sphere c R, f z ≠ 0) ∧
      ∀ z ∈ sphere c R, g z ≠ 0 := by
  constructor
  · intro z hz
    have h := hboundary z hz
    exact norm_pos_iff.mp ((norm_nonneg _).trans_lt h)
  · intro z hz hgz
    have h := hboundary z hz
    rw [hgz, zero_sub, norm_neg] at h
    exact (lt_irrefl _ h)

/-- Rouché domination on a circle forces equality of the two
logarithmic-derivative circle integrals. -/
theorem circleIntegral_logDeriv_eq_of_norm_sub_lt
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, ‖g z - f z‖ < ‖f z‖) :
    (∮ z in C(c, R), logDeriv g z) =
      ∮ z in C(c, R), logDeriv f z := by
  obtain ⟨hfzero, hgzero⟩ :=
    ne_zero_on_sphere_of_norm_sub_lt hboundary
  let q : ℂ → ℂ := fun z => g z / f z
  have hprimitive : ∀ z ∈ sphere c R,
      HasDerivWithinAt (fun u => Complex.log (q u))
        (logDeriv g z - logDeriv f z) (sphere c R) z := by
    intro z hz
    have hclose : ‖q z - 1‖ < 1 := by
      have hfnorm : 0 < ‖f z‖ := norm_pos_iff.mpr (hfzero z hz)
      have hform : q z - 1 = (g z - f z) / f z := by
        dsimp only [q]
        field_simp [hfzero z hz]
      rw [hform, norm_div]
      exact (div_lt_one hfnorm).mpr (hboundary z hz)
    have hreal : 0 < (q z).re := by
      have hre : |(q z).re - 1| < 1 := by
        calc
          |(q z).re - 1| = |(q z - 1).re| := by simp
          _ ≤ ‖q z - 1‖ := Complex.abs_re_le_norm _
          _ < 1 := hclose
      linarith [abs_lt.mp hre]
    have hslit : q z ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl hreal
    have hqdiff : DifferentiableAt ℂ q z := by
      exact (hg z).div (hf z) (hfzero z hz)
    have hlog := hqdiff.hasDerivAt.clog hslit
    have hquotient :
        logDeriv q z = logDeriv g z - logDeriv f z := by
      simpa [q] using
        (logDeriv_div z (hgzero z hz) (hfzero z hz) (hg z) (hf z))
    have hlog' : HasDerivAt (fun u => Complex.log (q u))
        (logDeriv q z) z := by
      simpa [logDeriv_apply] using hlog
    rw [hquotient] at hlog'
    exact hlog'.hasDerivWithinAt
  have hzero :
      (∮ z in C(c, R), logDeriv g z - logDeriv f z) = 0 :=
    circleIntegral.integral_eq_zero_of_hasDerivWithinAt hR hprimitive
  have hfContinuous : ContinuousOn (logDeriv f) (sphere c R) := by
    unfold logDeriv
    exact hf.deriv.continuous.continuousOn.div₀
      hf.continuous.continuousOn hfzero
  have hgContinuous : ContinuousOn (logDeriv g) (sphere c R) := by
    unfold logDeriv
    exact hg.deriv.continuous.continuousOn.div₀
      hg.continuous.continuousOn hgzero
  have hfIntegrable : CircleIntegrable (logDeriv f) c R :=
    hfContinuous.circleIntegrable hR
  have hgIntegrable : CircleIntegrable (logDeriv g) c R :=
    hgContinuous.circleIntegrable hR
  rw [circleIntegral.integral_sub hgIntegrable hfIntegrable] at hzero
  exact sub_eq_zero.mp hzero

/-- Polynomial specialization of Rouché: the algebraic root count in the
open ball is certified by the reference function's logarithmic-derivative
integral. -/
theorem realPolynomialRootCountInBall_mul_eq_circleIntegral_of_norm_sub_lt
    {A : ℝ[X]} {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R,
      ‖(A.map Complex.ofRealHom).eval z - f z‖ < ‖f z‖) :
    (realPolynomialRootCountInBall A c R : ℂ) *
        (2 * Real.pi : ℝ) * Complex.I =
      ∮ z in C(c, R), logDeriv f z := by
  let g : ℂ → ℂ := fun z => (A.map Complex.ofRealHom).eval z
  obtain ⟨hfzero, hgzero⟩ :=
    ne_zero_on_sphere_of_norm_sub_lt (f := f) (g := g) (by
      simpa [g] using hboundary)
  obtain ⟨w, hw⟩ :=
    (NormedSpace.sphere_nonempty (E := ℂ) (x := c)).mpr hR
  have hA : A ≠ 0 := by
    intro hAzero
    exact hgzero w hw (by simp [g, hAzero])
  have hpolynomial :=
    circleIntegral_logDeriv_realPolynomial_eq_rootCount
      hA hR (by simpa [g] using hgzero)
  have hrouche := circleIntegral_logDeriv_eq_of_norm_sub_lt
    hf (A.map Complex.ofRealHom).differentiable hR hboundary
  calc
    (realPolynomialRootCountInBall A c R : ℂ) *
          (2 * Real.pi : ℝ) * Complex.I =
        ∮ z in C(c, R), logDeriv g z := by
      simpa [g, realPolynomialRootCountInBall] using hpolynomial.symm
    _ = ∮ z in C(c, R), logDeriv f z := by
      simpa [g] using hrouche

/-- Under failure of RH, the scheduled canonical finite Hardy polynomials
have exactly the spectral-xi argument-principle count inside every selected
expanding circle. -/
theorem exists_radialRouche_rootCount_integral_sequence_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ z : ℂ, 0 < z.im ∧
      ∃ A : ℝ, 1 ≤ A ∧ ∃ C : ℝ, 0 < C ∧
        ∃ B : ℕ → ℝ[X],
          let L := finiteERootPinnedRadialConstant A eta z
          Tendsto (radialRoucheIndex A L C) atTop atTop ∧
          TendstoLocallyUniformlyOn
            (fun n w => ((B n).map Complex.ofRealHom).eval w)
            riemannXiSpectral atTop Set.univ ∧
          (∀ n, CanonicalFiniteHardyFrontier (B n) eta z ∧
            (B n).natDegree ≤ max (radialRoucheIndex A L C n) 3) ∧
          (∀ n, (radialRoucheIndex A L C n : ℝ) <
            radialRoucheIndexGrowthConstant A L C *
              Real.exp (5 * quantitativeSpectralRadialBoundary n)) ∧
          (∀ (n : ℕ) {w : ℂ},
            ‖w‖ = quantitativeSpectralRadialBoundary n →
              Real.exp
                  (-C * Real.exp
                    (5 * quantitativeSpectralRadialBoundary n)) ≤
                ‖riemannXiSpectral w‖) ∧
          ∀ n : ℕ,
            (realPolynomialRootCountInBall (B n) 0
                (quantitativeSpectralRadialBoundary n) : ℂ) *
                (2 * Real.pi : ℝ) * Complex.I =
              ∮ w in C(0, quantitativeSpectralRadialBoundary n),
                logDeriv riemannXiSpectral w := by
  obtain ⟨eta, heta, z, hz, A, hA, C, hC, B,
      hindex, hlimit, hfrontier, hgrowth, hfloor, herror⟩ :=
    exists_radialRouche_canonicalFiniteHardyFrontier_sequence_of_not_rh hRH
  let L : ℝ := finiteERootPinnedRadialConstant A eta z
  refine ⟨eta, heta, z, hz, A, hA, C, hC, B, ?_⟩
  dsimp only
  refine ⟨by simpa [L] using hindex, hlimit, ?_, ?_, ?_, ?_⟩
  · intro n
    simpa [L] using hfrontier n
  · intro n
    simpa [L] using hgrowth n
  · intro n w hw
    exact hfloor n hw
  · intro n
    apply realPolynomialRootCountInBall_mul_eq_circleIntegral_of_norm_sub_lt
      differentiable_riemannXiSpectral
      (quantitativeSpectralRadialBoundary_pos n).le
    intro w hw
    exact (herror n (by simpa [mem_sphere, dist_zero_left] using hw)).2

end

end RiemannGaussian
