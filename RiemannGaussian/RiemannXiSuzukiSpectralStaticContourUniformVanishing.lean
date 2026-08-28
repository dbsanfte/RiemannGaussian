import RiemannGaussian.RiemannXiSuzukiSpectralStaticContourVanishing

/-!
# Uniform vanishing of the static signed vertical remainder

The selected static vertical remainder is already known to vanish at every
fixed purely imaginary observation point above the contour.  This module
extracts the common logarithmic-derivative main term and combines it with the
inverse-square Cauchy-factor error estimate.  The result is uniform vanishing
on every compact interval of imaginary observation heights strictly above
`1`.

This compact-uniform form is the appropriate input for subsequent analytic
transport: it permits bounded families of observation points and integration
in the observation parameter without reverting to an unproved exchange of
limits.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The signed logarithmic-derivative main term left by the static Cauchy
factor tends to zero on the quantitative contour sequence. -/
theorem tendsto_staticContourLogDerivativeMain_quantitative_zero :
    Tendsto
      (fun n : ℕ ↦
        (4 / quantitativeSpectralBoundaryTruncation n) *
          (∫ y : ℝ in (0 : ℝ)..1,
            (xiSpectralNegativeLogDerivative
              ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                (y : ℂ) * Complex.I)).re))
      atTop (nhds 0) := by
  let V : ℕ → ℂ := fun n ↦
    -Complex.I *
      xiSpectralBlaschkeSignedVerticalRemainderWindow
        (quantitativeSpectralBoundaryTruncation n) 0
        (((2 : ℝ) : ℂ) * Complex.I)
  let M : ℕ → ℝ := fun n ↦
    (4 / quantitativeSpectralBoundaryTruncation n) *
      (∫ y : ℝ in (0 : ℝ)..1,
        (xiSpectralNegativeLogDerivative
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)).re)
  have hsum : Tendsto (fun n : ℕ ↦ V n + (M n : ℂ))
      atTop (nhds 0) := by
    simpa [V, M] using
      tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_add_logDerivative_main_quantitative_zero
        (by norm_num : (1 : ℝ) < 2)
  have hvertical : Tendsto V atTop (nhds 0) := by
    simpa [V] using
      tendsto_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_quantitative_zero
        (by norm_num : (1 : ℝ) < 2)
  have hcomplex : Tendsto (fun n : ℕ ↦ (M n : ℂ))
      atTop (nhds 0) := by
    have hdifference : Tendsto
        (fun n : ℕ ↦ (V n + (M n : ℂ)) - V n)
        atTop (nhds 0) := by
      simpa using hsum.sub hvertical
    refine hdifference.congr' (Eventually.of_forall fun n ↦ ?_)
    ring
  have hreal : Tendsto M atTop (nhds 0) :=
    tendsto_ofReal_iff.mp hcomplex
  simpa [M] using hreal

/-- A quantitative majorant for the static signed vertical remainder,
uniform in every observation height bounded above by `b`. -/
theorem norm_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_quantitative_le
    {v b : ℝ} (hv : 1 < v) (hvb : v ≤ b) (n : ℕ) :
    ‖-Complex.I *
        xiSpectralBlaschkeSignedVerticalRemainderWindow
          (quantitativeSpectralBoundaryTruncation n) 0
          ((v : ℂ) * Complex.I)‖ ≤
      4 * b *
          ((1 / quantitativeSpectralBoundaryTruncation n ^ 2) *
            (∫ y : ℝ in (0 : ℝ)..1,
              ‖xiSpectralNegativeLogDerivative
                ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                  (y : ℂ) * Complex.I)‖)) +
        |(4 / quantitativeSpectralBoundaryTruncation n) *
          (∫ y : ℝ in (0 : ℝ)..1,
            (xiSpectralNegativeLogDerivative
              ((quantitativeSpectralBoundaryTruncation n : ℂ) +
                (y : ℂ) * Complex.I)).re)| := by
  let T : ℝ := quantitativeSpectralBoundaryTruncation n
  let F : ℝ := ∫ y : ℝ in (0 : ℝ)..1,
    (xiSpectralBlaschkeRightFoldedVerticalKernel T
      ((v : ℂ) * Complex.I) y).re
  let L : ℝ := ∫ y : ℝ in (0 : ℝ)..1,
    (xiSpectralNegativeLogDerivative
      ((T : ℂ) + (y : ℂ) * Complex.I)).re
  let N : ℝ := ∫ y : ℝ in (0 : ℝ)..1,
    ‖xiSpectralNegativeLogDerivative
      ((T : ℂ) + (y : ℂ) * Complex.I)‖
  let E : ℝ := (1 / T ^ 2) * N
  have hT : 0 < T :=
    (Nat.cast_nonneg n).trans_lt
      (by simpa [T] using
        (quantitativeSpectralBoundaryTruncation_spec n).1)
  have hboundary : ∀ rho : NontrivialZetaZero,
      |(zetaSpectralCoordinate rho.1).re| ≠ T := by
    simpa [T] using quantitativeSpectralBoundaryTruncation_zeroFree n
  have hN : 0 ≤ N := by
    dsimp [N]
    exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun y ↦ norm_nonneg _)
  have hE : 0 ≤ E := mul_nonneg (by positivity) hN
  have herror : |F + (2 / T) * L| ≤ (2 * v / T ^ 2) * N := by
    simpa [F, L, N, T] using
      abs_intervalIntegral_xiSpectralBlaschkeRightFoldedVerticalKernel_re_add_main_quantitative_le
        hv n
  rw [neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary
    hv hT.le hboundary]
  change ‖((2 * F : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs]
  change |2 * F| ≤ 4 * b * E + |(4 / T) * L|
  calc
    |2 * F| = |2 * (F + (2 / T) * L) - (4 / T) * L| := by
      congr 1
      ring
    _ ≤ |2 * (F + (2 / T) * L)| + |(4 / T) * L| :=
      abs_sub _ _
    _ = 2 * |F + (2 / T) * L| + |(4 / T) * L| := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * ((2 * v / T ^ 2) * N) + |(4 / T) * L| := by
      gcongr
    _ = 4 * v * E + |(4 / T) * L| := by
      dsimp [E]
      ring
    _ ≤ 4 * b * E + |(4 / T) * L| := by
      gcongr

/-- On every compact interval of imaginary-axis observation heights strictly
above the safe contour, the selected static signed vertical remainder tends
uniformly to zero. -/
theorem tendstoUniformlyOn_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_quantitative_zero
    {a b : ℝ} (ha : 1 < a) :
    TendstoUniformlyOn
      (fun n : ℕ ↦ fun v : ℝ ↦
        -Complex.I *
          xiSpectralBlaschkeSignedVerticalRemainderWindow
            (quantitativeSpectralBoundaryTruncation n) 0
            ((v : ℂ) * Complex.I))
      (fun _ : ℝ ↦ (0 : ℂ)) atTop (Icc a b) := by
  let E : ℕ → ℝ := fun n ↦
    (1 / quantitativeSpectralBoundaryTruncation n ^ 2) *
      (∫ y : ℝ in (0 : ℝ)..1,
        ‖xiSpectralNegativeLogDerivative
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)‖)
  let M : ℕ → ℝ := fun n ↦
    (4 / quantitativeSpectralBoundaryTruncation n) *
      (∫ y : ℝ in (0 : ℝ)..1,
        (xiSpectralNegativeLogDerivative
          ((quantitativeSpectralBoundaryTruncation n : ℂ) +
            (y : ℂ) * Complex.I)).re)
  let Q : ℕ → ℝ := fun n ↦ 4 * b * E n + |M n|
  have hE : Tendsto E atTop (nhds 0) := by
    simpa [E] using
      tendsto_inv_sq_mul_intervalIntegral_norm_xiSpectralNegativeLogDerivative_quantitative_upper_zero
  have hM : Tendsto M atTop (nhds 0) := by
    simpa [M] using tendsto_staticContourLogDerivativeMain_quantitative_zero
  have hQ : Tendsto Q atTop (nhds 0) := by
    have hscaled : Tendsto (fun n : ℕ ↦ (4 * b) * E n)
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hE
    have habs : Tendsto (fun n : ℕ ↦ |M n|) atTop (nhds 0) := by
      simpa using hM.abs
    simpa [Q] using hscaled.add habs
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hsmall : ∀ᶠ n : ℕ in atTop, Q n < epsilon :=
    hQ.eventually (Iio_mem_nhds hepsilon)
  filter_upwards [hsmall] with n hn
  intro v hv
  have hva : a ≤ v := hv.1
  have hvone : 1 < v := ha.trans_le hva
  calc
    dist (0 : ℂ)
        (-Complex.I *
          xiSpectralBlaschkeSignedVerticalRemainderWindow
            (quantitativeSpectralBoundaryTruncation n) 0
            ((v : ℂ) * Complex.I)) =
        ‖-Complex.I *
          xiSpectralBlaschkeSignedVerticalRemainderWindow
            (quantitativeSpectralBoundaryTruncation n) 0
            ((v : ℂ) * Complex.I)‖ := by
      simp [dist_eq]
    _ ≤ Q n := by
      simpa [Q, E, M] using
        norm_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_quantitative_le
          hvone hv.2 n
    _ < epsilon := hn

/-- Removing the unit-modulus factor `-I`, the selected static signed
vertical remainder itself tends uniformly to zero on every such compact
imaginary-axis interval. -/
theorem tendstoUniformlyOn_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_quantitative_zero
    {a b : ℝ} (ha : 1 < a) :
    TendstoUniformlyOn
      (fun n : ℕ ↦ fun v : ℝ ↦
        xiSpectralBlaschkeSignedVerticalRemainderWindow
          (quantitativeSpectralBoundaryTruncation n) 0
          ((v : ℂ) * Complex.I))
      (fun _ : ℝ ↦ (0 : ℂ)) atTop (Icc a b) := by
  have hscaled :=
    tendstoUniformlyOn_neg_I_mul_xiSpectralBlaschkeSignedVerticalRemainderWindow_zero_imaginary_quantitative_zero
      (b := b) ha
  rw [Metric.tendstoUniformlyOn_iff] at hscaled ⊢
  intro epsilon hepsilon
  filter_upwards [hscaled epsilon hepsilon] with n hn
  intro v hv
  simpa [dist_eq] using hn v hv

end

end RiemannGaussian
