import RiemannGaussian.EtaCurrentMidpointCorrection

/-!
# Signed finite eta moment pairs for the actual midpoint correction

The completed pair retains the reflected channel and the conjugate-original
orientation as a complex quantity. Genuine product integrability identifies
its integral with the existing finite eta moments. Multiplication by the
physical midpoint raises either centered order, with the cutoff retained.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The signed completed pair, retaining the orientation of both channels. -/
def etaSignedCompletedPair (Ap Bp A B : ℂ) : ℂ :=
  Ap * starRingEnd ℂ Bp - starRingEnd ℂ A * B

/-- The two parity factors cancel exactly without conjugating away the
orientation of the original channel. -/
theorem etaSignedCompletedPair_eq_parity_pair (m : ℕ) (Ap Bp A B : ℂ) :
    etaSignedCompletedPair Ap Bp A B =
      Ap * starRingEnd ℂ Bp -
        ((-1 : ℂ) ^ m * starRingEnd ℂ A) *
          starRingEnd ℂ ((-1 : ℂ) ^ m * starRingEnd ℂ B) := by
  have he : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  simp only [etaSignedCompletedPair, map_mul, map_pow, map_neg, map_one,
    starRingEnd_apply, star_star]
  linear_combination (star A * B) * he

/-- Complex conjugation preserves genuine integrability of eta moment features. -/
theorem integrable_etaMoment_conj {μ : Measure ℝ} {f : ℝ → ℂ}
    (hf : Integrable f μ) : Integrable (fun t ↦ starRingEnd ℂ (f t)) μ := by
  apply ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf).congr
  filter_upwards with t
  exact Complex.conjCLE_apply _

/-- Genuine integration commutes with the real part of a complex moment-pair kernel. -/
theorem integral_etaMomentPair_re {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → ℂ}
    (hf : Integrable f μ) : (∫ p, (f p).re ∂μ) = (∫ p, f p ∂μ).re :=
  integral_re hf

/-- Integrable features give a genuinely integrable signed completed product. -/
theorem integrable_etaSignedCompletedPair {μ ν : Measure ℝ}
    {fp gp f g : ℝ → ℂ} (hfp : Integrable fp μ) (hgp : Integrable gp ν)
    (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun p : ℝ × ℝ ↦ etaSignedCompletedPair (fp p.1) (gp p.2) (f p.1) (g p.2))
      (μ.prod ν) :=
  (hfp.mul_prod (integrable_etaMoment_conj hgp)).sub
    ((integrable_etaMoment_conj hf).mul_prod hg)

/-- The signed completed product integrates to its complex arithmetic pair. -/
theorem integral_etaSignedCompletedPair {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    {fp gp f g : ℝ → ℂ} (hfp : Integrable fp μ) (hgp : Integrable gp ν)
    (hf : Integrable f μ) (hg : Integrable g ν) :
    (∫ p : ℝ × ℝ, etaSignedCompletedPair (fp p.1) (gp p.2) (f p.1) (g p.2) ∂μ.prod ν) =
      etaSignedCompletedPair (∫ t, fp t ∂μ) (∫ t, gp t ∂ν) (∫ t, f t ∂μ) (∫ t, g t ∂ν) := by
  unfold etaSignedCompletedPair
  rw [integral_sub (hfp.mul_prod (integrable_etaMoment_conj hgp))
      ((integrable_etaMoment_conj hf).mul_prod hg),
    integral_prod_mul (μ := μ) (ν := ν) fp (fun t ↦ starRingEnd ℂ (gp t)),
    integral_prod_mul (μ := μ) (ν := ν) (fun t ↦ starRingEnd ℂ (f t)) g,
    integral_conj, integral_conj]

/-- The existing finite centered eta moment with its actual completion factor. -/
def pairedEtaFiniteCompletedMoment (rho : NontrivialZetaZero) (N k : ℕ) : ℂ :=
  (pairedEtaXiCompletionFactor rho.1 * rho.1) *
    pairedEtaLogLaplaceMomentCutoffCenteredPartialSum k rho.1 N

/-- The literal integrand of the completed finite centered eta moment. -/
def pairedEtaFiniteCompletedMomentFeature (rho : NontrivialZetaZero) (N k : ℕ) (t : ℝ) : ℂ :=
  (pairedEtaXiCompletionFactor rho.1 * rho.1) *
    (((t - pairedEtaLogTailCutoff N : ℝ) : ℂ) ^ k * Complex.exp (-rho.1 * t))

/-- Every finite completed moment feature is integrable on the actual prefix. -/
theorem integrable_pairedEtaFiniteCompletedMomentFeature (rho : NontrivialZetaZero) (N k : ℕ) :
    Integrable (pairedEtaFiniteCompletedMomentFeature rho N k) (pairedEtaFiniteLogMeasure N) :=
  (integrable_centered_cpow_mul_cexp_neg_mul_pairedEtaFiniteLogMeasure
    k N rho.1 (pairedEtaLogTailCutoff N)).const_mul _

/-- The finite feature integrates to the existing arithmetic moment. -/
theorem integral_pairedEtaFiniteCompletedMomentFeature (rho : NontrivialZetaZero) (N k : ℕ) :
    (∫ t, pairedEtaFiniteCompletedMomentFeature rho N k t ∂pairedEtaFiniteLogMeasure N) =
      pairedEtaFiniteCompletedMoment rho N k := by
  unfold pairedEtaFiniteCompletedMomentFeature pairedEtaFiniteCompletedMoment
  rw [integral_const_mul, ← pairedEtaLogLaplaceMomentCutoffCenteredPartialSum_eq_integral_finiteLogMeasure]

/-- Raising a finite centered order multiplies its feature by the real centered time. -/
theorem pairedEtaFiniteCompletedMomentFeature_succ (rho : NontrivialZetaZero) (N k : ℕ) (t : ℝ) :
    pairedEtaFiniteCompletedMomentFeature rho N (k + 1) t =
      (t - pairedEtaLogTailCutoff N : ℝ) * pairedEtaFiniteCompletedMomentFeature rho N k t := by
  unfold pairedEtaFiniteCompletedMomentFeature
  rw [pow_succ]
  ring

/-- The complete complex finite arithmetic pair of two centered orders. -/
def pairedEtaFiniteCompletedMomentPair (rho : NontrivialZetaZero) (N k l : ℕ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaFiniteCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N k)
    (pairedEtaFiniteCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N l)
    (pairedEtaFiniteCompletedMoment rho N k) (pairedEtaFiniteCompletedMoment rho N l)

/-- The literal complex signed product kernel of the finite arithmetic pair. -/
def pairedEtaFiniteCompletedMomentPairKernel (rho : NontrivialZetaZero) (N k l : ℕ) (p : ℝ × ℝ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaFiniteCompletedMomentFeature (NontrivialZetaZero.conjugatePartner rho) N k p.1)
    (pairedEtaFiniteCompletedMomentFeature (NontrivialZetaZero.conjugatePartner rho) N l p.2)
    (pairedEtaFiniteCompletedMomentFeature rho N k p.1) (pairedEtaFiniteCompletedMomentFeature rho N l p.2)

/-- The complex signed moment kernel is integrable on the actual product prefix. -/
theorem integrable_pairedEtaFiniteCompletedMomentPairKernel (rho : NontrivialZetaZero) (N k l : ℕ) :
    Integrable (pairedEtaFiniteCompletedMomentPairKernel rho N k l)
      ((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)) :=
  integrable_etaSignedCompletedPair
    (integrable_pairedEtaFiniteCompletedMomentFeature _ _ _)
    (integrable_pairedEtaFiniteCompletedMomentFeature _ _ _)
    (integrable_pairedEtaFiniteCompletedMomentFeature _ _ _)
    (integrable_pairedEtaFiniteCompletedMomentFeature _ _ _)

/-- Genuine product integration recovers the full signed arithmetic pair. -/
theorem integral_pairedEtaFiniteCompletedMomentPairKernel (rho : NontrivialZetaZero) (N k l : ℕ) :
    (∫ p, pairedEtaFiniteCompletedMomentPairKernel rho N k l p
      ∂((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N))) =
      pairedEtaFiniteCompletedMomentPair rho N k l := by
  unfold pairedEtaFiniteCompletedMomentPairKernel
  rw [integral_etaSignedCompletedPair
    (integrable_pairedEtaFiniteCompletedMomentFeature _ _ _)
    (integrable_pairedEtaFiniteCompletedMomentFeature _ _ _)
    (integrable_pairedEtaFiniteCompletedMomentFeature _ _ _)
    (integrable_pairedEtaFiniteCompletedMomentFeature _ _ _)]
  simp only [integral_pairedEtaFiniteCompletedMomentFeature, pairedEtaFiniteCompletedMomentPair]

/-- Multiplying the actual complex kernel by its physical midpoint raises
either centered order and retains the cutoff term exactly. -/
theorem pairedEtaFiniteCompletedMomentPairKernel_midpoint (rho : NontrivialZetaZero) (N k l : ℕ) (p : ℝ × ℝ) :
    pairedEtaFiniteCompletedMomentPairKernel rho N k l p * ((p.1 + p.2) / 2 : ℝ) =
      (pairedEtaLogTailCutoff N : ℂ) * pairedEtaFiniteCompletedMomentPairKernel rho N k l p +
        (pairedEtaFiniteCompletedMomentPairKernel rho N (k + 1) l p +
          pairedEtaFiniteCompletedMomentPairKernel rho N k (l + 1) p) / 2 := by
  unfold pairedEtaFiniteCompletedMomentPairKernel
  simp only [pairedEtaFiniteCompletedMomentFeature_succ, etaSignedCompletedPair,
    map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- The midpoint-weighted complex moment kernel is genuinely integrable. -/
theorem integrable_pairedEtaFiniteCompletedMomentPairKernel_midpoint
    (rho : NontrivialZetaZero) (N k l : ℕ) :
    Integrable (fun p ↦ pairedEtaFiniteCompletedMomentPairKernel rho N k l p * ((p.1 + p.2) / 2 : ℝ))
      ((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)) := by
  apply ((integrable_pairedEtaFiniteCompletedMomentPairKernel rho N k l).const_mul
    (pairedEtaLogTailCutoff N : ℂ) |>.add
      (((integrable_pairedEtaFiniteCompletedMomentPairKernel rho N (k + 1) l).add
        (integrable_pairedEtaFiniteCompletedMomentPairKernel rho N k (l + 1))).div_const 2)).congr
  filter_upwards with p
  exact (pairedEtaFiniteCompletedMomentPairKernel_midpoint rho N k l p).symm

/-- The physical midpoint coefficient evaluates to the two raised finite
eta moment pairs, with the original complex orientation preserved. -/
theorem integral_pairedEtaFiniteCompletedMomentPairKernel_midpoint
    (rho : NontrivialZetaZero) (N k l : ℕ) :
    (∫ p, pairedEtaFiniteCompletedMomentPairKernel rho N k l p * ((p.1 + p.2) / 2 : ℝ)
      ∂((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N))) =
      (pairedEtaLogTailCutoff N : ℂ) * pairedEtaFiniteCompletedMomentPair rho N k l +
        (pairedEtaFiniteCompletedMomentPair rho N (k + 1) l +
          pairedEtaFiniteCompletedMomentPair rho N k (l + 1)) / 2 := by
  simp_rw [pairedEtaFiniteCompletedMomentPairKernel_midpoint]
  rw [integral_add
      (f := fun p ↦ (pairedEtaLogTailCutoff N : ℂ) * pairedEtaFiniteCompletedMomentPairKernel rho N k l p)
      (g := fun p ↦ (pairedEtaFiniteCompletedMomentPairKernel rho N (k + 1) l p +
        pairedEtaFiniteCompletedMomentPairKernel rho N k (l + 1) p) / 2)
      ((integrable_pairedEtaFiniteCompletedMomentPairKernel rho N k l).const_mul _)
      (((integrable_pairedEtaFiniteCompletedMomentPairKernel rho N (k + 1) l).add
        (integrable_pairedEtaFiniteCompletedMomentPairKernel rho N k (l + 1))).div_const 2),
    integral_const_mul, integral_div, integral_add
      (f := fun p ↦ pairedEtaFiniteCompletedMomentPairKernel rho N (k + 1) l p)
      (g := fun p ↦ pairedEtaFiniteCompletedMomentPairKernel rho N k (l + 1) p)
      (integrable_pairedEtaFiniteCompletedMomentPairKernel rho N (k + 1) l)
      (integrable_pairedEtaFiniteCompletedMomentPairKernel rho N k (l + 1))]
  simp only [integral_pairedEtaFiniteCompletedMomentPairKernel]

end

end RiemannGaussian
