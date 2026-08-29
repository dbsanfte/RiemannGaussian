import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaGaussianSigmaMoments
import Mathlib.MeasureTheory.Integral.MeanInequalities

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Cauchy--Schwarz for the first two logarithmic-time moments of the finite
eta Gaussian--Laplace kernel. -/
theorem integral_firstSigmaMoment_sq_le_zero_mul_second
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    (∫ p : ℝ × ℝ, (p.1 + p.2) *
        pairedEtaFiniteGaussianLaplaceKernel sigma tau p
        ∂(pairedEtaFiniteLogMeasure N).prod
          (pairedEtaFiniteLogMeasure N)) ^ 2 ≤
      (∫ p : ℝ × ℝ,
          pairedEtaFiniteGaussianLaplaceKernel sigma tau p
          ∂(pairedEtaFiniteLogMeasure N).prod
            (pairedEtaFiniteLogMeasure N)) *
        ∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 *
          pairedEtaFiniteGaussianLaplaceKernel sigma tau p
          ∂(pairedEtaFiniteLogMeasure N).prod
            (pairedEtaFiniteLogMeasure N) := by
  let μ := (pairedEtaFiniteLogMeasure N).prod
    (pairedEtaFiniteLogMeasure N)
  let w : ℝ × ℝ → ℝ :=
    pairedEtaFiniteGaussianLaplaceKernel sigma tau
  let q : ℝ × ℝ → ℝ := fun p => p.1 + p.2
  have hwpos : ∀ p, 0 < w p := fun p => by
    exact pairedEtaFiniteGaussianLaplaceKernel_pos sigma tau p
  have hqnonneg : ∀ᵐ p ∂μ, 0 ≤ q p := by
    simpa only [μ, q] using
      (ae_nonneg_pairedEtaFiniteLogMeasure_prod N).mono
        (fun p hp => add_nonneg hp.1 hp.2)
  have hwint : Integrable w μ := by
    simpa only [μ, w] using
      integrable_pairedEtaFiniteGaussianLaplaceKernel N sigma htau
  have hq2wint : Integrable (fun p => q p ^ 2 * w p) μ := by
    simpa only [μ, q, w] using
      integrable_secondSigmaMoment_pairedEtaFiniteGaussianLaplaceKernel
        N sigma htau
  have hf : MemLp (fun p => Real.sqrt (w p)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (show AEStronglyMeasurable (fun p => Real.sqrt (w p)) μ by
        exact (show Continuous (fun p : ℝ × ℝ => Real.sqrt (w p)) by
          unfold w pairedEtaFiniteGaussianLaplaceKernel
          fun_prop).aestronglyMeasurable)).2
    apply hwint.congr
    exact Eventually.of_forall fun p => (Real.sq_sqrt (hwpos p).le).symm
  have hg : MemLp (fun p => q p * Real.sqrt (w p)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      (show AEStronglyMeasurable
          (fun p => q p * Real.sqrt (w p)) μ by
        exact (show Continuous
            (fun p : ℝ × ℝ => q p * Real.sqrt (w p)) by
          unfold q w pairedEtaFiniteGaussianLaplaceKernel
          fun_prop).aestronglyMeasurable)).2
    apply hq2wint.congr
    exact Eventually.of_forall fun p => by
      change q p ^ 2 * w p = (q p * Real.sqrt (w p)) ^ 2
      rw [mul_pow, Real.sq_sqrt (hwpos p).le]
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (Eventually.of_forall fun p => Real.sqrt_nonneg (w p))
    (hqnonneg.mono fun p hp => mul_nonneg hp (Real.sqrt_nonneg (w p)))
    (by simpa using hf) (by simpa using hg)
  have hleft :
      (∫ p, Real.sqrt (w p) * (q p * Real.sqrt (w p)) ∂μ) =
        ∫ p, q p * w p ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      change Real.sqrt (w p) * (q p * Real.sqrt (w p)) = q p * w p
      calc
        Real.sqrt (w p) * (q p * Real.sqrt (w p)) =
            q p * Real.sqrt (w p) ^ 2 := by ring
        _ = q p * w p := by rw [Real.sq_sqrt (hwpos p).le]
  have hzero :
      (∫ p, Real.sqrt (w p) ^ (2 : ℝ) ∂μ) = ∫ p, w p ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      change Real.sqrt (w p) ^ (2 : ℝ) = w p
      rw [Real.rpow_two, Real.sq_sqrt (hwpos p).le]
  have hsecond :
      (∫ p, (q p * Real.sqrt (w p)) ^ (2 : ℝ) ∂μ) =
        ∫ p, q p ^ 2 * w p ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by
      change (q p * Real.sqrt (w p)) ^ (2 : ℝ) = q p ^ 2 * w p
      rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hwpos p).le]
  rw [hleft, hzero, hsecond, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow] at hholder
  have hIzero : 0 ≤ ∫ p, w p ∂μ :=
    integral_nonneg fun p => (hwpos p).le
  have hIfirst : 0 ≤ ∫ p, q p * w p ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hqnonneg] with p hp
    exact mul_nonneg hp (hwpos p).le
  have hIsecond : 0 ≤ ∫ p, q p ^ 2 * w p ∂μ :=
    integral_nonneg fun p => mul_nonneg (sq_nonneg _) (hwpos p).le
  have hsquare := (sq_le_sq₀ hIfirst
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 hholder
  rw [mul_pow, Real.sq_sqrt hIzero, Real.sq_sqrt hIsecond] at hsquare
  simpa only [μ, q, w] using hsquare

/-- The scaled first sigma moment satisfies the exact Gram moment-determinant
inequality. -/
theorem pairedEtaFiniteGaussianLaplaceFirstSigmaMoment_sq_le
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    pairedEtaFiniteGaussianLaplaceFirstSigmaMoment N sigma tau ^ 2 ≤
      pairedEtaFiniteGaussianLaplaceGram N sigma tau *
        pairedEtaFiniteGaussianLaplaceSecondSigmaMoment N sigma tau := by
  have h := integral_firstSigmaMoment_sq_le_zero_mul_second
    N sigma htau
  unfold pairedEtaFiniteGaussianLaplaceFirstSigmaMoment
    pairedEtaFiniteGaussianLaplaceSecondSigmaMoment
    pairedEtaFiniteGaussianLaplaceGram
  calc
    (Real.sqrt (Real.pi / tau) *
        ∫ p : ℝ × ℝ, (p.1 + p.2) *
          pairedEtaFiniteGaussianLaplaceKernel sigma tau p
          ∂(pairedEtaFiniteLogMeasure N).prod
            (pairedEtaFiniteLogMeasure N)) ^ 2 =
      Real.sqrt (Real.pi / tau) ^ 2 *
        (∫ p : ℝ × ℝ, (p.1 + p.2) *
          pairedEtaFiniteGaussianLaplaceKernel sigma tau p
          ∂(pairedEtaFiniteLogMeasure N).prod
            (pairedEtaFiniteLogMeasure N)) ^ 2 := by ring
    _ ≤ Real.sqrt (Real.pi / tau) ^ 2 *
        ((∫ p : ℝ × ℝ,
            pairedEtaFiniteGaussianLaplaceKernel sigma tau p
            ∂(pairedEtaFiniteLogMeasure N).prod
              (pairedEtaFiniteLogMeasure N)) *
          ∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 *
            pairedEtaFiniteGaussianLaplaceKernel sigma tau p
            ∂(pairedEtaFiniteLogMeasure N).prod
              (pairedEtaFiniteLogMeasure N)) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = (Real.sqrt (Real.pi / tau) *
          ∫ p : ℝ × ℝ,
            pairedEtaFiniteGaussianLaplaceKernel sigma tau p
            ∂(pairedEtaFiniteLogMeasure N).prod
              (pairedEtaFiniteLogMeasure N)) *
        (Real.sqrt (Real.pi / tau) *
          ∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 *
            pairedEtaFiniteGaussianLaplaceKernel sigma tau p
            ∂(pairedEtaFiniteLogMeasure N).prod
              (pairedEtaFiniteLogMeasure N)) := by ring

/-- Every nonempty finite eta Gaussian--Laplace Gram value is strictly
positive at positive Gaussian time. -/
theorem pairedEtaFiniteGaussianLaplaceGram_pos
    {N : ℕ} (hN : 0 < N) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    0 < pairedEtaFiniteGaussianLaplaceGram N sigma tau := by
  have hstrict :=
    strictAnti_pairedEtaFiniteGaussianLaplaceGram_sigma hN htau
      (show sigma < sigma + 1 by linarith)
  exact (pairedEtaFiniteGaussianLaplaceGram_nonneg
    N (sigma + 1) tau).trans_lt hstrict

/-- Exact first derivative of the logarithm of a nonempty finite eta
Gaussian--Laplace Gram profile. -/
theorem hasDerivAt_log_pairedEtaFiniteGaussianLaplaceGram_sigma
    {N : ℕ} (hN : 0 < N) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    HasDerivAt
      (fun r : ℝ => Real.log
        (pairedEtaFiniteGaussianLaplaceGram N r tau))
      (-pairedEtaFiniteGaussianLaplaceFirstSigmaMoment N sigma tau /
        pairedEtaFiniteGaussianLaplaceGram N sigma tau) sigma := by
  exact (hasDerivAt_pairedEtaFiniteGaussianLaplaceGram_sigma
    N sigma htau).log
      (pairedEtaFiniteGaussianLaplaceGram_pos hN sigma htau).ne'

/-- The derivative of the logarithmic Gram slope is the normalized moment
determinant. -/
theorem hasDerivAt_deriv_log_pairedEtaFiniteGaussianLaplaceGram_sigma
    {N : ℕ} (hN : 0 < N) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    HasDerivAt
      (fun r : ℝ => deriv
        (fun q : ℝ => Real.log
          (pairedEtaFiniteGaussianLaplaceGram N q tau)) r)
      ((pairedEtaFiniteGaussianLaplaceSecondSigmaMoment N sigma tau *
          pairedEtaFiniteGaussianLaplaceGram N sigma tau -
        pairedEtaFiniteGaussianLaplaceFirstSigmaMoment N sigma tau ^ 2) /
        pairedEtaFiniteGaussianLaplaceGram N sigma tau ^ 2) sigma := by
  rw [show
    (fun r : ℝ => deriv
      (fun q : ℝ => Real.log
        (pairedEtaFiniteGaussianLaplaceGram N q tau)) r) =
      (fun r : ℝ =>
        -pairedEtaFiniteGaussianLaplaceFirstSigmaMoment N r tau /
          pairedEtaFiniteGaussianLaplaceGram N r tau) by
    funext r
    exact (hasDerivAt_log_pairedEtaFiniteGaussianLaplaceGram_sigma
      hN r htau).deriv]
  have hquot :=
    (hasDerivAt_neg_pairedEtaFiniteGaussianLaplaceFirstSigmaMoment
      N sigma htau).div
      (hasDerivAt_pairedEtaFiniteGaussianLaplaceGram_sigma
        N sigma htau)
      (pairedEtaFiniteGaussianLaplaceGram_pos hN sigma htau).ne'
  apply hquot.congr_deriv
  ring

/-- The logarithmic finite eta Gaussian--Laplace Gram profile is
differentiable on the whole real tilt line. -/
theorem differentiable_log_pairedEtaFiniteGaussianLaplaceGram_sigma
    {N : ℕ} (hN : 0 < N) {tau : ℝ} (htau : 0 < tau) :
    Differentiable ℝ
      (fun sigma : ℝ => Real.log
        (pairedEtaFiniteGaussianLaplaceGram N sigma tau)) :=
  fun sigma =>
    (hasDerivAt_log_pairedEtaFiniteGaussianLaplaceGram_sigma
      hN sigma htau).differentiableAt

/-- The derivative of the logarithmic finite eta Gaussian--Laplace Gram
profile is differentiable on the whole real tilt line. -/
theorem differentiable_deriv_log_pairedEtaFiniteGaussianLaplaceGram_sigma
    {N : ℕ} (hN : 0 < N) {tau : ℝ} (htau : 0 < tau) :
    Differentiable ℝ
      (deriv (fun sigma : ℝ => Real.log
        (pairedEtaFiniteGaussianLaplaceGram N sigma tau))) :=
  fun sigma =>
    (hasDerivAt_deriv_log_pairedEtaFiniteGaussianLaplaceGram_sigma
      hN sigma htau).differentiableAt

/-- Exact second derivative of the logarithmic finite eta Gaussian--Laplace
Gram profile. -/
theorem deriv_deriv_log_pairedEtaFiniteGaussianLaplaceGram_sigma
    {N : ℕ} (hN : 0 < N) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    deriv
      (fun r : ℝ => deriv
        (fun q : ℝ => Real.log
          (pairedEtaFiniteGaussianLaplaceGram N q tau)) r) sigma =
      (pairedEtaFiniteGaussianLaplaceSecondSigmaMoment N sigma tau *
          pairedEtaFiniteGaussianLaplaceGram N sigma tau -
        pairedEtaFiniteGaussianLaplaceFirstSigmaMoment N sigma tau ^ 2) /
        pairedEtaFiniteGaussianLaplaceGram N sigma tau ^ 2 :=
  (hasDerivAt_deriv_log_pairedEtaFiniteGaussianLaplaceGram_sigma
    hN sigma htau).deriv

/-- The finite eta Gaussian--Laplace Gram profile is log-convex in its real
tilt. This is the Cauchy--Schwarz consequence of its positive Laplace measure;
it does not provide complementary eta symmetry. -/
theorem convexOn_log_pairedEtaFiniteGaussianLaplaceGram_sigma
    {N : ℕ} (hN : 0 < N) {tau : ℝ} (htau : 0 < tau) :
    ConvexOn ℝ univ
      (fun sigma : ℝ => Real.log
        (pairedEtaFiniteGaussianLaplaceGram N sigma tau)) := by
  apply convexOn_univ_of_deriv2_nonneg
    (differentiable_log_pairedEtaFiniteGaussianLaplaceGram_sigma hN htau)
    (differentiable_deriv_log_pairedEtaFiniteGaussianLaplaceGram_sigma
      hN htau)
  intro sigma
  simp only [Nat.iterate]
  rw [deriv_deriv_log_pairedEtaFiniteGaussianLaplaceGram_sigma
    hN sigma htau]
  apply div_nonneg
  · rw [sub_nonneg]
    simpa only [mul_comm] using
      pairedEtaFiniteGaussianLaplaceFirstSigmaMoment_sq_le N sigma htau
  · exact sq_nonneg _

end

end RiemannGaussian
