import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteGaussianLaplaceGram
import Mathlib.Analysis.Convex.Deriv

/-!
# Sigma moments of the finite eta Gaussian--Laplace Gram form

The positive double-integral representation makes its dependence on the real
tilt explicit. This module differentiates that genuine integral and records
the first two logarithmic-time moments. These generic sign and convexity facts
do not supply the missing completed `sigma ↦ 1 - sigma` symmetry.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Every polynomial logarithmic-time moment is integrable against the finite
eta measure. -/
theorem integrable_pow_mul_rexp_neg_mul_pairedEtaFiniteLogMeasure
    (N k : ℕ) (sigma : ℝ) :
    Integrable (fun t : ℝ => t ^ k * Real.exp (-sigma * t))
      (pairedEtaFiniteLogMeasure N) := by
  unfold pairedEtaFiniteLogMeasure
  rw [integrable_finsetSum_measure]
  intro n hn
  change IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-sigma * t))
    (Ioc (Real.log (2 * n + 1)) (Real.log (2 * n + 2)))
  apply IntegrableOn.mono_set
    ((show Continuous (fun t : ℝ => t ^ k * Real.exp (-sigma * t)) by
      fun_prop).continuousOn.integrableOn_Icc)
  exact Ioc_subset_Icc_self

/-- The finite eta logarithmic measure is supported on nonnegative time. -/
theorem ae_nonneg_pairedEtaFiniteLogMeasure (N : ℕ) :
    ∀ᵐ t : ℝ ∂pairedEtaFiniteLogMeasure N, 0 ≤ t := by
  unfold pairedEtaFiniteLogMeasure
  rw [ae_finsetSum_measure_iff]
  intro n hn
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hlog : 0 ≤ Real.log (2 * n + 1) := by
    apply Real.log_nonneg
    norm_num
  exact hlog.trans ht.1.le

/-- The finite eta logarithmic measure is almost everywhere supported at
strictly positive time. -/
theorem ae_pos_pairedEtaFiniteLogMeasure (N : ℕ) :
    ∀ᵐ t : ℝ ∂pairedEtaFiniteLogMeasure N, 0 < t := by
  unfold pairedEtaFiniteLogMeasure
  rw [ae_finsetSum_measure_iff]
  intro n hn
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hlog : 0 ≤ Real.log (2 * n + 1) := by
    apply Real.log_nonneg
    norm_num
  exact hlog.trans_lt ht.1

/-- A nonempty finite eta logarithmic measure has positive total mass. -/
theorem pairedEtaFiniteLogMeasure_univ_pos
    {N : ℕ} (hN : 0 < N) :
    0 < pairedEtaFiniteLogMeasure N univ := by
  unfold pairedEtaFiniteLogMeasure
  rw [Measure.finsetSum_apply]
  let f : ℕ → ℝ≥0∞ := fun n =>
    (volume.restrict
      (Ioc (Real.log (2 * n + 1)) (Real.log (2 * n + 2)))) univ
  change 0 < ∑ n ∈ Finset.range N, f n
  have hterm : 0 < f 0 := by
    dsimp [f]
    simp [Measure.restrict_apply, Real.volume_Ioc,
      Real.log_pos one_lt_two]
  exact hterm.trans_le <| Finset.single_le_sum
    (f := f)
    (fun n hn => bot_le) (Finset.mem_range.mpr hN)

/-- A nonempty finite eta product measure has positive total mass. -/
theorem pairedEtaFiniteLogMeasure_prod_univ_pos
    {N : ℕ} (hN : 0 < N) :
    0 < ((pairedEtaFiniteLogMeasure N).prod
      (pairedEtaFiniteLogMeasure N)) univ := by
  rw [← univ_prod_univ, Measure.prod_prod]
  exact ENNReal.mul_pos (pairedEtaFiniteLogMeasure_univ_pos hN).ne'
    (pairedEtaFiniteLogMeasure_univ_pos hN).ne'

private theorem integral_pos_of_ae_pos_of_measure_univ_pos
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hpos : ∀ᵐ x ∂μ, 0 < f x) (hint : Integrable f μ)
    (hμ : 0 < μ univ) :
    0 < ∫ x, f x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg_ae
    (hpos.mono fun x hx => hx.le) hint).2
  calc
    0 < μ univ := hμ
    _ = μ (Function.support f) := by
      apply measure_congr
      filter_upwards [hpos] with x hx
      apply propext
      constructor
      · intro h
        exact hx.ne'
      · intro h
        trivial

/-- Both coordinates of the finite eta product measure are almost everywhere
nonnegative. -/
theorem ae_nonneg_pairedEtaFiniteLogMeasure_prod (N : ℕ) :
    ∀ᵐ p : ℝ × ℝ
      ∂(pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N),
      0 ≤ p.1 ∧ 0 ≤ p.2 := by
  rw [Measure.ae_prod_iff_ae_ae (by measurability)]
  filter_upwards [ae_nonneg_pairedEtaFiniteLogMeasure N] with t ht
  filter_upwards [ae_nonneg_pairedEtaFiniteLogMeasure N] with u hu
  exact ⟨ht, hu⟩

/-- The undamped first two-time Laplace moment is integrable over the finite
eta product measure. -/
theorem integrable_sum_mul_rexp_neg_mul_pairedEtaFiniteLogMeasure_prod
    (N : ℕ) (sigma : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      (p.1 + p.2) * Real.exp (-sigma * (p.1 + p.2)))
      ((pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N)) := by
  have hzero : Integrable (fun t : ℝ => Real.exp (-sigma * t))
      (pairedEtaFiniteLogMeasure N) := by
    simpa using
      integrable_pow_mul_rexp_neg_mul_pairedEtaFiniteLogMeasure N 0 sigma
  have hone : Integrable (fun t : ℝ => t * Real.exp (-sigma * t))
      (pairedEtaFiniteLogMeasure N) := by
    simpa using
      integrable_pow_mul_rexp_neg_mul_pairedEtaFiniteLogMeasure N 1 sigma
  have hsum := (hone.mul_prod hzero).add (hzero.mul_prod hone)
  apply hsum.congr
  exact Eventually.of_forall fun p => by
    change p.1 * Real.exp (-sigma * p.1) * Real.exp (-sigma * p.2) +
        Real.exp (-sigma * p.1) *
          (p.2 * Real.exp (-sigma * p.2)) =
      (p.1 + p.2) * Real.exp (-sigma * (p.1 + p.2))
    rw [show Real.exp (-sigma * (p.1 + p.2)) =
        Real.exp (-sigma * p.1) * Real.exp (-sigma * p.2) by
      rw [← Real.exp_add]
      congr 1
      ring]
    ring

/-- The undamped second two-time Laplace moment is integrable over the finite
eta product measure. -/
theorem integrable_sq_sum_mul_rexp_neg_mul_pairedEtaFiniteLogMeasure_prod
    (N : ℕ) (sigma : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      (p.1 + p.2) ^ 2 * Real.exp (-sigma * (p.1 + p.2)))
      ((pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N)) := by
  have hzero : Integrable (fun t : ℝ => Real.exp (-sigma * t))
      (pairedEtaFiniteLogMeasure N) := by
    simpa using
      integrable_pow_mul_rexp_neg_mul_pairedEtaFiniteLogMeasure N 0 sigma
  have hone : Integrable (fun t : ℝ => t * Real.exp (-sigma * t))
      (pairedEtaFiniteLogMeasure N) := by
    simpa using
      integrable_pow_mul_rexp_neg_mul_pairedEtaFiniteLogMeasure N 1 sigma
  have htwo : Integrable (fun t : ℝ => t ^ 2 * Real.exp (-sigma * t))
      (pairedEtaFiniteLogMeasure N) :=
    integrable_pow_mul_rexp_neg_mul_pairedEtaFiniteLogMeasure N 2 sigma
  have hsum := ((htwo.mul_prod hzero).add
    ((hone.mul_prod hone).const_mul 2)).add (hzero.mul_prod htwo)
  apply hsum.congr
  exact Eventually.of_forall fun p => by
    change p.1 ^ 2 * Real.exp (-sigma * p.1) *
          Real.exp (-sigma * p.2) +
        2 * (p.1 * Real.exp (-sigma * p.1) *
          (p.2 * Real.exp (-sigma * p.2))) +
        Real.exp (-sigma * p.1) *
          (p.2 ^ 2 * Real.exp (-sigma * p.2)) =
      (p.1 + p.2) ^ 2 * Real.exp (-sigma * (p.1 + p.2))
    rw [show Real.exp (-sigma * (p.1 + p.2)) =
        Real.exp (-sigma * p.1) * Real.exp (-sigma * p.2) by
      rw [← Real.exp_add]
      congr 1
      ring]
    ring

/-- First logarithmic-time moment of the positive Gaussian--Laplace Gram
kernel. -/
def pairedEtaFiniteGaussianLaplaceFirstSigmaMoment
    (N : ℕ) (sigma tau : ℝ) : ℝ :=
  Real.sqrt (Real.pi / tau) *
    ∫ p : ℝ × ℝ, (p.1 + p.2) *
      pairedEtaFiniteGaussianLaplaceKernel sigma tau p
      ∂(pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N)

/-- Second logarithmic-time moment of the positive Gaussian--Laplace Gram
kernel. -/
def pairedEtaFiniteGaussianLaplaceSecondSigmaMoment
    (N : ℕ) (sigma tau : ℝ) : ℝ :=
  Real.sqrt (Real.pi / tau) *
    ∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 *
      pairedEtaFiniteGaussianLaplaceKernel sigma tau p
      ∂(pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N)

/-- Pointwise derivative of the Gaussian--Laplace kernel with respect to its
real tilt. -/
theorem hasDerivAt_pairedEtaFiniteGaussianLaplaceKernel_sigma
    (sigma tau : ℝ) (p : ℝ × ℝ) :
    HasDerivAt
      (fun r : ℝ => pairedEtaFiniteGaussianLaplaceKernel r tau p)
      (-(p.1 + p.2) *
        pairedEtaFiniteGaussianLaplaceKernel sigma tau p) sigma := by
  have hlinear : HasDerivAt
      (fun r : ℝ => -r * (p.1 + p.2)) (-(p.1 + p.2)) sigma := by
    simpa using (hasDerivAt_id sigma).neg.mul_const (p.1 + p.2)
  unfold pairedEtaFiniteGaussianLaplaceKernel
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (hlinear.exp.mul_const
      (Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau))))

/-- Pointwise derivative of the negative first sigma-moment integrand. -/
theorem hasDerivAt_neg_sum_mul_pairedEtaFiniteGaussianLaplaceKernel_sigma
    (sigma tau : ℝ) (p : ℝ × ℝ) :
    HasDerivAt
      (fun r : ℝ => -(p.1 + p.2) *
        pairedEtaFiniteGaussianLaplaceKernel r tau p)
      ((p.1 + p.2) ^ 2 *
        pairedEtaFiniteGaussianLaplaceKernel sigma tau p) sigma := by
  have h := (hasDerivAt_pairedEtaFiniteGaussianLaplaceKernel_sigma
    sigma tau p).const_mul (-(p.1 + p.2))
  apply h.congr_deriv
  ring

/-- The first sigma-moment kernel is integrable at positive Gaussian time. -/
theorem integrable_firstSigmaMoment_pairedEtaFiniteGaussianLaplaceKernel
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Integrable (fun p : ℝ × ℝ => (p.1 + p.2) *
      pairedEtaFiniteGaussianLaplaceKernel sigma tau p)
      ((pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N)) := by
  have hmajor :=
    integrable_sum_mul_rexp_neg_mul_pairedEtaFiniteLogMeasure_prod N sigma
  apply hmajor.mono
  · exact (show Continuous (fun p : ℝ × ℝ => (p.1 + p.2) *
        pairedEtaFiniteGaussianLaplaceKernel sigma tau p) by
      unfold pairedEtaFiniteGaussianLaplaceKernel
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_nonneg_pairedEtaFiniteLogMeasure_prod N] with p hp
    have hsum : 0 ≤ p.1 + p.2 := add_nonneg hp.1 hp.2
    have hquad : -(p.1 - p.2) ^ 2 / (4 * tau) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
    have hdamp : Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hquad
    unfold pairedEtaFiniteGaussianLaplaceKernel
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        hsum (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)),
      abs_of_nonneg (mul_nonneg hsum (Real.exp_pos _).le)]
    rw [← mul_assoc]
    exact mul_le_of_le_one_right
      (mul_nonneg hsum (Real.exp_pos _).le) hdamp

/-- The second sigma-moment kernel is integrable at positive Gaussian time. -/
theorem integrable_secondSigmaMoment_pairedEtaFiniteGaussianLaplaceKernel
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Integrable (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2 *
      pairedEtaFiniteGaussianLaplaceKernel sigma tau p)
      ((pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N)) := by
  have hmajor :=
    integrable_sq_sum_mul_rexp_neg_mul_pairedEtaFiniteLogMeasure_prod N sigma
  apply hmajor.mono
  · exact (show Continuous (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2 *
        pairedEtaFiniteGaussianLaplaceKernel sigma tau p) by
      unfold pairedEtaFiniteGaussianLaplaceKernel
      fun_prop).aestronglyMeasurable
  · filter_upwards [ae_nonneg_pairedEtaFiniteLogMeasure_prod N] with p hp
    have hsq : 0 ≤ (p.1 + p.2) ^ 2 := sq_nonneg _
    have hquad : -(p.1 - p.2) ^ 2 / (4 * tau) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
    have hdamp : Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hquad
    unfold pairedEtaFiniteGaussianLaplaceKernel
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg
        hsq (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)),
      abs_of_nonneg (mul_nonneg hsq (Real.exp_pos _).le)]
    rw [← mul_assoc]
    exact mul_le_of_le_one_right
      (mul_nonneg hsq (Real.exp_pos _).le) hdamp

private theorem hasDerivAt_integral_pairedEtaFiniteGaussianLaplaceKernel_sigma
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    HasDerivAt
      (fun r : ℝ => ∫ p : ℝ × ℝ,
        pairedEtaFiniteGaussianLaplaceKernel r tau p
        ∂(pairedEtaFiniteLogMeasure N).prod
          (pairedEtaFiniteLogMeasure N))
      (∫ p : ℝ × ℝ, -(p.1 + p.2) *
        pairedEtaFiniteGaussianLaplaceKernel sigma tau p
        ∂(pairedEtaFiniteLogMeasure N).prod
          (pairedEtaFiniteLogMeasure N)) sigma := by
  let s : Set ℝ := Ioo (sigma - 1) (sigma + 1)
  let bound : ℝ × ℝ → ℝ := fun p =>
    (p.1 + p.2) * Real.exp (-(sigma - 1) * (p.1 + p.2))
  have hs : s ∈ 𝓝 sigma := by
    apply Ioo_mem_nhds
    · linarith
    · linarith
  have hFmeas : ∀ᶠ r : ℝ in 𝓝 sigma,
      AEStronglyMeasurable
        (pairedEtaFiniteGaussianLaplaceKernel r tau)
        ((pairedEtaFiniteLogMeasure N).prod
          (pairedEtaFiniteLogMeasure N)) :=
    Eventually.of_forall fun r =>
      (show Continuous
        (pairedEtaFiniteGaussianLaplaceKernel r tau) by
          unfold pairedEtaFiniteGaussianLaplaceKernel
          fun_prop).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => -(p.1 + p.2) *
        pairedEtaFiniteGaussianLaplaceKernel sigma tau p)
      ((pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N)) :=
    (show Continuous (fun p : ℝ × ℝ => -(p.1 + p.2) *
      pairedEtaFiniteGaussianLaplaceKernel sigma tau p) by
        unfold pairedEtaFiniteGaussianLaplaceKernel
        fun_prop).aestronglyMeasurable
  have hboundInt : Integrable bound
      ((pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N)) := by
    exact integrable_sum_mul_rexp_neg_mul_pairedEtaFiniteLogMeasure_prod
      N (sigma - 1)
  have hbound : ∀ᵐ p : ℝ × ℝ
      ∂(pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N),
      ∀ r ∈ s,
        ‖-(p.1 + p.2) *
          pairedEtaFiniteGaussianLaplaceKernel r tau p‖ ≤ bound p := by
    filter_upwards [ae_nonneg_pairedEtaFiniteLogMeasure_prod N] with p hp
    intro r hr
    have hsum : 0 ≤ p.1 + p.2 := add_nonneg hp.1 hp.2
    have hexponent : -r * (p.1 + p.2) ≤
        -(sigma - 1) * (p.1 + p.2) := by
      have hrLower : sigma - 1 ≤ r := hr.1.le
      nlinarith
    have hexp : Real.exp (-r * (p.1 + p.2)) ≤
        Real.exp (-(sigma - 1) * (p.1 + p.2)) :=
      Real.exp_le_exp.mpr hexponent
    have hquad : -(p.1 - p.2) ^ 2 / (4 * tau) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
    have hdamp : Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hquad
    unfold pairedEtaFiniteGaussianLaplaceKernel bound
    rw [Real.norm_eq_abs]
    rw [show |-(p.1 + p.2) *
          (Real.exp (-r * (p.1 + p.2)) *
            Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)))| =
        (p.1 + p.2) *
          (Real.exp (-r * (p.1 + p.2)) *
            Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau))) by
      rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hsum)
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))]
      ring]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_of_le_one_right (Real.exp_pos _).le hdamp).trans hexp) hsum
  have hdiff : ∀ᵐ p : ℝ × ℝ
      ∂(pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N),
      ∀ r ∈ s,
        HasDerivAt
          (fun q : ℝ => pairedEtaFiniteGaussianLaplaceKernel q tau p)
          (-(p.1 + p.2) *
            pairedEtaFiniteGaussianLaplaceKernel r tau p) r :=
    Eventually.of_forall fun p r hr =>
      hasDerivAt_pairedEtaFiniteGaussianLaplaceKernel_sigma r tau p
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hFmeas
    (integrable_pairedEtaFiniteGaussianLaplaceKernel N sigma htau)
    hF'meas hbound hboundInt hdiff).2

private theorem hasDerivAt_integral_neg_firstSigmaMomentKernel
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    HasDerivAt
      (fun r : ℝ => ∫ p : ℝ × ℝ, -(p.1 + p.2) *
        pairedEtaFiniteGaussianLaplaceKernel r tau p
        ∂(pairedEtaFiniteLogMeasure N).prod
          (pairedEtaFiniteLogMeasure N))
      (∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 *
        pairedEtaFiniteGaussianLaplaceKernel sigma tau p
        ∂(pairedEtaFiniteLogMeasure N).prod
          (pairedEtaFiniteLogMeasure N)) sigma := by
  let s : Set ℝ := Ioo (sigma - 1) (sigma + 1)
  let bound : ℝ × ℝ → ℝ := fun p =>
    (p.1 + p.2) ^ 2 * Real.exp (-(sigma - 1) * (p.1 + p.2))
  have hs : s ∈ 𝓝 sigma := by
    apply Ioo_mem_nhds
    · linarith
    · linarith
  have hFmeas : ∀ᶠ r : ℝ in 𝓝 sigma,
      AEStronglyMeasurable
        (fun p : ℝ × ℝ => -(p.1 + p.2) *
          pairedEtaFiniteGaussianLaplaceKernel r tau p)
        ((pairedEtaFiniteLogMeasure N).prod
          (pairedEtaFiniteLogMeasure N)) :=
    Eventually.of_forall fun r =>
      (show Continuous (fun p : ℝ × ℝ => -(p.1 + p.2) *
        pairedEtaFiniteGaussianLaplaceKernel r tau p) by
          unfold pairedEtaFiniteGaussianLaplaceKernel
          fun_prop).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2 *
        pairedEtaFiniteGaussianLaplaceKernel sigma tau p)
      ((pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N)) :=
    (show Continuous (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2 *
      pairedEtaFiniteGaussianLaplaceKernel sigma tau p) by
        unfold pairedEtaFiniteGaussianLaplaceKernel
        fun_prop).aestronglyMeasurable
  have hboundInt : Integrable bound
      ((pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N)) := by
    exact integrable_sq_sum_mul_rexp_neg_mul_pairedEtaFiniteLogMeasure_prod
      N (sigma - 1)
  have hbound : ∀ᵐ p : ℝ × ℝ
      ∂(pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N),
      ∀ r ∈ s,
        ‖(p.1 + p.2) ^ 2 *
          pairedEtaFiniteGaussianLaplaceKernel r tau p‖ ≤ bound p := by
    filter_upwards [ae_nonneg_pairedEtaFiniteLogMeasure_prod N] with p hp
    intro r hr
    have hsq : 0 ≤ (p.1 + p.2) ^ 2 := sq_nonneg _
    have hexponent : -r * (p.1 + p.2) ≤
        -(sigma - 1) * (p.1 + p.2) := by
      have hsum : 0 ≤ p.1 + p.2 := add_nonneg hp.1 hp.2
      have hrLower : sigma - 1 ≤ r := hr.1.le
      nlinarith
    have hexp : Real.exp (-r * (p.1 + p.2)) ≤
        Real.exp (-(sigma - 1) * (p.1 + p.2)) :=
      Real.exp_le_exp.mpr hexponent
    have hquad : -(p.1 - p.2) ^ 2 / (4 * tau) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) (by positivity)
    have hdamp : Real.exp (-(p.1 - p.2) ^ 2 / (4 * tau)) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hquad
    unfold pairedEtaFiniteGaussianLaplaceKernel bound
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hsq
        (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_of_le_one_right (Real.exp_pos _).le hdamp).trans hexp) hsq
  have hdiff : ∀ᵐ p : ℝ × ℝ
      ∂(pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N),
      ∀ r ∈ s,
        HasDerivAt
          (fun q : ℝ => -(p.1 + p.2) *
            pairedEtaFiniteGaussianLaplaceKernel q tau p)
          ((p.1 + p.2) ^ 2 *
            pairedEtaFiniteGaussianLaplaceKernel r tau p) r :=
    Eventually.of_forall fun p r hr =>
      hasDerivAt_neg_sum_mul_pairedEtaFiniteGaussianLaplaceKernel_sigma
        r tau p
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hFmeas
    (by
      have hfirst :=
        (integrable_firstSigmaMoment_pairedEtaFiniteGaussianLaplaceKernel
          N sigma htau).neg
      apply hfirst.congr
      exact Eventually.of_forall fun p => by
        change -((p.1 + p.2) *
            pairedEtaFiniteGaussianLaplaceKernel sigma tau p) =
          -(p.1 + p.2) *
            pairedEtaFiniteGaussianLaplaceKernel sigma tau p
        ring)
    hF'meas hbound hboundInt hdiff).2

/-- Exact first sigma derivative of the finite eta Gaussian--Laplace Gram
form. -/
theorem hasDerivAt_pairedEtaFiniteGaussianLaplaceGram_sigma
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    HasDerivAt
      (fun r : ℝ => pairedEtaFiniteGaussianLaplaceGram N r tau)
      (-pairedEtaFiniteGaussianLaplaceFirstSigmaMoment N sigma tau) sigma := by
  unfold pairedEtaFiniteGaussianLaplaceGram
    pairedEtaFiniteGaussianLaplaceFirstSigmaMoment
  have h := (hasDerivAt_integral_pairedEtaFiniteGaussianLaplaceKernel_sigma
    N sigma htau).const_mul (Real.sqrt (Real.pi / tau))
  apply h.congr_deriv
  rw [show
    (fun p : ℝ × ℝ => -(p.1 + p.2) *
      pairedEtaFiniteGaussianLaplaceKernel sigma tau p) =
      (fun p : ℝ × ℝ => -((p.1 + p.2) *
        pairedEtaFiniteGaussianLaplaceKernel sigma tau p)) by
      funext p
      ring,
    integral_neg]
  ring

/-- The derivative of the negative first sigma moment is the second sigma
moment, giving the exact positive second derivative integrand. -/
theorem hasDerivAt_neg_pairedEtaFiniteGaussianLaplaceFirstSigmaMoment
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    HasDerivAt
      (fun r : ℝ =>
        -pairedEtaFiniteGaussianLaplaceFirstSigmaMoment N r tau)
      (pairedEtaFiniteGaussianLaplaceSecondSigmaMoment N sigma tau) sigma := by
  unfold pairedEtaFiniteGaussianLaplaceFirstSigmaMoment
    pairedEtaFiniteGaussianLaplaceSecondSigmaMoment
  have h := (hasDerivAt_integral_neg_firstSigmaMomentKernel
    N sigma htau).const_mul (Real.sqrt (Real.pi / tau))
  rw [show
    (fun r : ℝ =>
      -(Real.sqrt (Real.pi / tau) *
        ∫ p : ℝ × ℝ, (p.1 + p.2) *
          pairedEtaFiniteGaussianLaplaceKernel r tau p
          ∂(pairedEtaFiniteLogMeasure N).prod
            (pairedEtaFiniteLogMeasure N))) =
      (fun r : ℝ =>
        Real.sqrt (Real.pi / tau) *
          ∫ p : ℝ × ℝ, -(p.1 + p.2) *
            pairedEtaFiniteGaussianLaplaceKernel r tau p
            ∂(pairedEtaFiniteLogMeasure N).prod
              (pairedEtaFiniteLogMeasure N)) by
      funext r
      rw [show
        (fun p : ℝ × ℝ => -(p.1 + p.2) *
          pairedEtaFiniteGaussianLaplaceKernel r tau p) =
          (fun p : ℝ × ℝ => -((p.1 + p.2) *
            pairedEtaFiniteGaussianLaplaceKernel r tau p)) by
          funext p
          ring,
        integral_neg]
      ring]
  exact h

/-- The first sigma moment is nonnegative at positive Gaussian time. -/
theorem pairedEtaFiniteGaussianLaplaceFirstSigmaMoment_nonneg
    (N : ℕ) (sigma tau : ℝ) :
    0 ≤ pairedEtaFiniteGaussianLaplaceFirstSigmaMoment N sigma tau := by
  unfold pairedEtaFiniteGaussianLaplaceFirstSigmaMoment
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply integral_nonneg_of_ae
  filter_upwards [ae_nonneg_pairedEtaFiniteLogMeasure_prod N] with p hp
  exact mul_nonneg (add_nonneg hp.1 hp.2)
    (pairedEtaFiniteGaussianLaplaceKernel_pos sigma tau p).le

/-- The second sigma moment is nonnegative at positive Gaussian time. -/
theorem pairedEtaFiniteGaussianLaplaceSecondSigmaMoment_nonneg
    (N : ℕ) (sigma tau : ℝ) :
    0 ≤ pairedEtaFiniteGaussianLaplaceSecondSigmaMoment N sigma tau := by
  unfold pairedEtaFiniteGaussianLaplaceSecondSigmaMoment
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply integral_nonneg
  intro p
  exact mul_nonneg (sq_nonneg _)
    (pairedEtaFiniteGaussianLaplaceKernel_pos sigma tau p).le

/-- The first logarithmic-time kernel has strictly positive integral for a
nonempty eta truncation at positive Gaussian time. -/
theorem integral_firstSigmaMoment_pairedEtaFiniteGaussianLaplaceKernel_pos
    {N : ℕ} (hN : 0 < N) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    0 < ∫ p : ℝ × ℝ, (p.1 + p.2) *
      pairedEtaFiniteGaussianLaplaceKernel sigma tau p
      ∂(pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N) := by
  apply integral_pos_of_ae_pos_of_measure_univ_pos
  · rw [Measure.ae_prod_iff_ae_ae
      ((isOpen_lt continuous_const
        (show Continuous (fun p : ℝ × ℝ => (p.1 + p.2) *
          pairedEtaFiniteGaussianLaplaceKernel sigma tau p) by
            unfold pairedEtaFiniteGaussianLaplaceKernel
            fun_prop)).measurableSet)]
    filter_upwards [ae_pos_pairedEtaFiniteLogMeasure N] with t ht
    filter_upwards [ae_pos_pairedEtaFiniteLogMeasure N] with u hu
    exact mul_pos (add_pos ht hu)
      (pairedEtaFiniteGaussianLaplaceKernel_pos sigma tau (t, u))
  · exact integrable_firstSigmaMoment_pairedEtaFiniteGaussianLaplaceKernel
      N sigma htau
  · exact pairedEtaFiniteLogMeasure_prod_univ_pos hN

/-- The second logarithmic-time kernel has strictly positive integral for a
nonempty eta truncation at positive Gaussian time. -/
theorem integral_secondSigmaMoment_pairedEtaFiniteGaussianLaplaceKernel_pos
    {N : ℕ} (hN : 0 < N) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    0 < ∫ p : ℝ × ℝ, (p.1 + p.2) ^ 2 *
      pairedEtaFiniteGaussianLaplaceKernel sigma tau p
      ∂(pairedEtaFiniteLogMeasure N).prod
        (pairedEtaFiniteLogMeasure N) := by
  apply integral_pos_of_ae_pos_of_measure_univ_pos
  · rw [Measure.ae_prod_iff_ae_ae
      ((isOpen_lt continuous_const
        (show Continuous (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2 *
          pairedEtaFiniteGaussianLaplaceKernel sigma tau p) by
            unfold pairedEtaFiniteGaussianLaplaceKernel
            fun_prop)).measurableSet)]
    filter_upwards [ae_pos_pairedEtaFiniteLogMeasure N] with t ht
    filter_upwards [ae_pos_pairedEtaFiniteLogMeasure N] with u hu
    exact mul_pos (sq_pos_of_pos (add_pos ht hu))
      (pairedEtaFiniteGaussianLaplaceKernel_pos sigma tau (t, u))
  · exact integrable_secondSigmaMoment_pairedEtaFiniteGaussianLaplaceKernel
      N sigma htau
  · exact pairedEtaFiniteLogMeasure_prod_univ_pos hN

/-- The first sigma moment is strictly positive for every nonempty finite eta
truncation at positive Gaussian time. -/
theorem pairedEtaFiniteGaussianLaplaceFirstSigmaMoment_pos
    {N : ℕ} (hN : 0 < N) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    0 < pairedEtaFiniteGaussianLaplaceFirstSigmaMoment N sigma tau := by
  unfold pairedEtaFiniteGaussianLaplaceFirstSigmaMoment
  exact mul_pos (Real.sqrt_pos.2 (div_pos Real.pi_pos htau))
    (integral_firstSigmaMoment_pairedEtaFiniteGaussianLaplaceKernel_pos
      hN sigma htau)

/-- The second sigma moment is strictly positive for every nonempty finite eta
truncation at positive Gaussian time. -/
theorem pairedEtaFiniteGaussianLaplaceSecondSigmaMoment_pos
    {N : ℕ} (hN : 0 < N) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    0 < pairedEtaFiniteGaussianLaplaceSecondSigmaMoment N sigma tau := by
  unfold pairedEtaFiniteGaussianLaplaceSecondSigmaMoment
  exact mul_pos (Real.sqrt_pos.2 (div_pos Real.pi_pos htau))
    (integral_secondSigmaMoment_pairedEtaFiniteGaussianLaplaceKernel_pos
      hN sigma htau)

/-- The first derivative is the negative first logarithmic-time moment. -/
theorem deriv_pairedEtaFiniteGaussianLaplaceGram_sigma
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    deriv (fun r : ℝ => pairedEtaFiniteGaussianLaplaceGram N r tau) sigma =
      -pairedEtaFiniteGaussianLaplaceFirstSigmaMoment N sigma tau :=
  (hasDerivAt_pairedEtaFiniteGaussianLaplaceGram_sigma N sigma htau).deriv

/-- The derivative of the first derivative is the second logarithmic-time
moment. -/
theorem hasDerivAt_deriv_pairedEtaFiniteGaussianLaplaceGram_sigma
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    HasDerivAt
      (fun r : ℝ =>
        deriv (fun q : ℝ => pairedEtaFiniteGaussianLaplaceGram N q tau) r)
      (pairedEtaFiniteGaussianLaplaceSecondSigmaMoment N sigma tau) sigma := by
  rw [show
    (fun r : ℝ =>
      deriv (fun q : ℝ =>
        pairedEtaFiniteGaussianLaplaceGram N q tau) r) =
      (fun r : ℝ =>
        -pairedEtaFiniteGaussianLaplaceFirstSigmaMoment N r tau) by
      funext r
      exact deriv_pairedEtaFiniteGaussianLaplaceGram_sigma N r htau]
  exact hasDerivAt_neg_pairedEtaFiniteGaussianLaplaceFirstSigmaMoment
    N sigma htau

/-- Exact second sigma derivative of the finite eta Gaussian--Laplace Gram
form. -/
theorem deriv_deriv_pairedEtaFiniteGaussianLaplaceGram_sigma
    (N : ℕ) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    deriv
      (fun r : ℝ =>
        deriv (fun q : ℝ => pairedEtaFiniteGaussianLaplaceGram N q tau) r)
      sigma = pairedEtaFiniteGaussianLaplaceSecondSigmaMoment N sigma tau :=
  (hasDerivAt_deriv_pairedEtaFiniteGaussianLaplaceGram_sigma
    N sigma htau).deriv

/-- The finite eta Gaussian--Laplace Gram profile is differentiable in its
real tilt. -/
theorem differentiable_pairedEtaFiniteGaussianLaplaceGram_sigma
    (N : ℕ) {tau : ℝ} (htau : 0 < tau) :
    Differentiable ℝ
      (fun sigma : ℝ => pairedEtaFiniteGaussianLaplaceGram N sigma tau) :=
  fun sigma =>
    (hasDerivAt_pairedEtaFiniteGaussianLaplaceGram_sigma
      N sigma htau).differentiableAt

/-- The first derivative of the finite eta Gaussian--Laplace Gram profile is
itself differentiable. -/
theorem differentiable_deriv_pairedEtaFiniteGaussianLaplaceGram_sigma
    (N : ℕ) {tau : ℝ} (htau : 0 < tau) :
    Differentiable ℝ
      (deriv (fun sigma : ℝ =>
        pairedEtaFiniteGaussianLaplaceGram N sigma tau)) :=
  fun sigma =>
    (hasDerivAt_deriv_pairedEtaFiniteGaussianLaplaceGram_sigma
      N sigma htau).differentiableAt

/-- The finite eta Gaussian--Laplace Gram profile is convex in its real tilt.
This is generic positive-Laplace structure, not complementary symmetry. -/
theorem convexOn_pairedEtaFiniteGaussianLaplaceGram_sigma
    (N : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ConvexOn ℝ univ
      (fun sigma : ℝ => pairedEtaFiniteGaussianLaplaceGram N sigma tau) := by
  apply convexOn_univ_of_deriv2_nonneg
    (differentiable_pairedEtaFiniteGaussianLaplaceGram_sigma N htau)
    (differentiable_deriv_pairedEtaFiniteGaussianLaplaceGram_sigma N htau)
  intro sigma
  simp only [Nat.iterate]
  rw [deriv_deriv_pairedEtaFiniteGaussianLaplaceGram_sigma N sigma htau]
  exact pairedEtaFiniteGaussianLaplaceSecondSigmaMoment_nonneg N sigma tau

/-- Every nonempty finite eta Gaussian--Laplace Gram profile is strictly
convex in its real tilt. This remains a generic positive-Laplace fact rather
than the missing completed symmetry. -/
theorem strictConvexOn_pairedEtaFiniteGaussianLaplaceGram_sigma
    {N : ℕ} (hN : 0 < N) {tau : ℝ} (htau : 0 < tau) :
    StrictConvexOn ℝ univ
      (fun sigma : ℝ => pairedEtaFiniteGaussianLaplaceGram N sigma tau) := by
  apply strictConvexOn_univ_of_deriv2_pos
    (differentiable_pairedEtaFiniteGaussianLaplaceGram_sigma N htau).continuous
  intro sigma
  simp only [Nat.iterate]
  rw [deriv_deriv_pairedEtaFiniteGaussianLaplaceGram_sigma N sigma htau]
  exact pairedEtaFiniteGaussianLaplaceSecondSigmaMoment_pos hN sigma htau

/-- The raw finite eta Gaussian--Laplace Gram profile is antitone in its real
tilt. A completed normalization must compensate for this one-sided drift
before a `sigma ↦ 1 - sigma` symmetry can emerge. -/
theorem antitone_pairedEtaFiniteGaussianLaplaceGram_sigma
    (N : ℕ) {tau : ℝ} (htau : 0 < tau) :
    Antitone
      (fun sigma : ℝ => pairedEtaFiniteGaussianLaplaceGram N sigma tau) := by
  apply antitone_of_deriv_nonpos
    (differentiable_pairedEtaFiniteGaussianLaplaceGram_sigma N htau)
  intro sigma
  rw [deriv_pairedEtaFiniteGaussianLaplaceGram_sigma N sigma htau]
  exact neg_nonpos.mpr
    (pairedEtaFiniteGaussianLaplaceFirstSigmaMoment_nonneg N sigma tau)

/-- Every nonempty raw finite eta Gaussian--Laplace Gram profile is strictly
decreasing in its real tilt. Thus a complementary reflection law cannot come
from the unnormalized positive Laplace form alone. -/
theorem strictAnti_pairedEtaFiniteGaussianLaplaceGram_sigma
    {N : ℕ} (hN : 0 < N) {tau : ℝ} (htau : 0 < tau) :
    StrictAnti
      (fun sigma : ℝ => pairedEtaFiniteGaussianLaplaceGram N sigma tau) := by
  apply strictAnti_of_deriv_neg
  intro sigma
  rw [deriv_pairedEtaFiniteGaussianLaplaceGram_sigma N sigma htau]
  simpa only [neg_lt_zero] using
    pairedEtaFiniteGaussianLaplaceFirstSigmaMoment_pos hN sigma htau

/-- For a nonempty truncation, equality of the two complementary raw Gram
values forces the central tilt. The theorem isolates precisely the equality
that a completed eta-specific symmetry would have to provide. -/
theorem pairedEtaFiniteGaussianLaplaceGram_eq_complementary_iff
    {N : ℕ} (hN : 0 < N) (sigma : ℝ) {tau : ℝ} (htau : 0 < tau) :
    pairedEtaFiniteGaussianLaplaceGram N sigma tau =
        pairedEtaFiniteGaussianLaplaceGram N (1 - sigma) tau ↔
      sigma = (1 : ℝ) / 2 := by
  constructor
  · intro h
    have htilt : sigma = 1 - sigma :=
      (strictAnti_pairedEtaFiniteGaussianLaplaceGram_sigma hN htau).injective h
    linarith
  · intro h
    congr 1
    linarith

end

end RiemannGaussian
