import RiemannGaussian.EtaNormalizedHeatKernel
import RiemannGaussian.Hybrid.EtaSupportGapPhaseGram

/-!
# Weighted continuous heat commutators on the actual eta support

The kernel of `W_sigma [P_A,H_(2 h^2)] W_sigma` uses the half tilt in each
weight. Its squared integral norm is the actual uncoloured support/gap heat
transfer divided by `4 sqrt(pi) h`. Phase conjugation preserves diagonal
norms while retaining the mixed inner products.
-/

open Complex Filter MeasureTheory Set Topology Matrix
open scoped Classical ENNReal Interval Topology BigOperators

namespace RiemannGaussian

noncomputable section

/-- Squaring the Gaussian at time `2h^2` gives the Gaussian at time `h^2`
with the precise extra normalization factor. -/
theorem etaNormalizedHeatKernel_sqrt_two_sq {h : ℝ} (hh : 0 < h) (r : ℝ) :
    (etaNormalizedHeatKernel (Real.sqrt 2 * h) r) ^ 2 =
      etaNormalizedHeatKernel h r / (4 * Real.sqrt Real.pi * h) := by
  have htwo : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have htwoNe : Real.sqrt (2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hpiNe : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have he : Real.exp (-(1 / 4) * (r / (Real.sqrt 2 * h)) ^ 2) ^ 2 =
      Real.exp (-(1 / 4) * (r / h) ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    field_simp [mul_pow, htwo]
    rw [htwo]
    ring
  unfold etaNormalizedHeatKernel
  rw [div_pow, he]
  field_simp [mul_pow, htwo]
  norm_num [htwo]

/-- The commutator kernel before the two positive-time weights are restricted. -/
def pairedEtaHeatCommutatorKernelCore (sigma h : ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-sigma * (p.1 + p.2) / 2) *
    etaNormalizedHeatKernel (Real.sqrt 2 * h) (p.2 - p.1) *
    (pairedEtaLogIndicator p.1 - pairedEtaLogIndicator p.2)

/-- The full-real-line kernel of the half-tilted support/heat commutator. -/
def pairedEtaHeatCommutatorKernel (sigma h : ℝ) (p : ℝ × ℝ) : ℝ :=
  ((Ioi (0 : ℝ)) ×ˢ (Ioi 0)).indicator (pairedEtaHeatCommutatorKernelCore sigma h) p

/-- The positive-time multiplication weight with half the horizontal tilt. -/
def pairedEtaHalfTiltWindow (sigma t : ℝ) : ℝ :=
  (Ioi 0).indicator (fun t ↦ Real.exp (-sigma * t / 2)) t

/-- Literal factorization into the two half-tilt weights and the difference
between multiplying by the support before and after heat convolution. -/
theorem pairedEtaHeatCommutatorKernel_eq_halfTilt_commutator (sigma h t u : ℝ) :
    pairedEtaHeatCommutatorKernel sigma h (t, u) =
      pairedEtaHalfTiltWindow sigma t *
        (pairedEtaLogIndicator t * etaNormalizedHeatKernel (Real.sqrt 2 * h) (u - t) -
          etaNormalizedHeatKernel (Real.sqrt 2 * h) (u - t) * pairedEtaLogIndicator u) *
        pairedEtaHalfTiltWindow sigma u := by
  by_cases ht : 0 < t
  · by_cases hu : 0 < u
    · simp only [pairedEtaHeatCommutatorKernel, pairedEtaHalfTiltWindow, Set.indicator_apply,
        mem_prod, mem_Ioi, ht, hu, and_self, if_true, pairedEtaHeatCommutatorKernelCore]
      rw [show -sigma * (t + u) / 2 = -sigma * t / 2 + -sigma * u / 2 by ring, Real.exp_add]
      ring
    · simp [pairedEtaHeatCommutatorKernel, pairedEtaHalfTiltWindow, ht, hu]
  · simp [pairedEtaHeatCommutatorKernel, pairedEtaHalfTiltWindow, ht]

/-- Pointwise square of the commutator core, with the exact tilt and heat time. -/
theorem pairedEtaHeatCommutatorKernelCore_sq {h : ℝ} (hh : 0 < h)
    (sigma : ℝ) (p : ℝ × ℝ) :
    (pairedEtaHeatCommutatorKernelCore sigma h p) ^ 2 =
      pairedEtaSupportGapHeatWeight sigma h p / (4 * Real.sqrt Real.pi * h) := by
  have he : Real.exp (-sigma * (p.1 + p.2) / 2) ^ 2 = Real.exp (-sigma * (p.1 + p.2)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold pairedEtaHeatCommutatorKernelCore
  rw [mul_pow, mul_pow, he, etaNormalizedHeatKernel_sqrt_two_sq hh]
  unfold pairedEtaSupportGapHeatWeight
  rw [pairedEtaLogShiftMismatch_sub]
  ring

/-- Pointwise squared norm on the full real plane, with the positive-time
restriction retained explicitly. -/
theorem pairedEtaHeatCommutatorKernel_norm_sq {h : ℝ} (hh : 0 < h)
    (sigma : ℝ) (p : ℝ × ℝ) :
    ‖pairedEtaHeatCommutatorKernel sigma h p‖ ^ 2 =
      (((Ioi (0 : ℝ)) ×ˢ (Ioi 0)).indicator (pairedEtaSupportGapHeatWeight sigma h) p) /
        (4 * Real.sqrt Real.pi * h) := by
  by_cases hp : p ∈ (Ioi (0 : ℝ)) ×ˢ (Ioi 0)
  · rw [pairedEtaHeatCommutatorKernel, Set.indicator_of_mem hp, Set.indicator_of_mem hp,
      Real.norm_eq_abs, sq_abs, pairedEtaHeatCommutatorKernelCore_sq hh]
  · simp only [pairedEtaHeatCommutatorKernel, Set.indicator_of_notMem hp,
      norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]

/-- Genuine square-integrability of the full continuous commutator kernel. -/
theorem integrable_pairedEtaHeatCommutatorKernel_norm_sq {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) :
    Integrable (fun p : ℝ × ℝ ↦ ‖pairedEtaHeatCommutatorKernel sigma h p‖ ^ 2)
      ((volume : Measure ℝ).prod volume) := by
  have hQ : MeasurableSet ((Ioi (0 : ℝ)) ×ˢ (Ioi (0 : ℝ))) := measurableSet_Ioi.prod measurableSet_Ioi
  have hi : Integrable (((Ioi (0 : ℝ)) ×ˢ (Ioi 0)).indicator (pairedEtaSupportGapHeatWeight sigma h))
      ((volume : Measure ℝ).prod volume) := by
    apply (integrable_indicator_iff hQ).mpr
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact integrable_pairedEtaSupportGapHeatWeight hsigma hh
  have hfun : (fun p : ℝ × ℝ ↦ ‖pairedEtaHeatCommutatorKernel sigma h p‖ ^ 2) =
      (fun p ↦ (((Ioi (0 : ℝ)) ×ˢ (Ioi 0)).indicator (pairedEtaSupportGapHeatWeight sigma h) p) /
        (4 * Real.sqrt Real.pi * h)) := funext (pairedEtaHeatCommutatorKernel_norm_sq hh sigma)
  rw [hfun]
  exact hi.div_const _

/-- Exact integral identity for the weighted continuous heat commutator.
At positive tilt the preceding integrability theorem gives a finite squared
norm. The half tilt in each outer weight retains the original tilt `sigma`. -/
theorem integral_pairedEtaHeatCommutatorKernel_norm_sq {sigma h : ℝ}
    (hh : 0 < h) :
    (∫ p : ℝ × ℝ, ‖pairedEtaHeatCommutatorKernel sigma h p‖ ^ 2
      ∂((volume : Measure ℝ).prod volume)) =
      pairedEtaSupportGapGaussianLeakage sigma h (fun _ ↦ 0) / (4 * Real.sqrt Real.pi * h) := by
  simp_rw [pairedEtaHeatCommutatorKernel_norm_sq hh sigma]
  rw [integral_div, integral_indicator (measurableSet_Ioi.prod measurableSet_Ioi),
    ← Measure.prod_restrict]
  simp only [pairedEtaSupportGapGaussianLeakage, pairedEtaSupportGapHeatKernel,
    sub_self, Real.cos_zero, mul_one]

/-- Conjugation of the continuous kernel by multiplication with `exp(i phi)`. -/
def pairedEtaHeatCommutatorPhaseKernel (sigma h : ℝ) (phi : ℝ → ℝ) (p : ℝ × ℝ) : ℂ :=
  (pairedEtaHeatCommutatorKernel sigma h p : ℂ) * pairedEtaHeatPhaseUnit phi p.swap

/-- Phase conjugation preserves the pointwise norm of the kernel. -/
theorem norm_pairedEtaHeatCommutatorPhaseKernel (sigma h : ℝ) (phi : ℝ → ℝ) (p : ℝ × ℝ) :
    ‖pairedEtaHeatCommutatorPhaseKernel sigma h phi p‖ = ‖pairedEtaHeatCommutatorKernel sigma h p‖ := by
  simp only [pairedEtaHeatCommutatorPhaseKernel, norm_mul, norm_pairedEtaHeatPhaseUnit,
    Complex.norm_real, mul_one]

/-- The full real commutator kernel is measurable. -/
theorem measurable_pairedEtaHeatCommutatorKernel (sigma h : ℝ) :
    Measurable (pairedEtaHeatCommutatorKernel sigma h) := by
  have he : Continuous (fun p : ℝ × ℝ ↦ Real.exp (-sigma * (p.1 + p.2) / 2)) := by fun_prop
  have hg : Continuous (fun p : ℝ × ℝ ↦ etaNormalizedHeatKernel (Real.sqrt 2 * h) (p.2 - p.1)) := by
    unfold etaNormalizedHeatKernel
    fun_prop
  have hi : Measurable (fun p : ℝ × ℝ ↦ pairedEtaLogIndicator p.1 - pairedEtaLogIndicator p.2) :=
    (measurable_pairedEtaLogIndicator.comp measurable_fst).sub
      (measurable_pairedEtaLogIndicator.comp measurable_snd)
  exact ((he.measurable.mul hg.measurable).mul hi).indicator
    (measurableSet_Ioi.prod measurableSet_Ioi)

/-- Measurable phases give measurable conjugated continuous kernels. -/
theorem measurable_pairedEtaHeatCommutatorPhaseKernel {phi : ℝ → ℝ} (hphi : Measurable phi)
    (sigma h : ℝ) : Measurable (pairedEtaHeatCommutatorPhaseKernel sigma h phi) := by
  exact (measurable_pairedEtaHeatCommutatorKernel sigma h).complex_ofReal.mul
    ((measurable_pairedEtaHeatPhaseUnit hphi).comp measurable_swap)

/-- The norm of a mixed product is exactly the original squared kernel norm. -/
theorem norm_pairedEtaHeatCommutatorPhaseKernel_mixed (sigma h : ℝ) (phi psi : ℝ → ℝ)
    (p : ℝ × ℝ) :
    ‖star (pairedEtaHeatCommutatorPhaseKernel sigma h phi p) *
      pairedEtaHeatCommutatorPhaseKernel sigma h psi p‖ =
      ‖pairedEtaHeatCommutatorKernel sigma h p‖ ^ 2 := by
  rw [norm_mul, norm_star, norm_pairedEtaHeatCommutatorPhaseKernel,
    norm_pairedEtaHeatCommutatorPhaseKernel, pow_two]

/-- Every ordered mixed kernel inner product is absolutely integrable. -/
theorem integrable_pairedEtaHeatCommutatorPhaseKernel_mixed {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) {phi psi : ℝ → ℝ}
    (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (fun p : ℝ × ℝ ↦ star (pairedEtaHeatCommutatorPhaseKernel sigma h phi p) *
      pairedEtaHeatCommutatorPhaseKernel sigma h psi p) ((volume : Measure ℝ).prod volume) := by
  apply (integrable_pairedEtaHeatCommutatorKernel_norm_sq hsigma hh).mono'
  · exact ((Complex.continuous_conj.measurable.comp
      (measurable_pairedEtaHeatCommutatorPhaseKernel hphi sigma h)).mul
      (measurable_pairedEtaHeatCommutatorPhaseKernel hpsi sigma h)).aestronglyMeasurable
  · exact Eventually.of_forall fun p ↦
      (norm_pairedEtaHeatCommutatorPhaseKernel_mixed sigma h phi psi p).le

/-- Exact ordered mixed-product kernel. The reversal of the two phases is
retained at this point, before the symmetric real integral is taken. -/
theorem pairedEtaHeatCommutatorPhaseKernel_mixed {h : ℝ} (hh : 0 < h)
    (sigma : ℝ) (phi psi : ℝ → ℝ) (p : ℝ × ℝ) :
    star (pairedEtaHeatCommutatorPhaseKernel sigma h phi p) *
      pairedEtaHeatCommutatorPhaseKernel sigma h psi p =
      ((Ioi (0 : ℝ)) ×ˢ (Ioi 0)).indicator
        (fun p ↦ pairedEtaSupportGapComplexKernel sigma h psi phi p /
          ((4 * Real.sqrt Real.pi * h : ℝ) : ℂ)) p := by
  have hprod : star (pairedEtaHeatCommutatorPhaseKernel sigma h phi p) *
      pairedEtaHeatCommutatorPhaseKernel sigma h psi p =
      ((pairedEtaHeatCommutatorKernel sigma h p : ℂ) ^ 2) *
        star (pairedEtaHeatPhaseUnit psi p) * pairedEtaHeatPhaseUnit phi p := by
    unfold pairedEtaHeatCommutatorPhaseKernel
    rw [pairedEtaHeatPhaseUnit_swap, pairedEtaHeatPhaseUnit_swap]
    simp only [star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have hsquare : (pairedEtaHeatCommutatorKernel sigma h p) ^ 2 =
      (((Ioi (0 : ℝ)) ×ˢ (Ioi 0)).indicator (pairedEtaSupportGapHeatWeight sigma h) p) /
        (4 * Real.sqrt Real.pi * h) := by
    simpa only [Real.norm_eq_abs, sq_abs] using pairedEtaHeatCommutatorKernel_norm_sq hh sigma p
  have hsquareC : (pairedEtaHeatCommutatorKernel sigma h p : ℂ) ^ 2 =
      ((((Ioi (0 : ℝ)) ×ˢ (Ioi 0)).indicator (pairedEtaSupportGapHeatWeight sigma h) p : ℝ) : ℂ) /
        ((4 * Real.sqrt Real.pi * h : ℝ) : ℂ) := by exact_mod_cast hsquare
  rw [hprod, hsquareC]
  by_cases hp : p ∈ (Ioi (0 : ℝ)) ×ˢ (Ioi 0)
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    unfold pairedEtaSupportGapComplexKernel
    ring
  · simp only [Set.indicator_of_notMem hp, Complex.ofReal_zero, zero_div, zero_mul]

/-- Mixed inner products of the phase-conjugated continuous commutator
kernels are precisely the actual support/gap phase Gram entries, with the
same normalization as their squared norms. -/
theorem integral_pairedEtaHeatCommutatorPhaseKernel_mixed {sigma h : ℝ}
    (hsigma : 0 < sigma) (hh : 0 < h) {phi psi : ℝ → ℝ}
    (hphi : Measurable phi) (hpsi : Measurable psi) :
    (∫ p : ℝ × ℝ, star (pairedEtaHeatCommutatorPhaseKernel sigma h phi p) *
      pairedEtaHeatCommutatorPhaseKernel sigma h psi p ∂((volume : Measure ℝ).prod volume)) =
      ((pairedEtaSupportGapGaussianLeakage sigma h (fun t ↦ psi t - phi t) /
        (4 * Real.sqrt Real.pi * h) : ℝ) : ℂ) := by
  simp_rw [pairedEtaHeatCommutatorPhaseKernel_mixed hh sigma phi psi]
  rw [integral_indicator (measurableSet_Ioi.prod measurableSet_Ioi), ← Measure.prod_restrict,
    integral_div, integral_pairedEtaSupportGapComplexKernel hsigma hh hpsi hphi]
  have hsymm : pairedEtaSupportGapGaussianLeakage sigma h (fun t ↦ phi t - psi t) =
      pairedEtaSupportGapGaussianLeakage sigma h (fun t ↦ psi t - phi t) := by
    unfold pairedEtaSupportGapGaussianLeakage pairedEtaSupportGapHeatKernel
    apply integral_congr_ae
    filter_upwards with p
    rw [show phi p.2 - psi p.2 - (phi p.1 - psi p.1) =
        -(psi p.2 - phi p.2 - (psi p.1 - phi p.1)) by ring, Real.cos_neg]
  rw [hsymm, Complex.ofReal_div]

/-- Diagonal integral norms are invariant under phase conjugation; the
phase information remains in the mixed inner products above. -/
theorem integral_pairedEtaHeatCommutatorPhaseKernel_norm_sq {h : ℝ} (hh : 0 < h)
    (sigma : ℝ) (phi : ℝ → ℝ) :
    (∫ p : ℝ × ℝ, ‖pairedEtaHeatCommutatorPhaseKernel sigma h phi p‖ ^ 2
      ∂((volume : Measure ℝ).prod volume)) =
      pairedEtaSupportGapGaussianLeakage sigma h (fun _ ↦ 0) / (4 * Real.sqrt Real.pi * h) := by
  simp_rw [norm_pairedEtaHeatCommutatorPhaseKernel]
  exact integral_pairedEtaHeatCommutatorKernel_norm_sq hh

end

end RiemannGaussian
