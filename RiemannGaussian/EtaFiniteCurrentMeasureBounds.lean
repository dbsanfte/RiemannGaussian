import RiemannGaussian.EtaCurrentReconstructionError

/-!
# Measure bounds for the actual completed-current carriers

Finite eta prefixes are dominated by the full positive half-line. Their
exponential masses are therefore bounded independently of the arithmetic
cutoff. The distinct translated head retains its short interval width,
and the consecutive logarithmic cutoff increment has an explicit reciprocal
arithmetic bound.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A finite eta prefix is dominated by the actual full eta measure. -/
theorem pairedEtaFiniteLogMeasure_le_logMeasure (N : ℕ) :
    pairedEtaFiniteLogMeasure N ≤ pairedEtaLogMeasure := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [pairedEtaFiniteLogMeasure, Measure.finsetSum_apply,
    pairedEtaLogMeasure_eq_sum_restrict, Measure.sum_apply _ hA]
  exact ENNReal.sum_le_tsum (Finset.range N)

/-- Every finite eta measure is dominated by Lebesgue measure on positive time. -/
theorem pairedEtaFiniteLogMeasure_le_positiveVolume (N : ℕ) :
    pairedEtaFiniteLogMeasure N ≤ volume.restrict (Ioi 0) :=
  (pairedEtaFiniteLogMeasure_le_logMeasure N).trans pairedEtaLogMeasure_le_volume_restrict_Ioi_zero

/-- Positive exponential mass of any finite prefix is at most the exact
full-half-line Laplace mass, uniformly in the arithmetic cutoff. -/
theorem integral_exp_neg_finiteLogMeasure_le (N : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    (∫ t : ℝ, Real.exp (-sigma * t) ∂pairedEtaFiniteLogMeasure N) ≤ 1 / sigma := by
  have hm := integral_mono_measure (pairedEtaFiniteLogMeasure_le_positiveVolume N)
    (Eventually.of_forall (fun t : ℝ ↦ (Real.exp_pos (-sigma * t)).le))
    (integrableOn_exp_mul_Ioi (a := -sigma) (by linarith) 0)
  have hv : (∫ t : ℝ in Ioi 0, Real.exp (-sigma * t)) = 1 / sigma := by
    simpa only [positiveHalfLineRealLogLaplaceMoment, pow_zero, one_mul, Nat.factorial_zero,
      Nat.cast_one, zero_add, pow_one] using positiveHalfLineRealLogLaplaceMoment_eq_factorial 0 hsigma
  exact hm.trans_eq hv

/-- The product-prefix exponential is integrable and has its cutoff-independent
inverse-square tilt bound. -/
theorem finite_current_exponential_integrable_bound (N : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Integrable (fun p : ℝ × ℝ ↦ Real.exp (-sigma * (p.1 + p.2)))
      ((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)) ∧
    (∫ p : ℝ × ℝ, Real.exp (-sigma * (p.1 + p.2))
      ∂((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N))) ≤ 1 / sigma ^ 2 := by
  have heq : (fun p : ℝ × ℝ ↦ Real.exp (-sigma * (p.1 + p.2))) =
      (fun p ↦ Real.exp (-sigma * p.1) * Real.exp (-sigma * p.2)) := by
    ext p
    rw [← Real.exp_add]
    congr 1
    ring
  have hi := integrable_rexp_neg_mul_pairedEtaFiniteLogMeasure N sigma
  rw [heq]
  refine ⟨hi.mul_prod hi, ?_⟩
  rw [integral_prod_mul (μ := pairedEtaFiniteLogMeasure N) (ν := pairedEtaFiniteLogMeasure N)
    (fun t : ℝ ↦ Real.exp (-sigma * t)) (fun t : ℝ ↦ Real.exp (-sigma * t))]
  have hb := integral_exp_neg_finiteLogMeasure_le N hsigma
  have hn : 0 ≤ ∫ t : ℝ, Real.exp (-sigma * t) ∂pairedEtaFiniteLogMeasure N :=
    integral_nonneg fun _ ↦ (Real.exp_pos _).le
  have hm := mul_le_mul hb hb hn (by positivity)
  exact hm.trans_eq (by ring)

/-- Every odd logarithmic cutoff is nonnegative. -/
theorem pairedEtaLogTailCutoff_nonneg (N : ℕ) : 0 ≤ pairedEtaLogTailCutoff N := by
  unfold pairedEtaLogTailCutoff
  exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * N + 1 by omega))

/-- The absolute-coordinate exponential on the translated head is integrable
and retains the head's one-step width as a bound. -/
theorem head_current_exponential_integrable_bound (N : ℕ) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    Integrable (fun t : ℝ ↦ Real.exp (-sigma * (t + pairedEtaLogTailCutoff (N + 1))))
      (pairedEtaShiftedLogHeadMeasure (N + 1)) ∧
    (∫ t : ℝ, Real.exp (-sigma * (t + pairedEtaLogTailCutoff (N + 1)))
      ∂pairedEtaShiftedLogHeadMeasure (N + 1)) ≤ pairedEtaLogTailShiftIncrement (N + 1) := by
  have hi : Integrable (fun t : ℝ ↦ Real.exp (-sigma * (t + pairedEtaLogTailCutoff (N + 1))))
      (pairedEtaShiftedLogHeadMeasure (N + 1)) := by
    rw [pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc]
    exact (show Continuous (fun t : ℝ ↦ Real.exp (-sigma * (t + pairedEtaLogTailCutoff (N + 1)))) by
      fun_prop).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ _ : ℝ, (1 : ℝ) ∂pairedEtaShiftedLogHeadMeasure (N + 1) := by
      apply integral_mono_ae hi (integrable_const 1)
      filter_upwards [ae_add_cutoff_mem_pairedEtaLogSupport_shiftedHeadMeasure (N + 1)] with t ht
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsigma)
        (pairedEtaLogSupport_subset_Ioi_zero ht).le)
    _ = pairedEtaShiftedLogHeadWidth (N + 1) := by
      rw [integral_const, smul_eq_mul, mul_one, pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc,
        measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le (pairedEtaShiftedLogHeadWidth_pos _).le, sub_zero]
    _ ≤ _ := (pairedEtaShiftedLogHeadWidth_lt_shiftIncrement _).le

/-- The actual head-prefix product exponential retains one reciprocal tilt
and the short head interval, with the physical translation included. -/
theorem head_prefix_exponential_integrable_bound (N : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Integrable (fun p : ℝ × ℝ ↦ Real.exp (-sigma * (p.1 + pairedEtaLogTailCutoff (N + 1) + p.2)))
      ((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))) ∧
    (∫ p : ℝ × ℝ, Real.exp (-sigma * (p.1 + pairedEtaLogTailCutoff (N + 1) + p.2))
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)))) ≤
      pairedEtaLogTailShiftIncrement (N + 1) / sigma := by
  have heq : (fun p : ℝ × ℝ ↦ Real.exp (-sigma * (p.1 + pairedEtaLogTailCutoff (N + 1) + p.2))) =
      (fun p ↦ Real.exp (-sigma * (p.1 + pairedEtaLogTailCutoff (N + 1))) * Real.exp (-sigma * p.2)) := by
    ext p
    rw [← Real.exp_add]
    congr 1
    ring
  obtain ⟨hh, hhb⟩ := head_current_exponential_integrable_bound N hsigma.le
  have hp := integrable_rexp_neg_mul_pairedEtaFiniteLogMeasure (N + 2) sigma
  rw [heq]
  refine ⟨hh.mul_prod hp, ?_⟩
  rw [integral_prod_mul (μ := pairedEtaShiftedLogHeadMeasure (N + 1)) (ν := pairedEtaFiniteLogMeasure (N + 2))
    (fun t : ℝ ↦ Real.exp (-sigma * (t + pairedEtaLogTailCutoff (N + 1))))
    (fun t : ℝ ↦ Real.exp (-sigma * t))]
  have hb := mul_le_mul hhb (integral_exp_neg_finiteLogMeasure_le (N + 2) hsigma)
    (integral_nonneg fun _ ↦ (Real.exp_pos _).le) (pairedEtaLogTailShiftIncrement_pos _).le
  simpa only [mul_one_div] using hb

/-- The actual successor cutoff increment is at most `1/(N+1)` for every
arithmetic cutoff, without an eventual-threshold hypothesis. -/
theorem pairedEtaLogTailShiftIncrement_succ_le (N : ℕ) :
    pairedEtaLogTailShiftIncrement (N + 1) ≤ 1 / (N + 1 : ℝ) := by
  have h3 : 0 < (2 * N + 3 : ℝ) := by positivity
  have h5 : 0 < (2 * N + 5 : ℝ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos h5 h3)
  have heq : pairedEtaLogTailShiftIncrement (N + 1) = Real.log ((2 * N + 5 : ℝ) / (2 * N + 3 : ℝ)) := by
    rw [Real.log_div h5.ne' h3.ne']
    unfold pairedEtaLogTailShiftIncrement pairedEtaLogTailCutoff
    congr 1 <;> push_cast <;> congr 1 <;> ring
  rw [heq]
  calc
    _ ≤ (2 * N + 5 : ℝ) / (2 * N + 3 : ℝ) - 1 := hlog
    _ = 2 / (2 * N + 3 : ℝ) := by field_simp; ring
    _ ≤ _ := (div_le_div_iff₀ h3 (by positivity : 0 < (N + 1 : ℝ))).mpr (by linarith)

end

end RiemannGaussian
