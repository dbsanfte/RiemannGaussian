import RiemannGaussian.EtaCurrentKernelEnvelope

/-!
# Arithmetic bounds for the actual completed-current absolute masses

Both multiplicity branches retain one reciprocal arithmetic cutoff. The
remaining cutoff growth is an explicit logarithmic power, with completion
weights, horizontal coordinates, and analytic multiplicity displayed in
the constant. This bounds the mass used in reconstruction errors; the
weighted absolute moment of the original signed current remains separate.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The two completed inverse-square horizontal masses, independent of cutoff. -/
def pairedEtaCompletedCurrentMassEnvelope (rho : NontrivialZetaZero) : ℝ :=
  pairedEtaCompletedLaplaceWeight (NontrivialZetaZero.conjugatePartner rho).1 / (1 - rho.1.re) ^ 2 +
    pairedEtaCompletedLaplaceWeight rho.1 / rho.1.re ^ 2

/-- The completed horizontal mass envelope is nonnegative. -/
theorem pairedEtaCompletedCurrentMassEnvelope_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaCompletedCurrentMassEnvelope rho := by
  exact add_nonneg (div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))
    (div_nonneg (Complex.normSq_nonneg _) (sq_nonneg _))

/-- The explicit completion- and multiplicity-dependent absolute-mass constant. -/
def pairedEtaLeadingCurrentMassConstant (rho : NontrivialZetaZero) : ℝ :=
  2 * (analyticZetaZeroMultiplicity rho : ℝ) * pairedEtaCompletedCurrentMassEnvelope rho

/-- The explicit absolute-mass constant is nonnegative. -/
theorem pairedEtaLeadingCurrentMassConstant_nonneg (rho : NontrivialZetaZero) :
    0 ≤ pairedEtaLeadingCurrentMassConstant rho :=
  mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (pairedEtaCompletedCurrentMassEnvelope_nonneg rho)

/-- The completed exponential envelope on two finite prefixes has its exact
cutoff-independent horizontal-mass majorant, with genuine integrability. -/
theorem completedCurrentExponentialEnvelope_prefix_bound (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (fun p : ℝ × ℝ ↦ pairedEtaCompletedCurrentExponentialEnvelope rho (p.1 + p.2))
      ((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N)) ∧
    (∫ p : ℝ × ℝ, pairedEtaCompletedCurrentExponentialEnvelope rho (p.1 + p.2)
      ∂((pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N))) ≤
      pairedEtaCompletedCurrentMassEnvelope rho := by
  have hs := NontrivialZetaZero.zero_lt_re rho
  have ht : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  obtain ⟨hi, hb⟩ := finite_current_exponential_integrable_bound N hs
  obtain ⟨hri, hrb⟩ := finite_current_exponential_integrable_bound N ht
  have hp : 0 ≤ pairedEtaCompletedLaplaceWeight (NontrivialZetaZero.conjugatePartner rho).1 := Complex.normSq_nonneg _
  have hq : 0 ≤ pairedEtaCompletedLaplaceWeight rho.1 := Complex.normSq_nonneg _
  refine ⟨(hri.const_mul _).add (hi.const_mul _), ?_⟩
  unfold pairedEtaCompletedCurrentExponentialEnvelope pairedEtaCompletedCurrentMassEnvelope
  rw [integral_add (hri.const_mul _) (hi.const_mul _), integral_const_mul, integral_const_mul]
  simpa only [mul_one_div] using add_le_add (mul_le_mul_of_nonneg_left hrb hp) (mul_le_mul_of_nonneg_left hb hq)

/-- The completed envelope on the restored head-prefix carrier retains one
cutoff increment; replacing inverse first powers by inverse squares uses
the actual zero's coordinates strictly between zero and one. -/
theorem completedCurrentExponentialEnvelope_head_bound (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (fun p : ℝ × ℝ ↦ pairedEtaCompletedCurrentExponentialEnvelope rho
      (p.1 + pairedEtaLogTailCutoff (N + 1) + p.2))
      ((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))) ∧
    (∫ p : ℝ × ℝ, pairedEtaCompletedCurrentExponentialEnvelope rho
      (p.1 + pairedEtaLogTailCutoff (N + 1) + p.2)
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)))) ≤
      pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCompletedCurrentMassEnvelope rho := by
  have hs := NontrivialZetaZero.zero_lt_re rho
  have hs1 := (NontrivialZetaZero.re_lt_one rho).le
  have ht : 0 < 1 - rho.1.re := sub_pos.mpr (NontrivialZetaZero.re_lt_one rho)
  have ht1 : 1 - rho.1.re ≤ 1 := by linarith
  obtain ⟨hi, hb⟩ := head_prefix_exponential_integrable_bound N hs
  obtain ⟨hri, hrb⟩ := head_prefix_exponential_integrable_bound N ht
  have hp : 0 ≤ pairedEtaCompletedLaplaceWeight (NontrivialZetaZero.conjugatePartner rho).1 := Complex.normSq_nonneg _
  have hq : 0 ≤ pairedEtaCompletedLaplaceWeight rho.1 := Complex.normSq_nonneg _
  have hd := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  have hb' := hb.trans (div_le_div_of_nonneg_left hd (sq_pos_of_pos hs) (by nlinarith))
  have hrb' := hrb.trans (div_le_div_of_nonneg_left hd (sq_pos_of_pos ht) (by nlinarith))
  refine ⟨(hri.const_mul _).add (hi.const_mul _), ?_⟩
  unfold pairedEtaCompletedCurrentExponentialEnvelope pairedEtaCompletedCurrentMassEnvelope
  rw [integral_add (hri.const_mul _) (hi.const_mul _), integral_const_mul, integral_const_mul]
  exact (add_le_add (mul_le_mul_of_nonneg_left hrb' hp) (mul_le_mul_of_nonneg_left hb' hq)).trans_eq (by ring)

/-- The actual simple-zero head absolute mass retains the one arithmetic
increment and explicit completed horizontal masses. -/
theorem integral_abs_topPrefixFiniteEnergyHeadKernel_le (rho : NontrivialZetaZero)
    (hm : analyticZetaZeroMultiplicity rho = 1) (N : ℕ) :
    (∫ p : ℝ × ℝ, |pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p|
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)))) ≤
      2 * pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCompletedCurrentMassEnvelope rho := by
  obtain ⟨hi, hb⟩ := completedCurrentExponentialEnvelope_head_bound rho N
  have hg := integral_mono (integrable_topPrefixFiniteEnergyHeadKernel rho N).abs (hi.const_mul 2)
    (abs_topPrefixFiniteEnergyHeadKernel_le rho hm N)
  rw [integral_const_mul] at hg
  exact (hg.trans (mul_le_mul_of_nonneg_left hb (by norm_num))).trans_eq (by ring)

/-- The adjacent-current absolute mass retains its cutoff increment and
logarithmic centered-power dependence, with both completion weights explicit. -/
theorem integral_abs_topPrefixFiniteEnergyAdjacentKernel_le (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ p : ℝ × ℝ, |pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p|
      ∂((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2)))) ≤
      2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho) *
          pairedEtaCompletedCurrentMassEnvelope rho := by
  obtain ⟨hi, hb⟩ := completedCurrentExponentialEnvelope_prefix_bound rho (N + 2)
  have hc : 0 ≤ 2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
      (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho) := by
    have hd := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
    have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
    positivity
  have hg := integral_mono_ae (integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N).abs (hi.const_mul
    (2 * (((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
      (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho)))
    ((ae_adjacent_current_physical_window N).mono fun p hp ↦ abs_topPrefixFiniteEnergyFactoredAdjacentMomentKernel_le rho N hp)
  rw [integral_const_mul] at hg
  exact hg.trans (mul_le_mul_of_nonneg_left hb hc)

/-- Both actual multiplicity branches have the same explicit mass bound,
retaining the arithmetic increment before replacing it by a reciprocal. -/
theorem pairedEtaLeadingCurrentAbsoluteKernelMass_le_increment (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaLeadingCurrentAbsoluteKernelMass rho N ≤
      pairedEtaLeadingCurrentMassConstant rho * pairedEtaLogTailShiftIncrement (N + 1) *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho) := by
  have hd := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  have hS := pairedEtaCompletedCurrentMassEnvelope_nonneg rho
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  have hP : 1 ≤ (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho) :=
    one_le_pow₀ (by linarith)
  unfold pairedEtaLeadingCurrentAbsoluteKernelMass
  split_ifs with hm
  · apply (integral_abs_topPrefixFiniteEnergyHeadKernel_le rho hm N).trans
    calc
      _ ≤ (2 * pairedEtaLogTailShiftIncrement (N + 1) * pairedEtaCompletedCurrentMassEnvelope rho) *
          (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho) :=
        le_mul_of_one_le_right (by positivity) hP
      _ = _ := by unfold pairedEtaLeadingCurrentMassConstant; rw [hm]; simp only [Nat.cast_one, mul_one]; ring
  · apply (integral_abs_topPrefixFiniteEnergyAdjacentKernel_le rho N).trans
    have hmul : ((analyticZetaZeroMultiplicity rho - 1 : ℕ) : ℝ) ≤ (analyticZetaZeroMultiplicity rho : ℝ) := by
      exact_mod_cast Nat.sub_le (analyticZetaZeroMultiplicity rho) 1
    calc
      _ ≤ (2 * ((analyticZetaZeroMultiplicity rho : ℝ) * pairedEtaLogTailShiftIncrement (N + 1)) *
          (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho)) *
            pairedEtaCompletedCurrentMassEnvelope rho := by
        gcongr
      _ = _ := by unfold pairedEtaLeadingCurrentMassConstant; ring

/-- The actual completed absolute kernel mass has one reciprocal cutoff
and only an explicit logarithmic power as the cutoff grows. -/
theorem pairedEtaLeadingCurrentAbsoluteKernelMass_le (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaLeadingCurrentAbsoluteKernelMass rho N ≤
      pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho) / (N + 1 : ℝ) := by
  have hC := pairedEtaLeadingCurrentMassConstant_nonneg rho
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  apply (pairedEtaLeadingCurrentAbsoluteKernelMass_le_increment rho N).trans
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pairedEtaLogTailShiftIncrement_succ_le N) hC) (by positivity)).trans_eq (by ring)

/-- The reconstruction error has a fully explicit arithmetic majorant:
the actual kernel mass has been bounded, with completion, multiplicity,
cutoff, tilt, and heat-width dependence all retained. -/
theorem pairedEtaLeadingCurrentNormalizedGapReturn_error_le_arithmetic
    (rho : NontrivialZetaZero) (N : ℕ) {a h : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hh : 0 < h) :
    ‖pairedEtaLeadingCurrentNormalizedGapReturn rho N a h -
      (pairedEtaTopPrefixFiniteEnergyLeadingFlux rho N : ℂ)‖ ≤
      (pairedEtaLeadingCurrentMassConstant rho *
        (1 + pairedEtaLogTailCutoff (N + 2)) ^ (2 * analyticZetaZeroMultiplicity rho) / (N + 1 : ℝ)) *
      (a * pairedEtaLogTailCutoff (N + 2) +
        (2 / (pairedEtaGapLaplaceMass 1 * a ^ 3) + 2 * pairedEtaLogTailCutoff (N + 2) ^ 2) / h ^ 2) := by
  apply (pairedEtaLeadingCurrentNormalizedGapReturn_error_le_smallTilt rho N ha ha1 hh).trans
  apply mul_le_mul_of_nonneg_right (pairedEtaLeadingCurrentAbsoluteKernelMass_le rho N)
  have hL := pairedEtaLogTailCutoff_nonneg (N + 2)
  have hM := (pairedEtaGapLaplaceMass_pos (by norm_num : (0 : ℝ) < 1)).le
  positivity

end

end RiemannGaussian
