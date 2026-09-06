import RiemannGaussian.EtaSignedHeatCurrentAudit

/-!
# A genuine ordered heat-return pairing of the completed eta current

At each positive intermediate time, both multiplicity branches have an
integrable two-transition pairing. It equals the negative gap-return
pairing with the exact completed features. The intermediate time, two heat
widths, phases, tilts, zero, and arithmetic cutoff remain independent.
No exchange with an infinite intermediate-time integral is asserted.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- A pointwise bound for the actual continuous phase commutator at
nonnegative tilt and positive heat width, on the positive-time plane. -/
theorem norm_pairedEtaHeatCommutatorPhaseKernel_le {sigma h t u : ℝ}
    (hsigma : 0 ≤ sigma) (hh : 0 < h) (ht : 0 < t) (hu : 0 < u) (phi : ℝ → ℝ) :
    ‖pairedEtaHeatCommutatorPhaseKernel sigma h phi (t, u)‖ ≤
      1 / (2 * Real.sqrt Real.pi * (Real.sqrt 2 * h)) := by
  have hp : (t, u) ∈ (Ioi (0 : ℝ)) ×ˢ (Ioi 0) := ⟨ht, hu⟩
  have hh' : 0 < Real.sqrt 2 * h := by positivity
  have hi : |pairedEtaLogIndicator t - pairedEtaLogIndicator u| ≤ 1 := by
    rcases pairedEtaLogIndicator_eq_zero_or_one t with ht | ht <;>
      rcases pairedEtaLogIndicator_eq_zero_or_one u with hu | hu <;> simp [ht, hu]
  have he : Real.exp (-sigma * (t + u) / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  rw [norm_pairedEtaHeatCommutatorPhaseKernel, pairedEtaHeatCommutatorKernel,
    Set.indicator_of_mem hp, pairedEtaHeatCommutatorKernelCore, Real.norm_eq_abs,
    abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (etaNormalizedHeatKernel_pos hh' _)]
  calc
    _ ≤ etaNormalizedHeatKernel (Real.sqrt 2 * h) (u - t) * 1 :=
      mul_le_mul (mul_le_of_le_one_left (etaNormalizedHeatKernel_pos hh' _).le he) hi
        (abs_nonneg _) (etaNormalizedHeatKernel_pos hh' _).le
    _ ≤ _ := by simpa only [mul_one] using etaNormalizedHeatKernel_le hh' (u - t)

private theorem integrable_current_twoTransitions {μ : Measure (ℝ × ℝ)} {f : ℝ × ℝ → ℝ}
    (hf : Integrable f μ) (T : ℝ × ℝ → ℝ) (hT : Measurable T)
    (hpos : ∀ᵐ p ∂μ, 0 < T p ∧ 0 < p.2) {sigma h tau k w : ℝ}
    (hsigma : 0 ≤ sigma) (hh : 0 < h) (htau : 0 ≤ tau) (hk : 0 < k) (hw : 0 < w)
    {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (fun p : ℝ × ℝ ↦ (f p : ℂ) * pairedEtaHeatCommutatorPhaseKernel sigma h phi (T p, w) *
      pairedEtaHeatCommutatorPhaseKernel tau k psi (w, p.2)) μ := by
  have hfc : Integrable (fun p ↦ (f p : ℂ)) μ := hf.ofReal
  have hm : Measurable (fun p : ℝ × ℝ ↦ pairedEtaHeatCommutatorPhaseKernel sigma h phi (T p, w) *
      pairedEtaHeatCommutatorPhaseKernel tau k psi (w, p.2)) :=
    ((measurable_pairedEtaHeatCommutatorPhaseKernel hphi sigma h).comp (hT.prodMk measurable_const)).mul
      ((measurable_pairedEtaHeatCommutatorPhaseKernel hpsi tau k).comp (measurable_const.prodMk measurable_snd))
  have hb : ∀ᵐ p ∂μ, ‖pairedEtaHeatCommutatorPhaseKernel sigma h phi (T p, w) *
      pairedEtaHeatCommutatorPhaseKernel tau k psi (w, p.2)‖ ≤
      (1 / (2 * Real.sqrt Real.pi * (Real.sqrt 2 * h))) * (1 / (2 * Real.sqrt Real.pi * (Real.sqrt 2 * k))) := by
    filter_upwards [hpos] with p hp
    rw [norm_mul]
    exact mul_le_mul (norm_pairedEtaHeatCommutatorPhaseKernel_le hsigma hh hp.1 hw phi)
      (norm_pairedEtaHeatCommutatorPhaseKernel_le htau hk hw hp.2 psi) (norm_nonneg _) (by positivity)
  simpa only [mul_assoc] using hfc.mul_bdd hm.aestronglyMeasurable hb

/-- Both literal multiplicity branches have genuine integrable ordered
two-transition kernels, with the head translation restored. -/
theorem integrable_leadingCurrent_twoTransition_insertions (rho : NontrivialZetaZero) (N : ℕ)
    {sigma h tau k w : ℝ} (hsigma : 0 ≤ sigma) (hh : 0 < h) (htau : 0 ≤ tau) (hk : 0 < k) (hw : 0 < w)
    {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (fun p : ℝ × ℝ ↦ (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p : ℂ) *
      pairedEtaHeatCommutatorPhaseKernel sigma h phi (p.1 + pairedEtaLogTailCutoff (N + 1), w) *
        pairedEtaHeatCommutatorPhaseKernel tau k psi (w, p.2))
      ((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))) ∧
    Integrable (fun p : ℝ × ℝ ↦ (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p : ℂ) *
      pairedEtaHeatCommutatorPhaseKernel sigma h phi (p.1, w) *
        pairedEtaHeatCommutatorPhaseKernel tau k psi (w, p.2))
      ((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2))) := by
  constructor
  · apply integrable_current_twoTransitions (integrable_topPrefixFiniteEnergyHeadKernel rho N)
      (fun p ↦ p.1 + pairedEtaLogTailCutoff (N + 1)) (measurable_fst.add_const _) _ hsigma hh htau hk hw hphi hpsi
    filter_upwards [ae_pair_mem_pairedEtaLogSupport_headMeasure N] with p hp
    exact ⟨pairedEtaLogSupport_subset_Ioi_zero hp.1, pairedEtaLogSupport_subset_Ioi_zero hp.2⟩
  · apply integrable_current_twoTransitions (integrable_topPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N)
      Prod.fst measurable_fst _ hsigma hh htau hk hw hphi hpsi
    filter_upwards [ae_pair_mem_pairedEtaLogSupport_finiteLogMeasure (N + 2)] with p hp
    exact ⟨pairedEtaLogSupport_subset_Ioi_zero hp.1, pairedEtaLogSupport_subset_Ioi_zero hp.2⟩

/-- The two exact gap-return kernels are also genuinely integrable on
their actual completed-current measures. -/
theorem integrable_leadingCurrent_gapReturn_insertions (rho : NontrivialZetaZero) (N : ℕ)
    {sigma h tau k w : ℝ} (hsigma : 0 ≤ sigma) (hh : 0 < h) (htau : 0 ≤ tau) (hk : 0 < k) (hw : 0 < w)
    {phi psi : ℝ → ℝ} (hphi : Measurable phi) (hpsi : Measurable psi) :
    Integrable (fun p : ℝ × ℝ ↦ (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p : ℂ) *
      pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi (p.1 + pairedEtaLogTailCutoff (N + 1)) p.2 w)
      ((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))) ∧
    Integrable (fun p : ℝ × ℝ ↦ (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p : ℂ) *
      pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi p.1 p.2 w)
      ((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2))) := by
  obtain ⟨hhead, hadj⟩ := integrable_leadingCurrent_twoTransition_insertions rho N hsigma hh htau hk hw hphi hpsi
  constructor
  · apply hhead.neg.congr
    filter_upwards [ae_head_current_two_transition_eq_gap_return rho N sigma h tau k phi psi hw] with p hp
    simpa only [Pi.neg_apply, neg_neg] using congrArg Neg.neg hp
  · apply hadj.neg.congr
    filter_upwards [ae_adjacent_current_two_transition_eq_gap_return rho N sigma h tau k phi psi hw] with p hp
    simpa only [Pi.neg_apply, neg_neg] using congrArg Neg.neg hp

/-- The completed current paired with two ordered actual heat transitions
at one fixed positive intermediate time. -/
def pairedEtaLeadingCurrentTwoTransitionPairing (rho : NontrivialZetaZero) (N : ℕ)
    (sigma h tau k : ℝ) (phi psi : ℝ → ℝ) (w : ℝ) : ℂ :=
  if analyticZetaZeroMultiplicity rho = 1 then
    ∫ p : ℝ × ℝ, (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p : ℂ) *
      pairedEtaHeatCommutatorPhaseKernel sigma h phi (p.1 + pairedEtaLogTailCutoff (N + 1), w) *
        pairedEtaHeatCommutatorPhaseKernel tau k psi (w, p.2)
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)))
  else
    ∫ p : ℝ × ℝ, (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p : ℂ) *
      pairedEtaHeatCommutatorPhaseKernel sigma h phi (p.1, w) * pairedEtaHeatCommutatorPhaseKernel tau k psi (w, p.2)
      ∂((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2)))

/-- The corresponding completed-current gap-return pairing, preserving
both ordered phase factors and the multiplicity-selected measure. -/
def pairedEtaLeadingCurrentGapReturnPairing (rho : NontrivialZetaZero) (N : ℕ)
    (sigma h tau k : ℝ) (phi psi : ℝ → ℝ) (w : ℝ) : ℂ :=
  if analyticZetaZeroMultiplicity rho = 1 then
    ∫ p : ℝ × ℝ, (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p : ℂ) *
      pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi (p.1 + pairedEtaLogTailCutoff (N + 1)) p.2 w
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)))
  else
    ∫ p : ℝ × ℝ, (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p : ℂ) *
      pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi p.1 p.2 w
      ∂((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2)))

/-- Exact completed-current pairing identity through the actual gap.
The preceding integrability theorems discharge convergence at nonnegative
tilts, positive widths, and measurable phases. -/
theorem pairedEtaLeadingCurrentTwoTransitionPairing_eq_neg_gapReturn (rho : NontrivialZetaZero) (N : ℕ)
    (sigma h tau k : ℝ) (phi psi : ℝ → ℝ) {w : ℝ} (hw : 0 < w) :
    pairedEtaLeadingCurrentTwoTransitionPairing rho N sigma h tau k phi psi w =
      -pairedEtaLeadingCurrentGapReturnPairing rho N sigma h tau k phi psi w := by
  unfold pairedEtaLeadingCurrentTwoTransitionPairing pairedEtaLeadingCurrentGapReturnPairing
  split
  · rw [integral_congr_ae (ae_head_current_two_transition_eq_gap_return rho N sigma h tau k phi psi hw), integral_neg]
  · rw [integral_congr_ae (ae_adjacent_current_two_transition_eq_gap_return rho N sigma h tau k phi psi hw), integral_neg]

/-- The reflection-closed polynomial phases and actual moving tilts satisfy
every integrability hypothesis of the completed gap-return pairing. The
zero, analytic multiplicity, cutoff, and intermediate time remain explicit. -/
theorem pairedEtaLeadingCurrentPolynomialReturn_audit (rho : NontrivialZetaZero) (N : ℕ)
    {lambda R w : ℝ} (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (hw : 0 < w)
    (kappa beta alpha : ℝ) :
    let h := Real.exp (-R)
    let sigma := pairedEtaMovingCriticalTilt lambda R
    let tau := pairedEtaMovingCriticalTilt (-lambda) R
    let phi := pairedEtaCriticalPolynomialPhase kappa beta alpha h R
    let psi := pairedEtaCriticalPolynomialPhase (kappa + beta + 3 * alpha) (-beta - 6 * alpha) alpha h R
    Integrable (fun p : ℝ × ℝ ↦ (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p : ℂ) *
      pairedEtaOrderedGapReturnKernelCore sigma h tau h phi psi (p.1 + pairedEtaLogTailCutoff (N + 1)) p.2 w)
      ((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))) ∧
    Integrable (fun p : ℝ × ℝ ↦ (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p : ℂ) *
      pairedEtaOrderedGapReturnKernelCore sigma h tau h phi psi p.1 p.2 w)
      ((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2))) ∧
    pairedEtaLeadingCurrentTwoTransitionPairing rho N sigma h tau h phi psi w =
      -pairedEtaLeadingCurrentGapReturnPairing rho N sigma h tau h phi psi w := by
  dsimp only
  have hs : 0 ≤ pairedEtaMovingCriticalTilt lambda R := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (pairedEtaMovingCriticalTilt_lower (by linarith) hlarge)
  have ht : 0 ≤ pairedEtaMovingCriticalTilt (-lambda) R := le_trans (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (pairedEtaMovingCriticalTilt_lower (by linarith) (by simpa only [abs_neg] using hlarge))
  have hi := integrable_leadingCurrent_gapReturn_insertions rho N hs (Real.exp_pos (-R)) ht (Real.exp_pos (-R)) hw
    (continuous_pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R).measurable
    (continuous_pairedEtaCriticalPolynomialPhase (kappa + beta + 3 * alpha) (-beta - 6 * alpha)
      alpha (Real.exp (-R)) R).measurable
  exact ⟨hi.1, hi.2, pairedEtaLeadingCurrentTwoTransitionPairing_eq_neg_gapReturn rho N _ _ _ _ _ _ hw⟩

end

end RiemannGaussian
