import RiemannGaussian.Hybrid.EtaPolynomialHeatMatrix
import RiemannGaussian.Hybrid.EtaSupportGapHeatCommutator
import RiemannGaussian.EtaEnergyLeadingFluxKernelFactorization

/-!
# Exact carrier audit of signed eta heat against the completed current

The direct signed support/gap insertion vanishes on both literal current
carriers, including the multiplicity-one head after restoring its original
time coordinate. A separate ordered two-transition identity retains the
gap-return channel. These identities do not estimate the completed current
or its cutoff-weighted first absolute moment.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ENNReal NNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Almost every point of the finite eta measure belongs to the actual infinite support. -/
theorem ae_mem_pairedEtaLogSupport_finiteLogMeasure (N : ℕ) :
    ∀ᵐ t : ℝ ∂pairedEtaFiniteLogMeasure N, t ∈ pairedEtaLogSupport := by
  unfold pairedEtaFiniteLogMeasure
  rw [ae_finsetSum_measure_iff]
  intro n _
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact mem_iUnion.mpr ⟨n, ht⟩

/-- Restoring the head translation places almost every head point in the
actual support interval at the original arithmetic cutoff. -/
theorem ae_add_cutoff_mem_pairedEtaLogSupport_shiftedHeadMeasure (N : ℕ) :
    ∀ᵐ t : ℝ ∂pairedEtaShiftedLogHeadMeasure N,
      t + pairedEtaLogTailCutoff N ∈ pairedEtaLogSupport := by
  rw [pairedEtaShiftedLogHeadMeasure_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  apply mem_iUnion.mpr
  refine ⟨N, ?_⟩
  have hx : t + pairedEtaLogTailCutoff N ∈
      Ioc (pairedEtaLogTailCutoff N) (Real.log (((2 * N + 2 : ℕ) : ℝ))) := by
    constructor
    · linarith [ht.1]
    · have h := ht.2
      unfold pairedEtaShiftedLogHeadWidth at h
      linarith
  simpa only [pairedEtaLogInterval, pairedEtaLogTailCutoff, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one] using hx

/-- Both coordinates of the finite current measure lie on the actual eta support almost everywhere. -/
theorem ae_pair_mem_pairedEtaLogSupport_finiteLogMeasure (N : ℕ) :
    ∀ᵐ p : ℝ × ℝ ∂(pairedEtaFiniteLogMeasure N).prod (pairedEtaFiniteLogMeasure N),
      p.1 ∈ pairedEtaLogSupport ∧ p.2 ∈ pairedEtaLogSupport := by
  have hm : MeasurableSet {p : ℝ × ℝ | p.1 ∈ pairedEtaLogSupport ∧ p.2 ∈ pairedEtaLogSupport} :=
    (measurableSet_pairedEtaLogSupport.preimage measurable_fst).inter
      (measurableSet_pairedEtaLogSupport.preimage measurable_snd)
  rw [Measure.ae_prod_iff_ae_ae hm]
  filter_upwards [ae_mem_pairedEtaLogSupport_finiteLogMeasure N] with t ht
  filter_upwards [ae_mem_pairedEtaLogSupport_finiteLogMeasure N] with u hu
  exact ⟨ht, hu⟩

/-- The physical head coordinate and its successor-prefix partner both lie on support. -/
theorem ae_pair_mem_pairedEtaLogSupport_headMeasure (N : ℕ) :
    ∀ᵐ p : ℝ × ℝ ∂(pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)),
      p.1 + pairedEtaLogTailCutoff (N + 1) ∈ pairedEtaLogSupport ∧ p.2 ∈ pairedEtaLogSupport := by
  have hm : MeasurableSet {p : ℝ × ℝ |
      p.1 + pairedEtaLogTailCutoff (N + 1) ∈ pairedEtaLogSupport ∧ p.2 ∈ pairedEtaLogSupport} :=
    (measurableSet_pairedEtaLogSupport.preimage (measurable_fst.add_const _)).inter
      (measurableSet_pairedEtaLogSupport.preimage measurable_snd)
  rw [Measure.ae_prod_iff_ae_ae hm]
  filter_upwards [ae_add_cutoff_mem_pairedEtaLogSupport_shiftedHeadMeasure (N + 1)] with t ht
  filter_upwards [ae_mem_pairedEtaLogSupport_finiteLogMeasure (N + 2)] with u hu
  exact ⟨ht, hu⟩

/-- A single actual support/gap heat kernel vanishes between two support points. -/
theorem pairedEtaSupportGapHeatKernel_eq_zero_on_support (sigma h : ℝ) (phi : ℝ → ℝ)
    {t u : ℝ} (ht : t ∈ pairedEtaLogSupport) (hu : u ∈ pairedEtaLogSupport) :
    pairedEtaSupportGapHeatKernel sigma h phi (t, u) = 0 := by
  simp only [pairedEtaSupportGapHeatKernel, pairedEtaSupportGapHeatWeight,
    pairedEtaLogShiftMismatch_sub, pairedEtaLogIndicator, Set.indicator_of_mem ht,
    Set.indicator_of_mem hu, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul]

/-- The exact signed two-time kernel of the reflected polynomial heat. -/
def pairedEtaSignedPolynomialHeatKernel (lambda kappa beta alpha R : ℝ) (p : ℝ × ℝ) : ℝ :=
  pairedEtaSupportGapHeatKernel (pairedEtaMovingCriticalTilt lambda R) (Real.exp (-R))
    (pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R) p -
  Real.exp (-2 * lambda) *
    pairedEtaSupportGapHeatKernel (pairedEtaMovingCriticalTilt (-lambda) R) (Real.exp (-R))
      (pairedEtaCriticalPolynomialPhase (kappa + beta + 3 * alpha) (-beta - 6 * alpha) alpha (Real.exp (-R)) R) p

/-- The signed kernel is genuinely integrable on the positive-time plane
in the same eventual tilt range as the heat theorem. -/
theorem integrable_pairedEtaSignedPolynomialHeatKernel {lambda R : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (kappa beta alpha : ℝ) :
    Integrable (pairedEtaSignedPolynomialHeatKernel lambda kappa beta alpha R)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hs : 0 < pairedEtaMovingCriticalTilt lambda R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (pairedEtaMovingCriticalTilt_lower (by linarith) hlarge)
  have hsr : 0 < pairedEtaMovingCriticalTilt (-lambda) R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (pairedEtaMovingCriticalTilt_lower (by linarith) (by simpa only [abs_neg] using hlarge))
  exact (integrable_pairedEtaSupportGapHeatKernel hs (Real.exp_pos _)
    (continuous_pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R).measurable).sub
    ((integrable_pairedEtaSupportGapHeatKernel hsr (Real.exp_pos _)
      (continuous_pairedEtaCriticalPolynomialPhase (kappa + beta + 3 * alpha)
        (-beta - 6 * alpha) alpha (Real.exp (-R)) R).measurable).const_mul (Real.exp (-2 * lambda)))

/-- Integrating the retained signed kernel gives exactly the actual
reflected heat used in the second-order theorem. -/
theorem integral_pairedEtaSignedPolynomialHeatKernel {lambda R : ℝ}
    (hR : 1 ≤ R) (hlarge : 4 * |lambda| ≤ R) (kappa beta alpha : ℝ) :
    (∫ p : ℝ × ℝ, pairedEtaSignedPolynomialHeatKernel lambda kappa beta alpha R p
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      pairedEtaSignedPolynomialHeat lambda kappa beta alpha R := by
  have hs : 0 < pairedEtaMovingCriticalTilt lambda R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (pairedEtaMovingCriticalTilt_lower (by linarith) hlarge)
  have hsr : 0 < pairedEtaMovingCriticalTilt (-lambda) R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 4)
    (pairedEtaMovingCriticalTilt_lower (by linarith) (by simpa only [abs_neg] using hlarge))
  unfold pairedEtaSignedPolynomialHeatKernel pairedEtaSignedPolynomialHeat pairedEtaSupportGapGaussianLeakage
  rw [integral_sub (integrable_pairedEtaSupportGapHeatKernel hs (Real.exp_pos _)
    (continuous_pairedEtaCriticalPolynomialPhase kappa beta alpha (Real.exp (-R)) R).measurable)
    ((integrable_pairedEtaSupportGapHeatKernel hsr (Real.exp_pos _)
      (continuous_pairedEtaCriticalPolynomialPhase (kappa + beta + 3 * alpha)
        (-beta - 6 * alpha) alpha (Real.exp (-R)) R).measurable).const_mul _), integral_const_mul]

/-- Signed reflection still vanishes on support times support. -/
theorem pairedEtaSignedPolynomialHeatKernel_eq_zero_on_support (lambda kappa beta alpha R : ℝ)
    {t u : ℝ} (ht : t ∈ pairedEtaLogSupport) (hu : u ∈ pairedEtaLogSupport) :
    pairedEtaSignedPolynomialHeatKernel lambda kappa beta alpha R (t, u) = 0 := by
  simp only [pairedEtaSignedPolynomialHeatKernel, pairedEtaSupportGapHeatKernel_eq_zero_on_support _ _ _ ht hu,
    mul_zero, sub_self]

/-- The actual adjacent-moment current times the signed heat kernel is zero
almost everywhere, retaining the real zero, cutoff, and completion factors. -/
theorem ae_adjacentMoment_signedHeat_insertion_eq_zero (rho : NontrivialZetaZero) (N : ℕ)
    (lambda kappa beta alpha R : ℝ) :
    (fun p : ℝ × ℝ ↦ pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p *
      pairedEtaSignedPolynomialHeatKernel lambda kappa beta alpha R p) =ᵐ[
        (pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2))] 0 := by
  filter_upwards [ae_pair_mem_pairedEtaLogSupport_finiteLogMeasure (N + 2)] with p hp
  change _ * _ = (0 : ℝ)
  rw [show pairedEtaSignedPolynomialHeatKernel lambda kappa beta alpha R p = 0 from
    pairedEtaSignedPolynomialHeatKernel_eq_zero_on_support _ _ _ _ _ hp.1 hp.2, mul_zero]

/-- The distinct head current also has zero direct insertion after restoring
the translated head to its original support coordinate. -/
theorem ae_head_signedHeat_insertion_eq_zero (rho : NontrivialZetaZero) (N : ℕ)
    (lambda kappa beta alpha R : ℝ) :
    (fun p : ℝ × ℝ ↦ pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p *
      pairedEtaSignedPolynomialHeatKernel lambda kappa beta alpha R (p.1 + pairedEtaLogTailCutoff (N + 1), p.2)) =ᵐ[
        (pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))] 0 := by
  filter_upwards [ae_pair_mem_pairedEtaLogSupport_headMeasure N] with p hp
  change _ * _ = (0 : ℝ)
  rw [pairedEtaSignedPolynomialHeatKernel_eq_zero_on_support _ _ _ _ _ hp.1 hp.2, mul_zero]

/-- Direct insertion of the new signed heat into the literal
multiplicity-selected completed current, with the head translation retained. -/
def pairedEtaLeadingCurrentSignedHeatPairing (rho : NontrivialZetaZero) (N : ℕ)
    (lambda kappa beta alpha R : ℝ) : ℝ :=
  if analyticZetaZeroMultiplicity rho = 1 then
    ∫ p : ℝ × ℝ, pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p *
      pairedEtaSignedPolynomialHeatKernel lambda kappa beta alpha R (p.1 + pairedEtaLogTailCutoff (N + 1), p.2)
      ∂((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)))
  else
    ∫ p : ℝ × ℝ, pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p *
      pairedEtaSignedPolynomialHeatKernel lambda kappa beta alpha R p
      ∂((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2)))

/-- Both literal current insertions are genuinely integrable because their
integrands vanish almost everywhere; no divergent integral is totalized. -/
theorem integrable_leadingCurrent_signedHeat_insertions (rho : NontrivialZetaZero) (N : ℕ)
    (lambda kappa beta alpha R : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦ pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p *
      pairedEtaSignedPolynomialHeatKernel lambda kappa beta alpha R (p.1 + pairedEtaLogTailCutoff (N + 1), p.2))
      ((pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2))) ∧
    Integrable (fun p : ℝ × ℝ ↦ pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p *
      pairedEtaSignedPolynomialHeatKernel lambda kappa beta alpha R p)
      ((pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2))) := by
  exact ⟨(integrable_zero (ℝ × ℝ) ℝ _).congr (ae_head_signedHeat_insertion_eq_zero rho N lambda kappa beta alpha R).symm,
    (integrable_zero (ℝ × ℝ) ℝ _).congr (ae_adjacentMoment_signedHeat_insertion_eq_zero rho N lambda kappa beta alpha R).symm⟩

/-- The audited direct pairing is identically zero for every actual zero
and cutoff, in both multiplicity branches. It therefore does not recover
the completed leading current by insertion of a support/gap factor. -/
theorem pairedEtaLeadingCurrentSignedHeatPairing_eq_zero (rho : NontrivialZetaZero) (N : ℕ)
    (lambda kappa beta alpha R : ℝ) :
    pairedEtaLeadingCurrentSignedHeatPairing rho N lambda kappa beta alpha R = 0 := by
  unfold pairedEtaLeadingCurrentSignedHeatPairing
  split
  · rw [integral_congr_ae (ae_head_signedHeat_insertion_eq_zero rho N lambda kappa beta alpha R)]
    simp
  · rw [integral_congr_ae (ae_adjacentMoment_signedHeat_insertion_eq_zero rho N lambda kappa beta alpha R)]
    simp

/-- The ordered return kernel through the actual gap. Both heat widths,
horizontal tilts, and phase channels remain explicit. -/
def pairedEtaOrderedGapReturnKernelCore (sigma h tau k : ℝ) (phi psi : ℝ → ℝ)
    (t u w : ℝ) : ℂ :=
  ((Real.exp (-sigma * (t + w) / 2) * etaNormalizedHeatKernel (Real.sqrt 2 * h) (w - t) *
    Real.exp (-tau * (w + u) / 2) * etaNormalizedHeatKernel (Real.sqrt 2 * k) (u - w) *
    (1 - pairedEtaLogIndicator w) : ℝ) : ℂ) *
    pairedEtaHeatPhaseUnit phi (w, t) * pairedEtaHeatPhaseUnit psi (u, w)

/-- Two actual continuous support/heat commutators return to the support
through the gap, with a negative sign and both phase/time orderings retained. -/
theorem pairedEtaHeatCommutatorPhaseKernel_two_transition (sigma h tau k : ℝ) (phi psi : ℝ → ℝ)
    {t u w : ℝ} (ht : t ∈ pairedEtaLogSupport) (hu : u ∈ pairedEtaLogSupport) (hw : 0 < w) :
    pairedEtaHeatCommutatorPhaseKernel sigma h phi (t, w) *
      pairedEtaHeatCommutatorPhaseKernel tau k psi (w, u) =
      -pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi t u w := by
  have ht0 : 0 < t := pairedEtaLogSupport_subset_Ioi_zero ht
  have hu0 : 0 < u := pairedEtaLogSupport_subset_Ioi_zero hu
  have hct : pairedEtaLogIndicator t = 1 := by simp only [pairedEtaLogIndicator, Set.indicator_of_mem ht]
  have hcu : pairedEtaLogIndicator u = 1 := by simp only [pairedEtaLogIndicator, Set.indicator_of_mem hu]
  have hp : (t, w) ∈ (Ioi (0 : ℝ)) ×ˢ (Ioi 0) := ⟨ht0, hw⟩
  have hq : (w, u) ∈ (Ioi (0 : ℝ)) ×ˢ (Ioi 0) := ⟨hw, hu0⟩
  simp only [pairedEtaHeatCommutatorPhaseKernel, pairedEtaHeatCommutatorKernel,
    Set.indicator_of_mem hp, Set.indicator_of_mem hq, pairedEtaHeatCommutatorKernelCore,
    pairedEtaOrderedGapReturnKernelCore, hct, hcu]
  rcases pairedEtaLogIndicator_eq_zero_or_one w with hc | hc
  · simp [hc]
    ring
  · simp [hc]

/-- The ordered two-transition identity on the literal completed adjacent
current retains all completion and multiplicity-dependent moment factors. -/
theorem ae_adjacent_current_two_transition_eq_gap_return (rho : NontrivialZetaZero) (N : ℕ)
    (sigma h tau k : ℝ) (phi psi : ℝ → ℝ) {w : ℝ} (hw : 0 < w) :
    ∀ᵐ p : ℝ × ℝ ∂(pairedEtaFiniteLogMeasure (N + 2)).prod (pairedEtaFiniteLogMeasure (N + 2)),
      (pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p : ℂ) *
        pairedEtaHeatCommutatorPhaseKernel sigma h phi (p.1, w) *
          pairedEtaHeatCommutatorPhaseKernel tau k psi (w, p.2) =
      -((pairedEtaTopPrefixFiniteEnergyFactoredAdjacentMomentKernel rho N p : ℂ) *
        pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi p.1 p.2 w) := by
  filter_upwards [ae_pair_mem_pairedEtaLogSupport_finiteLogMeasure (N + 2)] with p hp
  rw [mul_assoc, pairedEtaHeatCommutatorPhaseKernel_two_transition sigma h tau k phi psi hp.1 hp.2 hw, mul_neg]

/-- The same ordered return identity on the distinct head current uses its
restored physical coordinate and retains the negative completed head feature. -/
theorem ae_head_current_two_transition_eq_gap_return (rho : NontrivialZetaZero) (N : ℕ)
    (sigma h tau k : ℝ) (phi psi : ℝ → ℝ) {w : ℝ} (hw : 0 < w) :
    ∀ᵐ p : ℝ × ℝ ∂(pairedEtaShiftedLogHeadMeasure (N + 1)).prod (pairedEtaFiniteLogMeasure (N + 2)),
      (pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p : ℂ) *
        pairedEtaHeatCommutatorPhaseKernel sigma h phi (p.1 + pairedEtaLogTailCutoff (N + 1), w) *
          pairedEtaHeatCommutatorPhaseKernel tau k psi (w, p.2) =
      -((pairedEtaTopPrefixFiniteEnergyHeadKernel rho N p : ℂ) *
        pairedEtaOrderedGapReturnKernelCore sigma h tau k phi psi
          (p.1 + pairedEtaLogTailCutoff (N + 1)) p.2 w) := by
  filter_upwards [ae_pair_mem_pairedEtaLogSupport_headMeasure N] with p hp
  rw [mul_assoc, pairedEtaHeatCommutatorPhaseKernel_two_transition sigma h tau k phi psi hp.1 hp.2 hw, mul_neg]

end

end RiemannGaussian
