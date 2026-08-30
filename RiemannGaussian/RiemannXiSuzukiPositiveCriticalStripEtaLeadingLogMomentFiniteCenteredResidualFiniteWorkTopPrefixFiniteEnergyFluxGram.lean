import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixFiniteEnergyFluxWeightedSummability

/-!
# Finite eta Gram kernel for the successor energy flux

The previous module isolates the successor cross flux as the entire remaining
critical first-moment obstruction.  Here that scalar is returned to the
literal finite positive eta measure.

At cutoff `N`, each explicit head-plus-lower-prefix arithmetic increment is
paired with the corresponding completed successor feature at cutoff `N+1`.
The difference of the two real Hermitian pairings is an integrable kernel on
`pairedEtaFiniteLogMeasure (N+2)`, and its integral is exactly the successor
energy flux.  A pointwise phase-free envelope yields a nonnegative global
cancellation reserve with the exact ledger

`|flux_N| + reserve_N = integral envelope_N`.

The functional-equation partner swaps the two component amplitudes and
increment energies.  Lean consequently proves that the signed energy, its
work, its increment energy, and its successor flux are all odd under partner
reflection, while the absolute flux is invariant.  The critical first-moment
criterion is finally restated as summability of the absolute integrals of the
literal finite kernels.  This is a representation of the live arithmetic
cancellation problem, not an estimate solving it.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Real Hermitian pairing of the explicit reflected-partner arithmetic
increment with its successor finite eta feature. -/
def pairedEtaTopPrefixFinitePartnerFluxKernel
    (rho : NontrivialZetaZero) (N : ℕ) (t : ℝ) : ℝ :=
  2 *
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
        rho N *
      starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
          rho (N + 1) t)).re

/-- Real Hermitian pairing of the explicit conjugate-original arithmetic
increment with its successor finite eta feature. -/
def pairedEtaTopPrefixFiniteConjugateFluxKernel
    (rho : NontrivialZetaZero) (N : ℕ) (t : ℝ) : ℝ :=
  2 *
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
        rho N *
      starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
          rho (N + 1) t)).re

/-- Signed finite eta kernel whose integral is the successor energy flux. -/
def pairedEtaTopPrefixFiniteEnergyFluxKernel
    (rho : NontrivialZetaZero) (N : ℕ) (t : ℝ) : ℝ :=
  pairedEtaTopPrefixFinitePartnerFluxKernel rho N t -
    pairedEtaTopPrefixFiniteConjugateFluxKernel rho N t

/-- Phase-free pointwise envelope for the signed successor-flux kernel. -/
def pairedEtaTopPrefixFiniteEnergyFluxEnvelope
    (rho : NontrivialZetaZero) (N : ℕ) (t : ℝ) : ℝ :=
  2 *
    (‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
          rho N‖ *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
          rho (N + 1) t‖ +
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
          rho N‖ *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
          rho (N + 1) t‖)

private theorem integrable_star_of_integrable_fluxGram
    {μ : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f μ) :
    Integrable (fun t : ℝ => starRingEnd ℂ (f t)) μ := by
  apply ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hf).congr
  filter_upwards with t
  exact Complex.conjCLE_apply _

/-- The reflected-partner successor-flux kernel is integrable on the finite
positive eta measure at the successor cutoff. -/
theorem integrable_pairedEtaTopPrefixFinitePartnerFluxKernel
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (pairedEtaTopPrefixFinitePartnerFluxKernel rho N)
      (pairedEtaFiniteLogMeasure (N + 2)) := by
  have hfeature := integrable_topPrefixFinitePartnerFeature rho (N + 1)
  have hcomplex :=
    (integrable_star_of_integrable_fluxGram hfeature).const_mul
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
        rho N)
  exact hcomplex.re.const_mul 2

/-- The conjugate-original successor-flux kernel is integrable on the finite
positive eta measure at the successor cutoff. -/
theorem integrable_pairedEtaTopPrefixFiniteConjugateFluxKernel
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (pairedEtaTopPrefixFiniteConjugateFluxKernel rho N)
      (pairedEtaFiniteLogMeasure (N + 2)) := by
  have hfeature := integrable_topPrefixFiniteConjugateFeature rho (N + 1)
  have hcomplex :=
    (integrable_star_of_integrable_fluxGram hfeature).const_mul
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
        rho N)
  exact hcomplex.re.const_mul 2

/-- The signed successor-flux kernel is integrable. -/
theorem integrable_pairedEtaTopPrefixFiniteEnergyFluxKernel
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (pairedEtaTopPrefixFiniteEnergyFluxKernel rho N)
      (pairedEtaFiniteLogMeasure (N + 2)) :=
  (integrable_pairedEtaTopPrefixFinitePartnerFluxKernel rho N).sub
    (integrable_pairedEtaTopPrefixFiniteConjugateFluxKernel rho N)

/-- The phase-free successor-flux envelope is integrable. -/
theorem integrable_pairedEtaTopPrefixFiniteEnergyFluxEnvelope
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable (pairedEtaTopPrefixFiniteEnergyFluxEnvelope rho N)
      (pairedEtaFiniteLogMeasure (N + 2)) := by
  have hp :=
    (integrable_topPrefixFinitePartnerFeature rho (N + 1)).norm.const_mul
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
        rho N‖
  have hq :=
    (integrable_topPrefixFiniteConjugateFeature rho (N + 1)).norm.const_mul
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
        rho N‖
  exact (hp.add hq).const_mul 2

/-- The phase-free successor-flux envelope is pointwise nonnegative. -/
theorem pairedEtaTopPrefixFiniteEnergyFluxEnvelope_nonneg
    (rho : NontrivialZetaZero) (N : ℕ) (t : ℝ) :
    0 ≤ pairedEtaTopPrefixFiniteEnergyFluxEnvelope rho N t := by
  unfold pairedEtaTopPrefixFiniteEnergyFluxEnvelope
  positivity

/-- The absolute signed successor-flux kernel is pointwise bounded by its
phase-free envelope. -/
theorem abs_pairedEtaTopPrefixFiniteEnergyFluxKernel_le_envelope
    (rho : NontrivialZetaZero) (N : ℕ) (t : ℝ) :
    |pairedEtaTopPrefixFiniteEnergyFluxKernel rho N t| ≤
      pairedEtaTopPrefixFiniteEnergyFluxEnvelope rho N t := by
  let p : ℝ :=
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
        rho N *
      starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
          rho (N + 1) t)).re
  let q : ℝ :=
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
        rho N *
      starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
          rho (N + 1) t)).re
  have hp : |p| ≤
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
          rho N‖ *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
          rho (N + 1) t‖ := by
    calc
      |p| ≤
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
              rho N *
            starRingEnd ℂ
              (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
                rho (N + 1) t)‖ := Complex.abs_re_le_norm _
      _ = _ := by rw [norm_mul, norm_conj]
  have hq : |q| ≤
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
          rho N‖ *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
          rho (N + 1) t‖ := by
    calc
      |q| ≤
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
              rho N *
            starRingEnd ℂ
              (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
                rho (N + 1) t)‖ := Complex.abs_re_le_norm _
      _ = _ := by rw [norm_mul, norm_conj]
  have hpq : |p - q| ≤ |p| + |q| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le p (-q)
  unfold pairedEtaTopPrefixFiniteEnergyFluxKernel
    pairedEtaTopPrefixFinitePartnerFluxKernel
    pairedEtaTopPrefixFiniteConjugateFluxKernel
    pairedEtaTopPrefixFiniteEnergyFluxEnvelope
  change |2 * p - 2 * q| ≤ _
  rw [show 2 * p - 2 * q = 2 * (p - q) by ring, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (hpq.trans (add_le_add hp hq)) (by norm_num)

/-- Integrating the reflected-partner kernel gives its exact arithmetic
increment--successor Hermitian pairing. -/
theorem integral_pairedEtaTopPrefixFinitePartnerFluxKernel_eq
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ t : ℝ, pairedEtaTopPrefixFinitePartnerFluxKernel rho N t
      ∂pairedEtaFiniteLogMeasure (N + 2)) =
      2 *
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
            rho N *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
              rho (N + 1))).re := by
  have hcomplex : Integrable (fun t : ℝ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
          rho N *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
            rho (N + 1) t))
      (pairedEtaFiniteLogMeasure (N + 2)) :=
    (integrable_star_of_integrable_fluxGram
      (integrable_topPrefixFinitePartnerFeature rho (N + 1))).const_mul _
  unfold pairedEtaTopPrefixFinitePartnerFluxKernel
  rw [integral_const_mul]
  congr 1
  calc
    (∫ t : ℝ,
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
            rho N *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
              rho (N + 1) t)).re
        ∂pairedEtaFiniteLogMeasure (N + 2)) =
        (∫ t : ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
              rho N *
            starRingEnd ℂ
              (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
                rho (N + 1) t)
          ∂pairedEtaFiniteLogMeasure (N + 2)).re := integral_re hcomplex
    _ = _ := by
      rw [integral_const_mul, integral_conj,
        integral_topPrefixFinitePartnerFeature_eq_finitePartnerTerm]

/-- Integrating the conjugate-original kernel gives its exact arithmetic
increment--successor Hermitian pairing. -/
theorem integral_pairedEtaTopPrefixFiniteConjugateFluxKernel_eq
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ t : ℝ, pairedEtaTopPrefixFiniteConjugateFluxKernel rho N t
      ∂pairedEtaFiniteLogMeasure (N + 2)) =
      2 *
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
            rho N *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
              rho (N + 1))).re := by
  have hcomplex : Integrable (fun t : ℝ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
          rho N *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
            rho (N + 1) t))
      (pairedEtaFiniteLogMeasure (N + 2)) :=
    (integrable_star_of_integrable_fluxGram
      (integrable_topPrefixFiniteConjugateFeature rho (N + 1))).const_mul _
  unfold pairedEtaTopPrefixFiniteConjugateFluxKernel
  rw [integral_const_mul]
  congr 1
  calc
    (∫ t : ℝ,
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
            rho N *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
              rho (N + 1) t)).re
        ∂pairedEtaFiniteLogMeasure (N + 2)) =
        (∫ t : ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
              rho N *
            starRingEnd ℂ
              (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
                rho (N + 1) t)
          ∂pairedEtaFiniteLogMeasure (N + 2)).re := integral_re hcomplex
    _ = _ := by
      rw [integral_const_mul, integral_conj,
        integral_topPrefixFiniteConjugateFeature_eq_finiteConjugateTerm]

/-- Exact finite positive-measure representation of the successor energy
flux by the signed eta Gram kernel. -/
theorem integral_pairedEtaTopPrefixFiniteEnergyFluxKernel_eq_flux
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ t : ℝ, pairedEtaTopPrefixFiniteEnergyFluxKernel rho N t
      ∂pairedEtaFiniteLogMeasure (N + 2)) =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
        rho N := by
  unfold pairedEtaTopPrefixFiniteEnergyFluxKernel
  rw [integral_sub
      (integrable_pairedEtaTopPrefixFinitePartnerFluxKernel rho N)
      (integrable_pairedEtaTopPrefixFiniteConjugateFluxKernel rho N),
    integral_pairedEtaTopPrefixFinitePartnerFluxKernel_eq,
    integral_pairedEtaTopPrefixFiniteConjugateFluxKernel_eq]
  rw [← topPrefixFinitePartnerIncrement_eq_arithmeticIncrement,
    ← topPrefixFiniteConjugateIncrement_eq_arithmeticIncrement]
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
  ring

/-- The absolute successor flux is bounded by the integral of its phase-free
finite eta envelope. -/
theorem abs_topPrefixFiniteEnergyFlux_le_integral_envelope
    (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
        rho N| ≤
      ∫ t : ℝ, pairedEtaTopPrefixFiniteEnergyFluxEnvelope rho N t
        ∂pairedEtaFiniteLogMeasure (N + 2) := by
  have hnorm := norm_integral_le_integral_norm
    (μ := pairedEtaFiniteLogMeasure (N + 2))
    (pairedEtaTopPrefixFiniteEnergyFluxKernel rho N)
  have hmono :
      (∫ t : ℝ, ‖pairedEtaTopPrefixFiniteEnergyFluxKernel rho N t‖
        ∂pairedEtaFiniteLogMeasure (N + 2)) ≤
      ∫ t : ℝ, pairedEtaTopPrefixFiniteEnergyFluxEnvelope rho N t
        ∂pairedEtaFiniteLogMeasure (N + 2) := by
    apply integral_mono_ae
      (integrable_pairedEtaTopPrefixFiniteEnergyFluxKernel rho N).norm
      (integrable_pairedEtaTopPrefixFiniteEnergyFluxEnvelope rho N)
    exact Eventually.of_forall fun t => by
      simpa only [Real.norm_eq_abs] using
        abs_pairedEtaTopPrefixFiniteEnergyFluxKernel_le_envelope rho N t
  calc
    |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
        rho N| =
        ‖∫ t : ℝ, pairedEtaTopPrefixFiniteEnergyFluxKernel rho N t
          ∂pairedEtaFiniteLogMeasure (N + 2)‖ := by
      rw [integral_pairedEtaTopPrefixFiniteEnergyFluxKernel_eq_flux,
        Real.norm_eq_abs]
    _ ≤ ∫ t : ℝ, ‖pairedEtaTopPrefixFiniteEnergyFluxKernel rho N t‖
          ∂pairedEtaFiniteLogMeasure (N + 2) := hnorm
    _ ≤ _ := hmono

/-- The phase-free envelope integral is the explicit sum of the two
increment norms times the `L¹` masses of their successor features. -/
theorem integral_pairedEtaTopPrefixFiniteEnergyFluxEnvelope_eq
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ t : ℝ, pairedEtaTopPrefixFiniteEnergyFluxEnvelope rho N t
      ∂pairedEtaFiniteLogMeasure (N + 2)) =
      2 *
        (‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerArithmeticIncrement
              rho N‖ *
            (∫ t : ℝ,
              ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerFeature
                rho (N + 1) t‖
              ∂pairedEtaFiniteLogMeasure (N + 2)) +
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateArithmeticIncrement
              rho N‖ *
            ∫ t : ℝ,
              ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateFeature
                rho (N + 1) t‖
              ∂pairedEtaFiniteLogMeasure (N + 2)) := by
  unfold pairedEtaTopPrefixFiniteEnergyFluxEnvelope
  rw [integral_const_mul]
  rw [integral_add
    ((integrable_topPrefixFinitePartnerFeature rho (N + 1)).norm.const_mul _)
    ((integrable_topPrefixFiniteConjugateFeature rho (N + 1)).norm.const_mul _)]
  rw [integral_const_mul, integral_const_mul]

/-- The phase-cancellation reserve left after subtracting the absolute signed
flux from its phase-free envelope integral. -/
def pairedEtaTopPrefixFiniteEnergyFluxCancellationReserve
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  (∫ t : ℝ, pairedEtaTopPrefixFiniteEnergyFluxEnvelope rho N t
    ∂pairedEtaFiniteLogMeasure (N + 2)) -
    |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
      rho N|

/-- The finite successor-flux cancellation reserve is nonnegative. -/
theorem pairedEtaTopPrefixFiniteEnergyFluxCancellationReserve_nonneg
    (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤ pairedEtaTopPrefixFiniteEnergyFluxCancellationReserve rho N := by
  unfold pairedEtaTopPrefixFiniteEnergyFluxCancellationReserve
  exact sub_nonneg.mpr (abs_topPrefixFiniteEnergyFlux_le_integral_envelope rho N)

/-- Exact phase-cancellation ledger for the finite successor flux. -/
theorem abs_flux_add_cancellationReserve_eq_integral_envelope
    (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
        rho N| +
        pairedEtaTopPrefixFiniteEnergyFluxCancellationReserve rho N =
      ∫ t : ℝ, pairedEtaTopPrefixFiniteEnergyFluxEnvelope rho N t
        ∂pairedEtaFiniteLogMeasure (N + 2) := by
  unfold pairedEtaTopPrefixFiniteEnergyFluxCancellationReserve
  ring

/-- Partner reflection swaps the two finite component amplitudes. -/
theorem topPrefixFinitePartnerAmplitude_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
        (NontrivialZetaZero.conjugatePartner rho) N =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
        rho N := by
  simp only [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude,
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude,
    NontrivialZetaZero.conjugatePartner_conjugatePartner,
    analyticZetaZeroMultiplicity_conjugatePartner]

/-- Partner reflection swaps the conjugate and reflected finite component
amplitudes in the reverse direction. -/
theorem topPrefixFiniteConjugateAmplitude_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
        (NontrivialZetaZero.conjugatePartner rho) N =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
        rho N := by
  simp only [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude,
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude,
    analyticZetaZeroMultiplicity_conjugatePartner]

/-- The signed finite energy is odd under functional-equation partner
reflection. -/
theorem topPrefixFiniteEnergyDifference_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        (NontrivialZetaZero.conjugatePartner rho) N =
      -pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
  rw [topPrefixFinitePartnerAmplitude_conjugatePartner,
    topPrefixFiniteConjugateAmplitude_conjugatePartner]
  ring

/-- Consecutive signed finite energy work is odd under partner reflection. -/
theorem topPrefixFiniteEnergyWork_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
        (NontrivialZetaZero.conjugatePartner rho) N =
      -pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
  rw [topPrefixFiniteEnergyDifference_conjugatePartner rho N,
    topPrefixFiniteEnergyDifference_conjugatePartner rho (N + 1)]
  ring

/-- Partner reflection swaps the squared norms of the partner and conjugate
finite increments. -/
theorem normSq_topPrefixFinitePartnerIncrement_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    Complex.normSq
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
          (NontrivialZetaZero.conjugatePartner rho) N) =
      Complex.normSq
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
          rho N) := by
  have hparity : Complex.normSq
      ((-1 : ℂ) ^ analyticZetaZeroMultiplicity rho) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, norm_neg, norm_one, one_pow]
    norm_num
  have hrelation :
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
          rho N =
        (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
              (NontrivialZetaZero.conjugatePartner rho) N) := by
    unfold
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
    simp only [NontrivialZetaZero.conjugatePartner_conjugatePartner,
      analyticZetaZeroMultiplicity_conjugatePartner, map_sub]
    ring
  rw [hrelation, Complex.normSq_mul, Complex.normSq_conj, hparity, one_mul]

/-- Partner reflection swaps the squared norms of the conjugate and partner
finite increments in the reverse direction. -/
theorem normSq_topPrefixFiniteConjugateIncrement_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    Complex.normSq
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
          (NontrivialZetaZero.conjugatePartner rho) N) =
      Complex.normSq
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
          rho N) := by
  have hparity : Complex.normSq
      ((-1 : ℂ) ^ analyticZetaZeroMultiplicity rho) = 1 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow, norm_neg, norm_one, one_pow]
    norm_num
  have hrelation :
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
          (NontrivialZetaZero.conjugatePartner rho) N =
        (-1 : ℂ) ^ analyticZetaZeroMultiplicity rho *
          starRingEnd ℂ
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
              rho N) := by
    unfold
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
    simp only [analyticZetaZeroMultiplicity_conjugatePartner, map_sub]
    ring
  rw [hrelation, Complex.normSq_mul, Complex.normSq_conj, hparity, one_mul]

/-- The signed increment energy is odd under partner reflection. -/
theorem topPrefixFiniteIncrementEnergyDifference_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
        (NontrivialZetaZero.conjugatePartner rho) N =
      -pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
  rw [normSq_topPrefixFinitePartnerIncrement_conjugatePartner,
    normSq_topPrefixFiniteConjugateIncrement_conjugatePartner]
  ring

/-- The successor energy flux is odd under functional-equation partner
reflection. -/
theorem topPrefixFiniteEnergyFlux_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
        (NontrivialZetaZero.conjugatePartner rho) N =
      -pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
        rho N := by
  have hpartner :=
    topPrefixFiniteEnergyWork_eq_incrementEnergyDifference_add_flux
      (NontrivialZetaZero.conjugatePartner rho) N
  have hrho :=
    topPrefixFiniteEnergyWork_eq_incrementEnergyDifference_add_flux rho N
  rw [topPrefixFiniteEnergyWork_conjugatePartner,
    topPrefixFiniteIncrementEnergyDifference_conjugatePartner] at hpartner
  linarith

/-- The absolute successor flux is invariant under partner reflection. -/
theorem abs_topPrefixFiniteEnergyFlux_conjugatePartner
    (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
        (NontrivialZetaZero.conjugatePartner rho) N| =
      |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
        rho N| := by
  rw [topPrefixFiniteEnergyFlux_conjugatePartner, abs_neg]

/-- The critical first moment of the absolute integrals of the literal finite
eta flux kernels is summable exactly on the critical line.  The arithmetic
direction is still open. -/
theorem
    summable_oddEndpoint_mul_abs_integral_pairedEtaTopPrefixFiniteEnergyFluxKernel_iff_re_eq_half
    (rho : NontrivialZetaZero) :
    Summable (fun N : ℕ ↦
      ((2 * N + 1 : ℕ) : ℝ) *
        |∫ t : ℝ, pairedEtaTopPrefixFiniteEnergyFluxKernel rho N t
          ∂pairedEtaFiniteLogMeasure (N + 2)|) ↔
      rho.1.re = 1 / 2 := by
  simpa only [integral_pairedEtaTopPrefixFiniteEnergyFluxKernel_eq_flux] using
    summable_oddEndpoint_mul_abs_topPrefixFiniteEnergyFlux_iff_re_eq_half rho

end

end RiemannGaussian
