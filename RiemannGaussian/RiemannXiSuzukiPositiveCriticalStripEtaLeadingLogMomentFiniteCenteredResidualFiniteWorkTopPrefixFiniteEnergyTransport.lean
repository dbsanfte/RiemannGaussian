import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixFiniteEnergyGram

/-!
# One-step transport of the finite eta energy frontier

The signed finite energy `E_N` is now a literal finite eta Gram integral.  This
module gives that static representation an exact cutoff transport law.  The
partner and conjugate finite terms are split into their consecutive
increments.  Polarization then writes `E_N - E_(N+1)` as the signed energy of
those increments plus one explicit cross flux against the successor terms.

Both component amplitudes tend to zero unconditionally.  Consequently the
one-step energy work telescopes not only at every finite length but converges,
as an ordered tail, back to `E_N`.  Dividing by the fixed total amplitude gives
the analogous reconstruction of the normalized defect and hence of the
amplitude mismatch.

This is a finite discrete conservation law, not a sign or summability estimate
for its flux.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Consecutive cutoff increment of the reflected-partner completed finite
term. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
      rho N -
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
      rho (N + 1)

/-- Consecutive cutoff increment of the conjugate-original completed finite
term. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
    (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
      rho N -
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
      rho (N + 1)

/-- Signed energy carried by the two one-step finite-term increments. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  Complex.normSq
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
        rho N) -
    Complex.normSq
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
        rho N)

/-- Cross flux between each one-step increment and its successor finite term. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  2 *
    ((pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
          rho N *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
            rho (N + 1))).re -
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
          rho N *
        starRingEnd ℂ
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
            rho (N + 1))).re)

/-- The literal consecutive work of the signed finite energy. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
      rho N -
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
      rho (N + 1)

/-- The one-step energy work is exactly signed increment energy plus the
successor cross flux. -/
theorem topPrefixFiniteEnergyWork_eq_incrementEnergyDifference_add_flux
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
        rho N =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
          rho N +
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
          rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
  rw [show
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
          rho N =
        Complex.normSq
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
              rho N) -
          Complex.normSq
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
              rho N) by
        exact topPrefixFiniteEnergyDifference_eq_finiteTermNormSq_sub rho N,
    show
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
          rho (N + 1) =
        Complex.normSq
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
              rho (N + 1)) -
          Complex.normSq
            (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
              rho (N + 1)) by
        exact topPrefixFiniteEnergyDifference_eq_finiteTermNormSq_sub rho (N + 1)]
  have hpartner :
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
          rho N =
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
            rho N +
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
            rho (N + 1) := by
    unfold
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
    ring
  have hconjugate :
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
          rho N =
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
            rho N +
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
            rho (N + 1) := by
    unfold
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
    ring
  rw [hpartner, hconjugate, Complex.normSq_add, Complex.normSq_add]
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
  ring

/-- The signed increment energy is bounded by the sum of the two nonnegative
increment energies. -/
theorem abs_topPrefixFiniteIncrementEnergyDifference_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
        rho N| ≤
      Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
            rho N) +
        Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
            rho N) := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
  let p : ℝ := Complex.normSq
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
      rho N)
  let q : ℝ := Complex.normSq
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
      rho N)
  have hp : 0 ≤ p := Complex.normSq_nonneg _
  have hq : 0 ≤ q := Complex.normSq_nonneg _
  rw [sub_eq_add_neg]
  calc
    |p + -q| ≤ |p| + |-q| := abs_add_le p (-q)
    _ = p + q := by rw [abs_neg, abs_of_nonneg hp, abs_of_nonneg hq]

/-- The absolute cross flux is controlled by the two increment--successor
norm products. -/
theorem abs_topPrefixFiniteEnergyFlux_le
    (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
        rho N| ≤
      2 *
        (‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
              rho N‖ *
            ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
              rho (N + 1)‖ +
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
              rho N‖ *
            ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
              rho (N + 1)‖) := by
  let p : ℝ :=
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
          rho N *
      starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
          rho (N + 1))).re
  let q : ℝ :=
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
          rho N *
      starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
          rho (N + 1))).re
  have hp : |p| ≤
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
          rho N‖ *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
          rho (N + 1)‖ := by
    calc
      |p| ≤
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
              rho N *
            starRingEnd ℂ
              (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
                rho (N + 1))‖ := Complex.abs_re_le_norm _
      _ = _ := by rw [norm_mul, norm_conj]
  have hq : |q| ≤
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
          rho N‖ *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
          rho (N + 1)‖ := by
    calc
      |q| ≤
          ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
              rho N *
            starRingEnd ℂ
              (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
                rho (N + 1))‖ := Complex.abs_re_le_norm _
      _ = _ := by rw [norm_mul, norm_conj]
  have hpq : |p - q| ≤ |p| + |q| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le p (-q)
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
  change |2 * (p - q)| ≤ _
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left (hpq.trans (add_le_add hp hq)) (by norm_num)

/-- Complete absolute one-step energy estimate: only the two increment
energies and the two successor cross-flux products remain. -/
theorem abs_topPrefixFiniteEnergyWork_le_increment_energy_add_flux
    (rho : NontrivialZetaZero) (N : ℕ) :
    |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
        rho N| ≤
      Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
            rho N) +
        Complex.normSq
          (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
            rho N) +
        2 *
          (‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerIncrement
                rho N‖ *
              ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerTerm
                rho (N + 1)‖ +
            ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateIncrement
                rho N‖ *
              ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateTerm
                rho (N + 1)‖) := by
  rw [topPrefixFiniteEnergyWork_eq_incrementEnergyDifference_add_flux]
  calc
    |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
          rho N +
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
          rho N| ≤
      |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteIncrementEnergyDifference
          rho N| +
        |pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyFlux
          rho N| := abs_add_le _ _
    _ ≤ _ := add_le_add
      (abs_topPrefixFiniteIncrementEnergyDifference_le rho N)
      (abs_topPrefixFiniteEnergyFlux_le rho N)

/-- In Gram form, one-step work is the difference of the two consecutive
signed finite eta product integrals. -/
theorem topPrefixFiniteEnergyWork_eq_integral_gram_sub_succ
    (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
        rho N =
      (∫ p : ℝ × ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyGramKernel
            rho N p
          ∂((pairedEtaFiniteLogMeasure (N + 1)).prod
            (pairedEtaFiniteLogMeasure (N + 1)))) -
        ∫ p : ℝ × ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyGramKernel
            rho (N + 1) p
          ∂((pairedEtaFiniteLogMeasure (N + 2)).prod
            (pairedEtaFiniteLogMeasure (N + 2))) := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
  rw [integral_topPrefixFiniteEnergyGramKernel_eq_finiteEnergyDifference,
    integral_topPrefixFiniteEnergyGramKernel_eq_finiteEnergyDifference]

/-- The finite partner amplitude tends to zero at every nontrivial zero. -/
theorem tendsto_topPrefixFinitePartnerAmplitude_zero
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFinitePartnerAmplitude
        rho N) atTop (nhds 0) := by
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have htail :=
    (tendsto_pairedEtaLogLaplaceMomentCenteredTailUpper_zero
      (analyticZetaZeroMultiplicity rho - 1)
      (NontrivialZetaZero.zero_lt_re
        (NontrivialZetaZero.conjugatePartner rho))).comp hshift
  have hupper := Filter.Tendsto.const_mul
    (pairedEtaCompletionSpectralWeight
      (NontrivialZetaZero.conjugatePartner rho)) htail
  have hnorm : Tendsto (fun N : ℕ =>
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPartnerComponent
        rho N‖) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · exact Eventually.of_forall fun N =>
        norm_topPrefixPartnerComponent_le_completionWeight_mul_centeredTailUpper
          rho N
    · simpa only [Function.comp_apply, mul_zero] using hupper
  simpa only [norm_topPrefixPartnerComponent_eq_finitePartnerAmplitude] using hnorm

/-- The finite conjugate-original amplitude tends to zero at every
nontrivial zero. -/
theorem tendsto_topPrefixFiniteConjugateAmplitude_zero
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteConjugateAmplitude
        rho N) atTop (nhds 0) := by
  have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have htail :=
    (tendsto_pairedEtaLogLaplaceMomentCenteredTailUpper_zero
      (analyticZetaZeroMultiplicity rho - 1)
      (NontrivialZetaZero.zero_lt_re rho)).comp hshift
  have hupper := Filter.Tendsto.const_mul
    (pairedEtaCompletionSpectralWeight rho) htail
  have hnorm : Tendsto (fun N : ℕ =>
      ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixConjugateComponent
        rho N‖) atTop (nhds 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · exact Eventually.of_forall fun N =>
        norm_topPrefixConjugateComponent_le_completionWeight_mul_centeredTailUpper
          rho N
    · simpa only [Function.comp_apply, mul_zero] using hupper
  simpa only [norm_topPrefixConjugateComponent_eq_finiteConjugateAmplitude] using hnorm

/-- The signed finite energy itself tends to zero unconditionally. -/
theorem tendsto_topPrefixFiniteEnergyDifference_zero
    (rho : NontrivialZetaZero) :
    Tendsto (fun N : ℕ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho N) atTop (nhds 0) := by
  have hpartner := (tendsto_topPrefixFinitePartnerAmplitude_zero rho).pow 2
  have hconjugate := (tendsto_topPrefixFiniteConjugateAmplitude_zero rho).pow 2
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
  simpa only [zero_pow (by norm_num : 2 ≠ 0), sub_zero] using
    hpartner.sub hconjugate

/-- Consecutive signed energy work telescopes exactly from cutoff `N` through
cutoff `N+L`. -/
theorem sum_range_topPrefixFiniteEnergyWork_eq_sub
    (rho : NontrivialZetaZero) (N L : ℕ) :
    ∑ q ∈ Finset.range L,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
          rho (N + q) =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
          rho N -
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
          rho (N + L) := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
  simpa only [Nat.add_zero, Nat.add_assoc] using
    (Finset.sum_range_sub'
      (fun q : ℕ =>
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
          rho (N + q)) L)

/-- At every base cutoff, ordered finite sums of consecutive energy work
converge to the full signed finite energy. -/
theorem tendsto_sum_range_topPrefixFiniteEnergyWork
    (rho : NontrivialZetaZero) (N : ℕ) :
    Tendsto (fun L : ℕ =>
      ∑ q ∈ Finset.range L,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
          rho (N + q))
      atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
          rho N)) := by
  have hshift : Tendsto (fun L : ℕ => N + L) atTop atTop := by
    simpa only [Nat.add_comm] using Filter.tendsto_add_atTop_nat N
  have hterminal :=
    (tendsto_topPrefixFiniteEnergyDifference_zero rho).comp hshift
  have hconstant : Tendsto (fun _ : ℕ =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
        rho N) atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyDifference
          rho N)) := tendsto_const_nhds
  have hdifference := hconstant.sub hterminal
  have hsum := hdifference.congr' (Eventually.of_forall fun L =>
    (sum_range_topPrefixFiniteEnergyWork_eq_sub rho N L).symm)
  simpa only [Function.comp_apply, sub_zero] using hsum

/-- Dividing the ordered energy-work reconstruction by the fixed total
amplitude recovers the normalized finite energy defect. -/
theorem tendsto_sum_range_topPrefixFiniteEnergyWork_div_total
    (rho : NontrivialZetaZero) (N : ℕ) :
    Tendsto (fun L : ℕ =>
      (∑ q ∈ Finset.range L,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
          rho (N + q)) /
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteTotalAmplitude
          rho N)
      atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect
          rho N)) := by
  have h := (tendsto_sum_range_topPrefixFiniteEnergyWork rho N).div_const
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteTotalAmplitude
      rho N)
  simpa only [
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixNormalizedFiniteEnergyDefect]
    using h

/-- Squaring the normalized ordered work reconstruction converges exactly to
the original nonnegative amplitude mismatch. -/
theorem tendsto_sq_sum_range_topPrefixFiniteEnergyWork_div_total
    (rho : NontrivialZetaZero) (N : ℕ) :
    Tendsto (fun L : ℕ =>
      ((∑ q ∈ Finset.range L,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteEnergyWork
          rho (N + q)) /
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixFiniteTotalAmplitude
          rho N) ^ 2)
      atTop
      (nhds
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAmplitudeImbalance
          rho N)) := by
  have h := (tendsto_sum_range_topPrefixFiniteEnergyWork_div_total rho N).pow 2
  simpa only [
    ← topPrefixAmplitudeImbalance_eq_sq_normalizedFiniteEnergyDefect rho N]
    using h

end

end RiemannGaussian
