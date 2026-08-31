import RiemannGaussian.Hybrid.EtaGeometricReflectionSumCoefficientEnvelope

/-!
# Explicit lower bounds for upper eta pair reserves

This module joins the two quantitative sides of the literal upper--upper eta
certificate reserve.  The preceding coercivity theorem gives an explicit
positive lower bound for each packed upper atom norm, while the correlation
theorem gives an explicit four-colour coefficient-and-gap upper envelope for
their real correlation.

Lean proves that every actual multiplicity-weighted upper--upper reserve is
eventually bounded below by the product of the two coercive atom bounds minus
the square of that correlation envelope.  The conclusion is simultaneous over
the complete finite upper zero window.  This lower bound is unconditional but
is not asserted to be positive: proving enough positivity after aggregation is
the remaining eta-arithmetic certificate problem.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- The explicit coercive lower bound transported into the literal packed
upper-frame metric. -/
def pairedEtaGeometricUpperFrameAtomCoerciveLower
    (q : ℕ) {T : ℝ} (rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℝ :=
  (finiteReciprocalRadialPhaseCoercivity M
          ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖
          (etaGeometricNormalizedMode q rho.1.val) / 2 *
        (‖pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n‖ ^ 2 +
          ‖pairedEtaGeometricCompletedPrefixCoefficient q
            (NontrivialZetaZero.conjugatePartner rho.1) n‖ ^ 2)) /
      etaGeometricCriticalCoordinateTiltEnergy q M

/-- The transported atom lower bound is strictly positive whenever the
geometric block has at least two coordinates. -/
theorem pairedEtaGeometricUpperFrameAtomCoerciveLower_pos
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T)) (n : ℕ)
    {M : ℕ} (hM : 1 < M) :
    0 < pairedEtaGeometricUpperFrameAtomCoerciveLower q rho n M := by
  have hcoercivity :
      0 < finiteReciprocalRadialPhaseCoercivity M
          ‖etaGeometricShiftedMode q (1 / 2) rho.1.val‖
          (etaGeometricNormalizedMode q rho.1.val) / 2 :=
    half_pos
      (spectralUpperZetaZeroWindow_criticalShiftedReflectionCoercivity_pos
        hq rho hM)
  have hcoefficient :
      0 < ‖pairedEtaGeometricCompletedPrefixCoefficient q rho.1 n‖ ^ 2 +
        ‖pairedEtaGeometricCompletedPrefixCoefficient q
          (NontrivialZetaZero.conjugatePartner rho.1) n‖ ^ 2 := by
    apply add_pos_of_pos_of_nonneg
    · exact sq_pos_of_pos (norm_pos_iff.mpr
        (pairedEtaGeometricCompletedPrefixCoefficient_ne_zero
          hq.le rho.1 n))
    · positivity
  have henergy : 0 < etaGeometricCriticalCoordinateTiltEnergy q M :=
    etaGeometricCriticalCoordinateTiltEnergy_pos q (by omega)
  exact div_pos (mul_pos hcoercivity hcoefficient) henergy

/-- Every sufficiently late literal upper atom dominates its named coercive
lower bound in the original certificate metric. -/
theorem eventually_pairedEtaGeometricUpperFrameAtomCoerciveLower_le_normSq
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (rho : ↥(spectralUpperZetaZeroWindow T))
    {M : ℕ} (hM : 1 < M) :
    ∀ᶠ n in atTop,
      pairedEtaGeometricUpperFrameAtomCoerciveLower q rho n M ≤
        pairedEtaReflectionEvenFrameAtomNormSq
          (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
          T (Sum.inr rho) := by
  simpa [pairedEtaGeometricUpperFrameAtomCoerciveLower] using
    eventually_spectralUpperZetaZeroWindow_geometricFrameAtomNormSq_coercive
      hqOdd hq rho hM

/-- Coercivity-minus-correlation lower envelope for one ordered upper pair,
before applying the positive analytic-multiplicity weights. -/
def pairedEtaGeometricUpperPairReserveGapLower
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) (ε : ℝ) : ℝ :=
  pairedEtaGeometricUpperFrameAtomCoerciveLower q rho n M *
      pairedEtaGeometricUpperFrameAtomCoerciveLower q zeta n M -
    pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
      q zeta rho n ε ^ 2

/-- The same explicit pair lower envelope with the exact multiplicity weights
appearing in the reflection-even certificate reserve. -/
def pairedEtaGeometricUpperPairWeightedReserveGapLower
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) (ε : ℝ) : ℝ :=
  pairedEtaReflectionEvenFrameWeight T (Sum.inr rho) *
    pairedEtaReflectionEvenFrameWeight T (Sum.inr zeta) *
      pairedEtaGeometricUpperPairReserveGapLower q zeta rho n M ε

/-- A strict coefficient-gap comparison makes the explicit weighted lower
envelope positive.  This theorem exposes the precise pointwise arithmetic
condition; it does not assert that condition. -/
theorem pairedEtaGeometricUpperPairWeightedReserveGapLower_pos_of_sq_lt
    (q : ℕ) {T : ℝ}
    (zeta rho : ↥(spectralUpperZetaZeroWindow T))
    (n M : ℕ) (ε : ℝ)
    (hgap :
      pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
            q zeta rho n ε ^ 2 <
        pairedEtaGeometricUpperFrameAtomCoerciveLower q rho n M *
          pairedEtaGeometricUpperFrameAtomCoerciveLower q zeta n M) :
    0 < pairedEtaGeometricUpperPairWeightedReserveGapLower
      q zeta rho n M ε := by
  unfold pairedEtaGeometricUpperPairWeightedReserveGapLower
    pairedEtaGeometricUpperPairReserveGapLower
  exact mul_pos
    (mul_pos
      (pairedEtaReflectionEvenFrameWeight_pos T (Sum.inr rho))
      (pairedEtaReflectionEvenFrameWeight_pos T (Sum.inr zeta)))
    (sub_pos.mpr hgap)

/-- Simultaneously over the complete finite upper zero window, every actual
multiplicity-weighted upper--upper certificate reserve eventually dominates
the explicit coercivity-product-minus-gap-envelope-square lower bound. -/
theorem eventually_spectralUpperZetaZeroWindow_geometricUpperPairWeightedReserveGapLower_le
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    {M : ℕ} (hM : 1 < M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∀ zeta rho : ↥(spectralUpperZetaZeroWindow T),
        pairedEtaGeometricUpperPairWeightedReserveGapLower
            q zeta rho n M ε ≤
          pairedEtaGeometricUpperPairWeightedDecorrelationReserve
            q zeta rho n M := by
  have hatom :
      ∀ᶠ n in atTop,
        ∀ rho : ↥(spectralUpperZetaZeroWindow T),
          pairedEtaGeometricUpperFrameAtomCoerciveLower q rho n M ≤
            pairedEtaReflectionEvenFrameAtomNormSq
              (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
              T (Sum.inr rho) := by
    apply Filter.eventually_all.mpr
    intro rho
    exact eventually_pairedEtaGeometricUpperFrameAtomCoerciveLower_le_normSq
      hqOdd hq rho hM
  have hcorrelation :=
    eventually_spectralUpperZetaZeroWindow_geometricFrameCorrelation_upper_upper_abs_le_gapEnvelope
      hqOdd hq T M hε
  filter_upwards [hatom, hcorrelation] with n hatomN hcorrelationN
  intro zeta rho
  have hrhoNonneg :
      0 ≤ pairedEtaReflectionEvenFrameAtomNormSq
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr rho) := by
    unfold pairedEtaReflectionEvenFrameAtomNormSq
    positivity
  have hnormProduct :
      pairedEtaGeometricUpperFrameAtomCoerciveLower q rho n M *
          pairedEtaGeometricUpperFrameAtomCoerciveLower q zeta n M ≤
        pairedEtaReflectionEvenFrameAtomNormSq
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T (Sum.inr rho) *
          pairedEtaReflectionEvenFrameAtomNormSq
            (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
            T (Sum.inr zeta) :=
    mul_le_mul (hatomN rho) (hatomN zeta)
      (pairedEtaGeometricUpperFrameAtomCoerciveLower_pos
        hq zeta n hM).le hrhoNonneg
  let correlation : ℝ :=
    (star (pairedEtaReflectionEvenFrameVector
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr zeta)) ⬝ᵥ
      pairedEtaReflectionEvenFrameVector
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k)
        T (Sum.inr rho)).re
  let envelope : ℝ :=
    pairedEtaGeometricUpperReflectionSumCorrelationGapEnvelope
      q zeta rho n ε
  have habs : |correlation| ≤ envelope := hcorrelationN zeta rho
  have henvelope : 0 ≤ envelope := (abs_nonneg correlation).trans habs
  have hcorrelationSq : correlation ^ 2 ≤ envelope ^ 2 := by
    calc
      correlation ^ 2 = |correlation| ^ 2 := (sq_abs correlation).symm
      _ ≤ envelope ^ 2 :=
        (sq_le_sq₀ (abs_nonneg correlation) henvelope).2 habs
  unfold pairedEtaGeometricUpperPairWeightedReserveGapLower
    pairedEtaGeometricUpperPairReserveGapLower
    pairedEtaGeometricUpperPairWeightedDecorrelationReserve
  apply mul_le_mul_of_nonneg_left
  · exact sub_le_sub hnormProduct hcorrelationSq
  · exact mul_nonneg
      (pairedEtaReflectionEvenFrameWeight_pos T (Sum.inr rho)).le
      (pairedEtaReflectionEvenFrameWeight_pos T (Sum.inr zeta)).le

/-- Sum of the actual weighted decorrelation reserves over all ordered
distinct pairs in the upper off-line window. -/
def pairedEtaGeometricUpperWindowWeightedDecorrelationReserve
    (q : ℕ) (T : ℝ) (n M : ℕ) : ℝ :=
  ∑ rho : ↥(spectralUpperZetaZeroWindow T),
    ∑ zeta ∈ (Finset.univ :
        Finset ↥(spectralUpperZetaZeroWindow T)).erase rho,
      pairedEtaGeometricUpperPairWeightedDecorrelationReserve
        q zeta rho n M

/-- Sum of the explicit coercivity-minus-envelope lower bounds over exactly
the same ordered distinct upper pairs. -/
def pairedEtaGeometricUpperWindowWeightedReserveGapLower
    (q : ℕ) (T : ℝ) (n M : ℕ) (ε : ℝ) : ℝ :=
  ∑ rho : ↥(spectralUpperZetaZeroWindow T),
    ∑ zeta ∈ (Finset.univ :
        Finset ↥(spectralUpperZetaZeroWindow T)).erase rho,
      pairedEtaGeometricUpperPairWeightedReserveGapLower
        q zeta rho n M ε

/-- The pointwise quantitative reserve bounds aggregate without loss over the
entire ordered distinct upper--upper sector of the finite certificate. -/
theorem eventually_pairedEtaGeometricUpperWindowWeightedReserveGapLower_le_decorrelationReserve
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    {M : ℕ} (hM : 1 < M) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      pairedEtaGeometricUpperWindowWeightedReserveGapLower
          q T n M ε ≤
        pairedEtaGeometricUpperWindowWeightedDecorrelationReserve
          q T n M := by
  have hpairs :=
    eventually_spectralUpperZetaZeroWindow_geometricUpperPairWeightedReserveGapLower_le
      hqOdd hq T hM hε
  filter_upwards [hpairs] with n hpairsN
  unfold pairedEtaGeometricUpperWindowWeightedReserveGapLower
    pairedEtaGeometricUpperWindowWeightedDecorrelationReserve
  apply Finset.sum_le_sum
  intro rho _hrho
  apply Finset.sum_le_sum
  intro zeta _hzeta
  exact hpairsN zeta rho

end

end RiemannGaussian
