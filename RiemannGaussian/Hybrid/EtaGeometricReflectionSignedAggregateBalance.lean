import RiemannGaussian.Hybrid.EtaGeometricReflectionSignedAggregateDominantColour

/-!
# Exact polar--hyperbolic balancing of the signed eta aggregate

The natural original-colour normalization of an off-critical completion pair
has a proved dominant-colour limit.  This module instead factors each moving
coefficient exactly as a common positive geometric mean, a positive radial
balance, and a unit complex phase.  The two radial balances are reciprocal,
so neither reflected/original colour is discarded.

Lean transports this factorization through every four-colour metric
contraction and through the complete ordered-distinct upper-window reserve.
The literal signed reserve is exactly a sum of positive pair scales times the
balanced reserves, and the existing `13/18` and finite-window `18/18`
certificate interfaces are unchanged under this reparameterization.

This is an information-preserving identity, not a new estimate.  Neither
certificate threshold is proved here, and no zero-proportion improvement is
claimed.  The remaining arithmetic problem is to bound the exact balanced
carrier while retaining its reciprocal radii, unit phases, and signed colour
interactions.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Positive common amplitude used to balance the two moving completion
coefficients of one upper reflection pair. -/
def pairedEtaGeometricUpperCoefficientGeometricMean
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) : ℝ :=
  Real.sqrt
    (‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n 0‖ *
      ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1‖)

/-- The common geometric-mean amplitude is strictly positive for a positive
geometric base. -/
theorem pairedEtaGeometricUpperCoefficientGeometricMean_pos
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    0 < pairedEtaGeometricUpperCoefficientGeometricMean q rho n := by
  unfold pairedEtaGeometricUpperCoefficientGeometricMean
  exact Real.sqrt_pos.2 (mul_pos
    (norm_pos_iff.mpr (by
      unfold pairedEtaGeometricUpperCompletionCoefficientVector
      exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq _ n))
    (norm_pos_iff.mpr (by
      unfold pairedEtaGeometricUpperCompletionCoefficientVector
      exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq _ n)))

/-- Positive radial factor left after dividing one completion-coefficient norm
by the pair's common geometric mean. -/
def pairedEtaGeometricUpperCoefficientRadialBalance
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) (i : Fin 2) : ℝ :=
  ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n i‖ /
    pairedEtaGeometricUpperCoefficientGeometricMean q rho n

/-- Every balanced radial colour is strictly positive. -/
theorem pairedEtaGeometricUpperCoefficientRadialBalance_pos
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) (i : Fin 2) :
    0 < pairedEtaGeometricUpperCoefficientRadialBalance q rho n i := by
  exact div_pos
    (norm_pos_iff.mpr (by
      unfold pairedEtaGeometricUpperCompletionCoefficientVector
      exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq _ n))
    (pairedEtaGeometricUpperCoefficientGeometricMean_pos hq rho n)

/-- The reflected and original radial colours are exact reciprocals. -/
theorem pairedEtaGeometricUpperCoefficientRadialBalance_mul
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    pairedEtaGeometricUpperCoefficientRadialBalance q rho n 0 *
      pairedEtaGeometricUpperCoefficientRadialBalance q rho n 1 = 1 := by
  let a := ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n 0‖
  let b := ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1‖
  let g := pairedEtaGeometricUpperCoefficientGeometricMean q rho n
  have ha : 0 < a := norm_pos_iff.mpr (by
    unfold pairedEtaGeometricUpperCompletionCoefficientVector
    exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq _ n)
  have hb : 0 < b := norm_pos_iff.mpr (by
    unfold pairedEtaGeometricUpperCompletionCoefficientVector
    exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq _ n)
  have hg : 0 < g :=
    pairedEtaGeometricUpperCoefficientGeometricMean_pos hq rho n
  have hgSq : g ^ 2 = a * b := by
    unfold g pairedEtaGeometricUpperCoefficientGeometricMean a b
    exact Real.sq_sqrt (mul_nonneg ha.le hb.le)
  unfold pairedEtaGeometricUpperCoefficientRadialBalance
  change a / g * (b / g) = 1
  field_simp
  nlinarith

/-- Unit complex phase of one nonzero moving completion coefficient. -/
def pairedEtaGeometricUpperCoefficientUnitPhase
    (q : ℕ) {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) (i : Fin 2) : ℂ :=
  pairedEtaGeometricUpperCompletionCoefficientVector q rho n i /
    (‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n i‖ : ℂ)

/-- Every coefficient phase in the balanced ledger has norm one. -/
theorem norm_pairedEtaGeometricUpperCoefficientUnitPhase
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) (i : Fin 2) :
    ‖pairedEtaGeometricUpperCoefficientUnitPhase q rho n i‖ = 1 := by
  let c := pairedEtaGeometricUpperCompletionCoefficientVector q rho n i
  have hc : c ≠ 0 := by
    unfold c pairedEtaGeometricUpperCompletionCoefficientVector
    exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq _ n
  have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  unfold pairedEtaGeometricUpperCoefficientUnitPhase
  change ‖c / (‖c‖ : ℂ)‖ = 1
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcnorm]
  exact div_self hcnorm.ne'

/-- Exact polar--hyperbolic reconstruction of either moving completion
coefficient from common amplitude, reciprocal radius, and unit phase. -/
theorem pairedEtaGeometricUpperCompletionCoefficientVector_eq_balanced
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) (i : Fin 2) :
    pairedEtaGeometricUpperCompletionCoefficientVector q rho n i =
      ((pairedEtaGeometricUpperCoefficientGeometricMean q rho n *
        pairedEtaGeometricUpperCoefficientRadialBalance q rho n i : ℝ) : ℂ) *
      pairedEtaGeometricUpperCoefficientUnitPhase q rho n i := by
  let c := pairedEtaGeometricUpperCompletionCoefficientVector q rho n i
  let g := pairedEtaGeometricUpperCoefficientGeometricMean q rho n
  have hc : c ≠ 0 := by
    unfold c pairedEtaGeometricUpperCompletionCoefficientVector
    exact pairedEtaGeometricCompletedPrefixCoefficient_ne_zero hq _ n
  have hg : 0 < g :=
    pairedEtaGeometricUpperCoefficientGeometricMean_pos hq rho n
  have hscale :
      g * pairedEtaGeometricUpperCoefficientRadialBalance q rho n i = ‖c‖ := by
    unfold pairedEtaGeometricUpperCoefficientRadialBalance
    dsimp only [g, c]
    field_simp [
      (pairedEtaGeometricUpperCoefficientGeometricMean_pos hq rho n).ne']
  unfold pairedEtaGeometricUpperCoefficientUnitPhase
  change c = ((g * _ : ℝ) : ℂ) * (c / (‖c‖ : ℂ))
  rw [hscale]
  field_simp

/-- Four-colour metric contraction after retaining unit phase and reciprocal
radial colour but extracting both common pair amplitudes. -/
def pairedEtaGeometricCriticalUpperBalancedMetricContraction
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    star (pairedEtaGeometricUpperCoefficientUnitPhase q zeta n i) *
      pairedEtaGeometricUpperCoefficientUnitPhase q rho n j *
      ((pairedEtaGeometricUpperCoefficientRadialBalance q zeta n i *
        pairedEtaGeometricUpperCoefficientRadialBalance q rho n j : ℝ) : ℂ) *
      pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
        q zeta rho n M i j

/-- The raw complex metric contraction is exactly the product of its two
common amplitudes and the balanced four-colour contraction. -/
theorem pairedEtaGeometricCriticalUpperMetricCoefficientContraction_eq_mean_mul_balanced
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricCriticalUpperMetricCoefficientContraction
        q zeta rho n M =
      ((pairedEtaGeometricUpperCoefficientGeometricMean q zeta n *
        pairedEtaGeometricUpperCoefficientGeometricMean q rho n : ℝ) : ℂ) *
      pairedEtaGeometricCriticalUpperBalancedMetricContraction
        q zeta rho n M := by
  unfold pairedEtaGeometricCriticalUpperMetricCoefficientContraction
    pairedEtaGeometricCriticalUpperBalancedMetricContraction
  simp only [Fin.sum_univ_two]
  rw [pairedEtaGeometricUpperCompletionCoefficientVector_eq_balanced
      hq zeta n 0,
    pairedEtaGeometricUpperCompletionCoefficientVector_eq_balanced
      hq zeta n 1,
    pairedEtaGeometricUpperCompletionCoefficientVector_eq_balanced
      hq rho n 0,
    pairedEtaGeometricUpperCompletionCoefficientVector_eq_balanced
      hq rho n 1]
  simp only [map_mul, RCLike.star_def, Complex.conj_ofReal]
  push_cast
  ring

/-- Real-part form of the exact common-amplitude contraction factorization. -/
theorem pairedEtaGeometricCriticalUpperMetricCoefficientContraction_re_eq_mean_mul_balanced_re
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    (pairedEtaGeometricCriticalUpperMetricCoefficientContraction
        q zeta rho n M).re =
      (pairedEtaGeometricUpperCoefficientGeometricMean q zeta n *
        pairedEtaGeometricUpperCoefficientGeometricMean q rho n) *
      (pairedEtaGeometricCriticalUpperBalancedMetricContraction
        q zeta rho n M).re := by
  rw [pairedEtaGeometricCriticalUpperMetricCoefficientContraction_eq_mean_mul_balanced
    hq]
  simp

/-- Pair decorrelation reserve formed from the balanced four-colour
contractions while retaining the literal multiplicity weights. -/
def pairedEtaGeometricUpperPairBalancedMetricReserve
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℝ :=
  pairedEtaReflectionEvenFrameWeight T (Sum.inr rho) *
    pairedEtaReflectionEvenFrameWeight T (Sum.inr zeta) *
      ((pairedEtaGeometricCriticalUpperBalancedMetricContraction
          q rho rho n M).re *
        (pairedEtaGeometricCriticalUpperBalancedMetricContraction
          q zeta zeta n M).re -
        (pairedEtaGeometricCriticalUpperBalancedMetricContraction
          q zeta rho n M).re ^ 2)

/-- Positive common scale extracted from one ordered upper-zero pair. -/
def pairedEtaGeometricUpperPairBalanceScale
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) : ℝ :=
  (pairedEtaGeometricUpperCoefficientGeometricMean q zeta n *
    pairedEtaGeometricUpperCoefficientGeometricMean q rho n) ^ 2

/-- The common ordered-pair balance scale is strictly positive. -/
theorem pairedEtaGeometricUpperPairBalanceScale_pos
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n : ℕ) :
    0 < pairedEtaGeometricUpperPairBalanceScale q zeta rho n := by
  unfold pairedEtaGeometricUpperPairBalanceScale
  exact pow_pos (mul_pos
    (pairedEtaGeometricUpperCoefficientGeometricMean_pos hq zeta n)
    (pairedEtaGeometricUpperCoefficientGeometricMean_pos hq rho n)) 2

/-- The literal signed pair reserve is exactly its positive common scale times
the balanced pair reserve. -/
theorem pairedEtaGeometricUpperPairSignedMetricReserve_eq_scale_mul_balanced
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricUpperPairSignedMetricReserve q zeta rho n M =
      pairedEtaGeometricUpperPairBalanceScale q zeta rho n *
        pairedEtaGeometricUpperPairBalancedMetricReserve
          q zeta rho n M := by
  unfold pairedEtaGeometricUpperPairSignedMetricReserve
    pairedEtaGeometricUpperPairBalanceScale
    pairedEtaGeometricUpperPairBalancedMetricReserve
  rw [pairedEtaGeometricCriticalUpperMetricOrderedColourInteraction_eq_re_sq]
  rw [pairedEtaGeometricCriticalUpperMetricCoefficientContraction_re_eq_mean_mul_balanced_re
      hq,
    pairedEtaGeometricCriticalUpperMetricCoefficientContraction_re_eq_mean_mul_balanced_re
      hq,
    pairedEtaGeometricCriticalUpperMetricCoefficientContraction_re_eq_mean_mul_balanced_re
      hq]
  ring

/-- The balanced pair reserve is nonnegative because its positive rescaling is
the literal Gram decorrelation reserve. -/
theorem pairedEtaGeometricUpperPairBalancedMetricReserve_nonneg
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    0 ≤ pairedEtaGeometricUpperPairBalancedMetricReserve
      q zeta rho n M := by
  have hraw := pairedEtaGeometricUpperPairSignedMetricReserve_nonneg
    hqOdd hq zeta rho hn M
  rw [pairedEtaGeometricUpperPairSignedMetricReserve_eq_scale_mul_balanced
    hq.le] at hraw
  have hscale :=
    pairedEtaGeometricUpperPairBalanceScale_pos hq.le zeta rho n
  nlinarith

/-- Complete ordered-distinct upper-window sum of the positive-scaled balanced
pair reserves. -/
def pairedEtaGeometricUpperWindowScaledBalancedMetricReserve
    (q : ℕ) (T : ℝ) (n M : ℕ) : ℝ :=
  ∑ rho : ↑(spectralUpperZetaZeroWindow T),
    ∑ zeta ∈ (Finset.univ :
        Finset ↑(spectralUpperZetaZeroWindow T)).erase rho,
      pairedEtaGeometricUpperPairBalanceScale q zeta rho n *
        pairedEtaGeometricUpperPairBalancedMetricReserve q zeta rho n M

/-- The scale-weighted balanced window is exactly the existing literal signed
upper-window reserve, with no inequality or asymptotic replacement. -/
theorem pairedEtaGeometricUpperWindowSignedMetricReserve_eq_scaled_balanced
    {q : ℕ} (hq : 0 < q) (T : ℝ) (n M : ℕ) :
    pairedEtaGeometricUpperWindowSignedMetricReserve q T n M =
      pairedEtaGeometricUpperWindowScaledBalancedMetricReserve
        q T n M := by
  unfold pairedEtaGeometricUpperWindowSignedMetricReserve
    pairedEtaGeometricUpperWindowScaledBalancedMetricReserve
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro zeta _hzeta
  exact pairedEtaGeometricUpperPairSignedMetricReserve_eq_scale_mul_balanced
    hq zeta rho n M

/-- The complete scale-weighted balanced upper-window carrier is
nonnegative. -/
theorem pairedEtaGeometricUpperWindowScaledBalancedMetricReserve_nonneg
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    0 ≤ pairedEtaGeometricUpperWindowScaledBalancedMetricReserve
      q T n M := by
  rw [← pairedEtaGeometricUpperWindowSignedMetricReserve_eq_scaled_balanced
    hq.le]
  exact pairedEtaGeometricUpperWindowSignedMetricReserve_nonneg
    hqOdd hq T hn M

/-- The complete balanced upper-window carrier lies below the full literal
reflection-even certificate reserve. -/
theorem pairedEtaGeometricUpperWindowScaledBalancedMetricReserve_le_full
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    pairedEtaGeometricUpperWindowScaledBalancedMetricReserve q T n M ≤
      pairedEtaReflectionEvenFrameDecorrelationReserve
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k) T := by
  rw [← pairedEtaGeometricUpperWindowSignedMetricReserve_eq_scaled_balanced
    hq.le]
  exact pairedEtaGeometricUpperWindowSignedMetricReserve_le_full
    hqOdd hq T hn M

/-- The `13/18` and finite-window `18/18` certificate implications expressed
directly through the exact scale-weighted balanced carrier. -/
def PairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveTargets
    (q : ℕ) (T : ℝ) (n M : ℕ) : Prop :=
  ((((31 : ℝ) * (spectralZetaZeroWindow T).card - 36) *
        pairedEtaReflectionEvenFramePotential
          (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T <
      36 * pairedEtaGeometricUpperWindowScaledBalancedMetricReserve q T n M) →
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card) ∧
  (((((spectralZetaZeroWindow T).card : ℝ) - 1) *
        pairedEtaReflectionEvenFramePotential
          (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T ≤
      pairedEtaGeometricUpperWindowScaledBalancedMetricReserve q T n M) →
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card)

/-- The balanced and signed certificate target pairs are logically identical
because their reserve carriers are exactly equal. -/
theorem pairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveTargets_iff_signed
    {q : ℕ} (hq : 0 < q) (T : ℝ) (n M : ℕ) :
    PairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveTargets
        q T n M ↔
      PairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveTargets
        q T n M := by
  unfold
    PairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveTargets
    PairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveTargets
  rw [pairedEtaGeometricUpperWindowSignedMetricReserve_eq_scaled_balanced
    hq T n M]

/-- A separated long eta frame turns either balanced-carrier threshold into
the corresponding `13/18` or finite-window `18/18` conclusion. -/
theorem pairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveCertificateInterface
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (hT : 0 ≤ T) (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (n M : ℕ) (hn : 1 ≤ n)
    (hLI : LinearIndependent ℂ
      (pairedEtaReflectionEvenFrameVector
        (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T)) :
    PairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveTargets
      q T n M := by
  rw [pairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveTargets_iff_signed
    hq.le]
  exact
    pairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveCertificateInterface
      hqOdd hq hT hwindow n M hn hLI

/-- Every eligible finite zero window admits one odd prime whose sufficiently
late separated blocks expose the two exact balanced certificate interfaces. -/
theorem exists_prime_eventually_pairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveCertificateInterface
    {T : ℝ} (hT : 0 ≤ T)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    {M : ℕ} (hKM : (spectralZetaZeroWindow T).card ≤ M) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        PairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveTargets
          q T n M := by
  obtain ⟨q, hqPrime, hqOdd, hq, hcert⟩ :=
    exists_prime_eventually_pairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveCertificateInterface
      hT hwindow hKM
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hcert] with n hn
  rw [pairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveTargets_iff_signed
    hq.le]
  exact hn

end

end RiemannGaussian
