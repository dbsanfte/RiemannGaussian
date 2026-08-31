import RiemannGaussian.Hybrid.EtaGeometricReflectionLongBlockFloorCeiling

/-!
# Signed four-colour eta reserve aggregate

The pointwise coercivity-minus-triangle floor has a proved long-block ceiling.
This module moves back upstream of that lossy step.  For each ordered upper
zero pair it exposes the real metric contraction as four signed
reflected/original colour contributions, then retains all sixteen ordered
cross-colour products appearing in its square.

Lean proves that this signed carrier is not a surrogate: after summing over
the finite upper window it is exactly the literal upper--upper decorrelation
reserve sector.  It is therefore nonnegative and lies below the complete
reflection-even reserve without an asymptotic envelope.  For every eligible
long block, one odd prime base eventually makes thresholds on this exact
aggregate imply respectively a critical-zero proportion above `13/18` and
the finite-window `18/18` conclusion.

Neither threshold is proved here, so no zero-proportion improvement is
claimed.  The advance is a rigorous certificate interface whose arithmetic
frontier retains the phase and sign cancellations that the failed pointwise
triangle method destroyed.
-/

open Complex Matrix Finset Filter
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- One real signed colour contribution to the exact metric coefficient
contraction of two upper reflection sums. -/
def pairedEtaGeometricCriticalUpperMetricColourContribution
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) (i j : Fin 2) : ℝ :=
  (star (pairedEtaGeometricUpperCompletionCoefficientVector q zeta n i) *
      pairedEtaGeometricUpperCompletionCoefficientVector q rho n j *
        pairedEtaGeometricCriticalUpperMetricPrefixCorrelationMatrix
          q zeta rho n M i j).re

/-- The real part of the exact metric contraction is the signed sum of all
four reflected/original colour contributions. -/
theorem pairedEtaGeometricCriticalUpperMetricCoefficientContraction_re_eq_sum_colour
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    (pairedEtaGeometricCriticalUpperMetricCoefficientContraction
        q zeta rho n M).re =
      ∑ i : Fin 2, ∑ j : Fin 2,
        pairedEtaGeometricCriticalUpperMetricColourContribution
          q zeta rho n M i j := by
  unfold pairedEtaGeometricCriticalUpperMetricCoefficientContraction
    pairedEtaGeometricCriticalUpperMetricColourContribution
  simp
  ring

/-- All sixteen ordered cross-colour products retained before any triangle
inequality is applied. -/
def pairedEtaGeometricCriticalUpperMetricOrderedColourInteraction
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ∑ l : Fin 2,
    pairedEtaGeometricCriticalUpperMetricColourContribution
        q zeta rho n M i j *
      pairedEtaGeometricCriticalUpperMetricColourContribution
        q zeta rho n M k l

/-- The ordered sixteen-term colour interaction is exactly the square of the
real full contraction, including every signed cross-colour cancellation. -/
theorem pairedEtaGeometricCriticalUpperMetricOrderedColourInteraction_eq_re_sq
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) :
    pairedEtaGeometricCriticalUpperMetricOrderedColourInteraction
        q zeta rho n M =
      (pairedEtaGeometricCriticalUpperMetricCoefficientContraction
        q zeta rho n M).re ^ 2 := by
  rw [pairedEtaGeometricCriticalUpperMetricCoefficientContraction_re_eq_sum_colour]
  unfold pairedEtaGeometricCriticalUpperMetricOrderedColourInteraction
  simp only [Fin.sum_univ_two]
  ring

/-- Exact multiplicity-weighted pair reserve with all four metric colours and
all sixteen signed ordered colour interactions left visible. -/
def pairedEtaGeometricUpperPairSignedMetricReserve
    (q : ℕ) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    (n M : ℕ) : ℝ :=
  pairedEtaReflectionEvenFrameWeight T (Sum.inr rho) *
    pairedEtaReflectionEvenFrameWeight T (Sum.inr zeta) *
      ((pairedEtaGeometricCriticalUpperMetricCoefficientContraction
          q rho rho n M).re *
        (pairedEtaGeometricCriticalUpperMetricCoefficientContraction
          q zeta zeta n M).re -
        pairedEtaGeometricCriticalUpperMetricOrderedColourInteraction
          q zeta rho n M)

/-- The signed four-colour pair carrier is exactly the actual upper-pair
decorrelation reserve. -/
theorem pairedEtaGeometricUpperPairSignedMetricReserve_eq_decorrelationReserve
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    pairedEtaGeometricUpperPairSignedMetricReserve q zeta rho n M =
      pairedEtaGeometricUpperPairWeightedDecorrelationReserve
        q zeta rho n M := by
  rw [pairedEtaGeometricUpperPairWeightedDecorrelationReserve_eq_metricContractionLedger
    hqOdd hq zeta rho hn M]
  unfold pairedEtaGeometricUpperPairSignedMetricReserve
  rw [pairedEtaGeometricCriticalUpperMetricOrderedColourInteraction_eq_re_sq]
  unfold pairedEtaGeometricCriticalUpperMetricCoefficientGramReserve
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The signed pair carrier is nonnegative by its exact identification with
the literal Gram reserve. -/
theorem pairedEtaGeometricUpperPairSignedMetricReserve_nonneg
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T))
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    0 ≤ pairedEtaGeometricUpperPairSignedMetricReserve
      q zeta rho n M := by
  rw [pairedEtaGeometricUpperPairSignedMetricReserve_eq_decorrelationReserve
    hqOdd hq zeta rho hn M]
  exact pairedEtaGeometricUpperPairWeightedDecorrelationReserve_nonneg
    q zeta rho n M

/-- Complete ordered-distinct upper-window reserve in the signed four-colour
metric carrier, before any pointwise absolute-value estimate. -/
def pairedEtaGeometricUpperWindowSignedMetricReserve
    (q : ℕ) (T : ℝ) (n M : ℕ) : ℝ :=
  ∑ rho : ↑(spectralUpperZetaZeroWindow T),
    ∑ zeta ∈ (Finset.univ :
        Finset ↑(spectralUpperZetaZeroWindow T)).erase rho,
      pairedEtaGeometricUpperPairSignedMetricReserve q zeta rho n M

/-- The signed metric window carrier is exactly the actual upper--upper
ordered-distinct reserve sector. -/
theorem pairedEtaGeometricUpperWindowSignedMetricReserve_eq_decorrelationReserve
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    pairedEtaGeometricUpperWindowSignedMetricReserve q T n M =
      pairedEtaGeometricUpperWindowWeightedDecorrelationReserve
        q T n M := by
  unfold pairedEtaGeometricUpperWindowSignedMetricReserve
    pairedEtaGeometricUpperWindowWeightedDecorrelationReserve
  apply Finset.sum_congr rfl
  intro rho _hrho
  apply Finset.sum_congr rfl
  intro zeta _hzeta
  exact pairedEtaGeometricUpperPairSignedMetricReserve_eq_decorrelationReserve
    hqOdd hq zeta rho hn M

/-- The exact signed upper-window carrier is nonnegative. -/
theorem pairedEtaGeometricUpperWindowSignedMetricReserve_nonneg
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    0 ≤ pairedEtaGeometricUpperWindowSignedMetricReserve q T n M := by
  rw [pairedEtaGeometricUpperWindowSignedMetricReserve_eq_decorrelationReserve
    hqOdd hq T hn M]
  unfold pairedEtaGeometricUpperWindowWeightedDecorrelationReserve
  exact Finset.sum_nonneg fun rho _hrho ↦
    Finset.sum_nonneg fun zeta _hzeta ↦
      pairedEtaGeometricUpperPairWeightedDecorrelationReserve_nonneg
        q zeta rho n M

/-- The exact signed upper-window carrier is a lower bound for the complete
reflection-even certificate reserve without any asymptotic envelope. -/
theorem pairedEtaGeometricUpperWindowSignedMetricReserve_le_full
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    pairedEtaGeometricUpperWindowSignedMetricReserve q T n M ≤
      pairedEtaReflectionEvenFrameDecorrelationReserve
        (fun k : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n k) T := by
  rw [pairedEtaGeometricUpperWindowSignedMetricReserve_eq_decorrelationReserve
    hqOdd hq T hn M]
  exact pairedEtaGeometricUpperWindowWeightedDecorrelationReserve_le_full
    q T n M

/-- The two certificate implications driven directly by the exact signed
four-colour upper-window reserve, with no triangle-envelope parameter. -/
def PairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveTargets
    (q : ℕ) (T : ℝ) (n M : ℕ) : Prop :=
  ((((31 : ℝ) * (spectralZetaZeroWindow T).card - 36) *
        pairedEtaReflectionEvenFramePotential
          (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T <
      36 * pairedEtaGeometricUpperWindowSignedMetricReserve q T n M) →
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card) ∧
  (((((spectralZetaZeroWindow T).card : ℝ) - 1) *
        pairedEtaReflectionEvenFramePotential
          (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T ≤
      pairedEtaGeometricUpperWindowSignedMetricReserve q T n M) →
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card)

/-- A separated long eta frame turns either exact signed-aggregate threshold
into the corresponding `13/18` or `18/18` zero-location conclusion. -/
theorem pairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveCertificateInterface
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (hT : 0 ≤ T) (hwindow : (spectralZetaZeroWindow T).Nonempty)
    (n M : ℕ) (hn : 1 ≤ n)
    (hLI : LinearIndependent ℂ
      (pairedEtaReflectionEvenFrameVector
        (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T)) :
    PairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveTargets
      q T n M := by
  have hfloor := pairedEtaGeometricUpperWindowSignedMetricReserve_le_full
    hqOdd hq T hn M
  unfold PairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveTargets
  let cutoff : Fin M → ℕ := fun j ↦
    pairedEtaGeometricHyperbolicCutoff q n j
  constructor
  · intro hthirteen
    apply pairedEtaReflectionEven_thirteen_eighteen_of_framePotential
      cutoff hT hwindow hLI
    apply (pairedEtaReflectionEvenFrame_thirteenEighteenMoment_iff_reserve
      cutoff T (spectralZetaZeroWindow T).card).2
    exact hthirteen.trans_le
      (mul_le_mul_of_nonneg_left hfloor (by norm_num))
  · intro hendpoint
    apply pairedEtaReflectionEven_allCritical_of_framePotentialCeiling
      cutoff hT hwindow hLI
    apply (pairedEtaReflectionEvenFrame_endpointMoment_iff_reserve
      cutoff T (spectralZetaZeroWindow T).card).2
    exact hendpoint.trans hfloor

/-- Once an odd base separates the square eta block, the exact signed
aggregate certificate interface holds eventually for every longer block. -/
theorem eventually_pairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveCertificateInterface
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) {T : ℝ}
    (hT : 0 ≤ T) (hwindow : (spectralZetaZeroWindow T).Nonempty)
    {M : ℕ} (hKM : (spectralZetaZeroWindow T).card ≤ M)
    (hK : ∀ᶠ n in atTop,
      (pairedEtaGeometricMultiplicityWeightedZeroGram q
        (spectralZetaZeroWindow T) n).PosDef) :
    ∀ᶠ n in atTop,
      PairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveTargets
        q T n M := by
  filter_upwards [hK, eventually_ge_atTop (1 : ℕ)] with n hKn hn
  have hLI :=
    linearIndependent_pairedEtaGeometricReflectionEvenFrameVector_longBlock
      q hT n M hKM hKn
  exact
    pairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveCertificateInterface
      hqOdd hq hT hwindow n M hn hLI

/-- Every eligible finite zero window admits one odd prime base for which the
exact sixteen-interaction signed aggregate, rather than the collapsing
pointwise triangle floor, feeds both certificate implications eventually. -/
theorem exists_prime_eventually_pairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveCertificateInterface
    {T : ℝ} (hT : 0 ≤ T)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    {M : ℕ} (hKM : (spectralZetaZeroWindow T).card ≤ M) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        PairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveTargets
          q T n M := by
  obtain ⟨q, hqPrime, hqOdd, hq, hpos⟩ :=
    exists_prime_eventually_posDef_pairedEtaGeometricMultiplicityWeightedZeroGram_and_inv
      (spectralZetaZeroWindow T)
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  exact
    eventually_pairedEtaGeometricReflectionEvenLongBlockSignedMetricReserveCertificateInterface
      hqOdd hq hT hwindow hKM (hpos.mono fun _ hn ↦ hn.1)

end

end RiemannGaussian
