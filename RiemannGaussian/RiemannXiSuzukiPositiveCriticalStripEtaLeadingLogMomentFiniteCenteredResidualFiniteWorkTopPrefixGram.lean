import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaLeadingLogMomentFiniteCenteredResidualFiniteWorkTopPrefixInterference

/-!
# Gram form and cancellation defect of the top finite-work prefix

The isolated order-`m-1` prefix is one integral of a complex interference
feature `f_N` over the shifted positive eta-tail measure.  This module squares
that identity without taking pointwise absolute values.  It proves

`|C_(m-1,N+1)|^2 = integral Re (f_N(u) * conj (f_N(v))) d(mu_N x mu_N)`.

The Hermitian kernel is symmetric but need not be pointwise nonnegative.  Its
integral is nonnegative because it is an exact rank-one Gram quadratic.  We
also compare it with the positive absolute kernel
`|f_N(u)| |f_N(v)|` and isolate their difference as a nonnegative phase
cancellation defect.  Thus the missing square-root estimate is expressed in
a form that retains, and quantitatively names, all interference discarded by
the triangle inequality.

No upper bound for the Gram integral or lower bound for the cancellation
defect is assumed.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The shifted eta-tail measure is sigma-finite, as it is a measurable image
of a restriction of Lebesgue measure. -/
instance instSFinitePairedEtaShiftedLogTailMeasure (N : ℕ) :
    SFinite (pairedEtaShiftedLogTailMeasure N) := by
  unfold pairedEtaShiftedLogTailMeasure pairedEtaLogTailMeasure
  infer_instance

/-- The complex rank-one Gram kernel of the critical-half top-prefix feature. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) (p : ℝ × ℝ) : ℂ :=
  pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
      rho N p.1 *
    starRingEnd ℂ
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
        rho N p.2)

/-- The real Hermitian kernel whose integral is the top-prefix squared norm. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) (p : ℝ × ℝ) : ℝ :=
  (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel
    rho N p).re

/-- The phase-free positive product kernel dominating the Hermitian kernel. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAbsoluteGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) (p : ℝ × ℝ) : ℝ :=
  ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
      rho N p.1‖ *
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
      rho N p.2‖

/-- Complex conjugation preserves integrability of the top-prefix feature. -/
theorem
    integrable_star_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (fun u : ℝ => starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
          rho N u))
      (pairedEtaShiftedLogTailMeasure (N + 1)) := by
  have h :=
    integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
      rho N
  apply ((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp h).congr
  filter_upwards with u
  exact Complex.conjCLE_apply _

/-- The complex rank-one kernel is integrable on the product tail measure. -/
theorem
    integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel
        rho N)
      ((pairedEtaShiftedLogTailMeasure (N + 1)).prod
        (pairedEtaShiftedLogTailMeasure (N + 1))) := by
  exact
    (integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
      rho N).mul_prod
      (integrable_star_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
        rho N)

/-- The complex product integral is exactly the squared norm of the one-variable
interference integral, embedded in `ℂ`. -/
theorem
    integral_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel_eq_normSq_integral
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel
          rho N p
        ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
          (pairedEtaShiftedLogTailMeasure (N + 1)))) =
      (Complex.normSq
        (∫ u : ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
            rho N u
          ∂pairedEtaShiftedLogTailMeasure (N + 1)) : ℂ) := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel
  rw [integral_prod_mul
      (μ := pairedEtaShiftedLogTailMeasure (N + 1))
      (ν := pairedEtaShiftedLogTailMeasure (N + 1))
      (fun u : ℝ =>
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
          rho N u)
      (fun u : ℝ => starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
          rho N u)),
    integral_conj, Complex.mul_conj]

/-- The real Hermitian Gram kernel is integrable. -/
theorem
    integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
        rho N)
      ((pairedEtaShiftedLogTailMeasure (N + 1)).prod
        (pairedEtaShiftedLogTailMeasure (N + 1))) := by
  exact
    (integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel
      rho N).re

/-- The Hermitian kernel is pointwise symmetric under exchange of its two
positive-measure variables. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel_swap
    (rho : NontrivialZetaZero) (N : ℕ) (p : ℝ × ℝ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
        rho N p.swap =
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
        rho N p := by
  rcases p with ⟨u, v⟩
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel
  simp only [Prod.swap_prod_mk, Complex.mul_re, Complex.conj_re,
    Complex.conj_im]
  ring

/-- The real product-kernel integral is exactly the squared norm of the
critical-half interference integral. -/
theorem
    integral_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel_eq_normSq_integral
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
          rho N p
        ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
          (pairedEtaShiftedLogTailMeasure (N + 1)))) =
      Complex.normSq
        (∫ u : ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
            rho N u
          ∂pairedEtaShiftedLogTailMeasure (N + 1)) := by
  calc
    (∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
          rho N p
        ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
          (pairedEtaShiftedLogTailMeasure (N + 1)))) =
        (∫ p : ℝ × ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel
            rho N p
          ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
            (pairedEtaShiftedLogTailMeasure (N + 1)))).re := by
      exact integral_re
        (integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel
          rho N)
    _ = Complex.normSq
        (∫ u : ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
            rho N u
          ∂pairedEtaShiftedLogTailMeasure (N + 1)) := by
      rw [
        integral_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel_eq_normSq_integral]
      simp

/-- Exact positive Gram identity for the isolated finite-work frontier. -/
theorem
    norm_sq_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_integral_gramKernel
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
        rho N‖ ^ 2 =
      ∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
          rho N p
        ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
          (pairedEtaShiftedLogTailMeasure (N + 1))) := by
  rw [
    norm_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_integral_halfIntegrand,
    Complex.sq_norm,
    integral_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel_eq_normSq_integral]

/-- Although the Hermitian kernel can change sign, its complete product
integral is nonnegative because it is an exact Gram quadratic. -/
theorem
    integral_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel_nonneg
    (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤
      ∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
          rho N p
        ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
          (pairedEtaShiftedLogTailMeasure (N + 1))) := by
  rw [←
    norm_sq_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_integral_gramKernel]
  positivity

/-- The positive absolute product kernel is integrable. -/
theorem
    integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAbsoluteGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) :
    Integrable
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAbsoluteGramKernel
        rho N)
      ((pairedEtaShiftedLogTailMeasure (N + 1)).prod
        (pairedEtaShiftedLogTailMeasure (N + 1))) := by
  exact
    (integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
      rho N).norm.mul_prod
      (integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
        rho N).norm

/-- The absolute product mass factors as the square of the one-variable
absolute envelope. -/
theorem
    integral_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAbsoluteGramKernel_eq_sq_integral_norm
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAbsoluteGramKernel
          rho N p
        ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
          (pairedEtaShiftedLogTailMeasure (N + 1)))) =
      (∫ u : ℝ,
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
          rho N u‖
        ∂pairedEtaShiftedLogTailMeasure (N + 1)) ^ 2 := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAbsoluteGramKernel
  rw [integral_prod_mul
      (μ := pairedEtaShiftedLogTailMeasure (N + 1))
      (ν := pairedEtaShiftedLogTailMeasure (N + 1))
      (fun u : ℝ =>
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
          rho N u‖)
      (fun u : ℝ =>
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
          rho N u‖),
    pow_two]

/-- Pointwise Hermitian mass is bounded by the phase-free positive kernel. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel_le_absoluteGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) (p : ℝ × ℝ) :
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
        rho N p ≤
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAbsoluteGramKernel
        rho N p := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixComplexGramKernel
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAbsoluteGramKernel
  have h := Complex.re_le_norm
    (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
        rho N p.1 *
      starRingEnd ℂ
        (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
          rho N p.2))
  simpa only [norm_mul, norm_conj] using h

/-- The complete Hermitian Gram mass is bounded by the positive absolute
product mass. -/
theorem
    integral_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel_le_absoluteGramKernel
    (rho : NontrivialZetaZero) (N : ℕ) :
    (∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
          rho N p
        ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
          (pairedEtaShiftedLogTailMeasure (N + 1)))) ≤
      ∫ p : ℝ × ℝ,
        pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAbsoluteGramKernel
          rho N p
        ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
          (pairedEtaShiftedLogTailMeasure (N + 1))) := by
  apply integral_mono_ae
  · exact
      integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
        rho N
  · exact
      integrable_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAbsoluteGramKernel
        rho N
  · exact Eventually.of_forall fun p =>
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel_le_absoluteGramKernel
        rho N p

/-- The nonnegative amount of phase-free product mass removed by the actual
Hermitian interference. -/
def pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPhaseCancellationDefect
    (rho : NontrivialZetaZero) (N : ℕ) : ℝ :=
  (∫ p : ℝ × ℝ,
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAbsoluteGramKernel
        rho N p
      ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
        (pairedEtaShiftedLogTailMeasure (N + 1)))) -
    ∫ p : ℝ × ℝ,
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
        rho N p
      ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
        (pairedEtaShiftedLogTailMeasure (N + 1)))

/-- The phase-cancellation defect is nonnegative. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPhaseCancellationDefect_nonneg
    (rho : NontrivialZetaZero) (N : ℕ) :
    0 ≤
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPhaseCancellationDefect
        rho N := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPhaseCancellationDefect
  exact sub_nonneg.mpr
    (integral_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel_le_absoluteGramKernel
      rho N)

/-- Exact cancellation ledger: squared absolute mass is the surviving prefix
Gram plus the phase-cancellation defect. -/
theorem
    norm_sq_topPrefix_add_phaseCancellationDefect_eq_sq_integral_norm_halfIntegrand
    (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
        rho N‖ ^ 2 +
      pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPhaseCancellationDefect
        rho N =
      (∫ u : ℝ,
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixHalfIntegrand
          rho N u‖
        ∂pairedEtaShiftedLogTailMeasure (N + 1)) ^ 2 := by
  unfold
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixPhaseCancellationDefect
  rw [
    norm_sq_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_integral_gramKernel,
    integral_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixAbsoluteGramKernel_eq_sq_integral_norm]
  ring

/-- Pointwise scale identity: the endpoint-scaled Gram mass is the square of
the square-root-scaled top prefix. -/
theorem
    oddEndpoint_mul_integral_topPrefixGramKernel_eq_sq_half_rpow_mul_norm_topPrefix
    (rho : NontrivialZetaZero) (N : ℕ) :
    ((2 * N + 1 : ℕ) : ℝ) *
        (∫ p : ℝ × ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
            rho N p
          ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
            (pairedEtaShiftedLogTailMeasure (N + 1)))) =
      (((((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
          rho N‖) ^ 2) := by
  rw [←
    norm_sq_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_eq_integral_gramKernel,
    ← Real.sqrt_eq_rpow, mul_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ))]

/-- The cancellation-preserving form of the local frontier: the exact
Hermitian Gram mass is eventually bounded after multiplication by the odd
endpoint. -/
def PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramCriticalScaleEventuallyBounded
    (rho : NontrivialZetaZero) : Prop :=
  ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
    ((2 * N + 1 : ℕ) : ℝ) *
        (∫ p : ℝ × ℝ,
          pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
            rho N p
          ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
            (pairedEtaShiftedLogTailMeasure (N + 1)))) ≤ C

/-- At each nontrivial zero, endpoint boundedness of the Hermitian Gram mass
is exactly equivalent to square-root boundedness of the original prefix. -/
theorem
    pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_criticalScale_eventuallyBounded_iff_gram
    (rho : NontrivialZetaZero) :
    PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCriticalScaleEventuallyBounded
        rho ↔
      PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramCriticalScaleEventuallyBounded
        rho := by
  constructor
  · rintro ⟨C, hprefix⟩
    refine ⟨C ^ 2, ?_⟩
    filter_upwards [hprefix] with N hN
    let a : ℝ :=
      (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
          rho N‖
    have ha : 0 ≤ a := by
      dsimp only [a]
      positivity
    have hC : 0 ≤ C := ha.trans hN
    rw [
      oddEndpoint_mul_integral_topPrefixGramKernel_eq_sq_half_rpow_mul_norm_topPrefix]
    change a ^ 2 ≤ C ^ 2
    nlinarith
  · rintro ⟨D, hgram⟩
    refine ⟨D + 1, ?_⟩
    filter_upwards [hgram] with N hN
    let a : ℝ :=
      (((2 * N + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
        ‖pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix
          rho N‖
    have ha : 0 ≤ a := by
      dsimp only [a]
      positivity
    have haSq : a ^ 2 ≤ D := by
      calc
        a ^ 2 =
            ((2 * N + 1 : ℕ) : ℝ) *
              (∫ p : ℝ × ℝ,
                pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramKernel
                  rho N p
                ∂((pairedEtaShiftedLogTailMeasure (N + 1)).prod
                  (pairedEtaShiftedLogTailMeasure (N + 1)))) := by
              symm
              exact
                oddEndpoint_mul_integral_topPrefixGramKernel_eq_sq_half_rpow_mul_norm_topPrefix
                  rho N
        _ ≤ D := hN
    change a ≤ D + 1
    nlinarith [sq_nonneg (a - (1 / 2 : ℝ))]

/-- The global endpoint-scaled Hermitian Gram bound. -/
def AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramCriticalScaleEventuallyBounded :
    Prop :=
  ∀ rho : NontrivialZetaZero,
    PairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramCriticalScaleEventuallyBounded
      rho

/-- The global Gram frontier and the global square-root prefix frontier are
exactly equivalent. -/
theorem
    all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_criticalScale_eventuallyBounded_iff_gram :
    AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixCriticalScaleEventuallyBounded ↔
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramCriticalScaleEventuallyBounded := by
  constructor
  · intro h rho
    exact
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_criticalScale_eventuallyBounded_iff_gram
        rho).mp (h rho)
  · intro h rho
    exact
      (pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_criticalScale_eventuallyBounded_iff_gram
        rho).mpr (h rho)

/-- A universal endpoint bound for the exact Hermitian Gram mass proves the
Riemann hypothesis.  The bound itself remains open. -/
theorem
    riemannHypothesis_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGram_criticalScale_eventuallyBounded
    (hgram :
      AllPairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefixGramCriticalScaleEventuallyBounded) :
    RiemannHypothesis := by
  exact
    riemannHypothesis_of_all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_criticalScale_eventuallyBounded
      (all_pairedEtaCompletedLeadingLogCutoffCenteredPartnerResidualFiniteWorkTopPrefix_criticalScale_eventuallyBounded_iff_gram.mpr
        hgram)

end

end RiemannGaussian
