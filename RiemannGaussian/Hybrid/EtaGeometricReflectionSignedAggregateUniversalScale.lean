import RiemannGaussian.Hybrid.EtaGeometricReflectionSignedAggregateBalance

/-!
# Universal cutoff scale of the balanced signed eta aggregate

The polar--hyperbolic ledger separates a common amplitude from the two
reciprocal radial colours of every off-critical completion pair.  This module
computes the cutoff dependence of that common amplitude exactly.

The norm of a completed coefficient is its fixed leading norm times the
inverse `n`th power of `q ^ Re rho`.  Functional-equation reflection makes the
two real parts sum to one, so the product of the reflected/original norms is a
fixed positive leading product times `q ^ (-n)`.  Consequently every ordered
pair reserve contains the same global factor `q ^ (-2*n)`.  Lean removes that
factor from the complete upper-window reserve and from both certificate
inequalities, proving the normalized and literal targets equivalent.

The remaining carrier is not phase-free: the reflected radial colour has
square equal to the norm of the exact coefficient ratio and tends to zero,
while the two radial colours remain reciprocal.  Thus the theorem removes a
harmless universal decay but leaves the genuine hyperbolic imbalance visible.
No arithmetic threshold or zero-proportion improvement is proved here.
-/

open Complex Matrix Finset Filter Topology
open scoped BigOperators Classical ComplexConjugate ComplexOrder Matrix Real

namespace RiemannGaussian

noncomputable section

/-- Exact norm of a completed geometric-prefix coefficient: fixed leading
norm times the inverse geometric decay at `Re rho`. -/
theorem norm_pairedEtaGeometricCompletedPrefixCoefficient_eq
    {q : ℕ} (hq : 0 < q) (rho : NontrivialZetaZero) (n : ℕ) :
    ‖pairedEtaGeometricCompletedPrefixCoefficient q rho n‖ =
      ‖pairedEtaGeometricCompletedPrefixLeadingCoefficient rho‖ *
        (((q : ℝ) ^ rho.val.re) ^ n)⁻¹ := by
  rw [pairedEtaGeometricCompletedPrefixCoefficient_eq_leading_mul_inv_pow,
    norm_mul, norm_inv, norm_pow]
  change
    ‖pairedEtaGeometricCompletedPrefixLeadingCoefficient rho‖ *
        (‖(((q : ℝ) : ℂ) ^ rho.val)‖ ^ n)⁻¹ = _
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hq)]

/-- Reflection makes the product of the two completion-coefficient norms a
fixed leading product times the universal factor `q ^ (-n)`. -/
theorem pairedEtaGeometricUpperCompletionCoefficientNormProduct_eq
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n 0‖ *
        ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1‖ =
      (‖pairedEtaGeometricCompletedPrefixLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho.1)‖ *
        ‖pairedEtaGeometricCompletedPrefixLeadingCoefficient rho.1‖) *
        ((q : ℝ) ^ n)⁻¹ := by
  unfold pairedEtaGeometricUpperCompletionCoefficientVector
    pairedEtaGeometricUpperReflectionPairZero
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [norm_pairedEtaGeometricCompletedPrefixCoefficient_eq hq,
    norm_pairedEtaGeometricCompletedPrefixCoefficient_eq hq]
  have hqreal : (0 : ℝ) < q := by exact_mod_cast hq
  have hdecay :
      ((((q : ℝ) ^
          (NontrivialZetaZero.conjugatePartner rho.1).val.re) ^ n)⁻¹ *
        (((q : ℝ) ^ rho.1.val.re) ^ n)⁻¹) =
        ((q : ℝ) ^ n)⁻¹ := by
    rw [← mul_inv, ← mul_pow, ← Real.rpow_add hqreal]
    simp [NontrivialZetaZero.conjugatePartner_coe]
  calc
    _ = (‖pairedEtaGeometricCompletedPrefixLeadingCoefficient
          (NontrivialZetaZero.conjugatePartner rho.1)‖ *
        ‖pairedEtaGeometricCompletedPrefixLeadingCoefficient rho.1‖) *
        ((((q : ℝ) ^
          (NontrivialZetaZero.conjugatePartner rho.1).val.re) ^ n)⁻¹ *
          (((q : ℝ) ^ rho.1.val.re) ^ n)⁻¹) := by ring
    _ = _ := by rw [hdecay]

/-- Cutoff-independent geometric mean of the two leading completion-
coefficient norms in one upper reflection pair. -/
def pairedEtaGeometricUpperCoefficientLeadingGeometricMean
    {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T)) : ℝ :=
  Real.sqrt
    (‖pairedEtaGeometricCompletedPrefixLeadingCoefficient
        (NontrivialZetaZero.conjugatePartner rho.1)‖ *
      ‖pairedEtaGeometricCompletedPrefixLeadingCoefficient rho.1‖)

/-- The leading geometric mean of every upper completion pair is strictly
positive. -/
theorem pairedEtaGeometricUpperCoefficientLeadingGeometricMean_pos
    {T : ℝ} (rho : ↑(spectralUpperZetaZeroWindow T)) :
    0 < pairedEtaGeometricUpperCoefficientLeadingGeometricMean rho := by
  unfold pairedEtaGeometricUpperCoefficientLeadingGeometricMean
  apply Real.sqrt_pos.2
  exact mul_pos (norm_pos_iff.mpr (by
    unfold pairedEtaGeometricCompletedPrefixLeadingCoefficient
    exact mul_ne_zero
      (by
        unfold pairedEtaTopPrefixFiniteCompletionWeight
        exact mul_ne_zero
          (pairedEtaXiCompletionFactor_ne_zero
            (NontrivialZetaZero.zero_lt_re _)
            (NontrivialZetaZero.re_lt_one _))
          (NontrivialZetaZero.coe_ne_zero _))
      (pairedEtaLowerMomentGeometricLimit_ne_zero _)))
    (norm_pos_iff.mpr (by
      unfold pairedEtaGeometricCompletedPrefixLeadingCoefficient
      exact mul_ne_zero
        (by
          unfold pairedEtaTopPrefixFiniteCompletionWeight
          exact mul_ne_zero
            (pairedEtaXiCompletionFactor_ne_zero
              (NontrivialZetaZero.zero_lt_re _)
              (NontrivialZetaZero.re_lt_one _))
            (NontrivialZetaZero.coe_ne_zero _))
        (pairedEtaLowerMomentGeometricLimit_ne_zero _)))

/-- The squared moving geometric mean is its squared leading value times the
universal factor `q ^ (-n)`. -/
theorem pairedEtaGeometricUpperCoefficientGeometricMean_sq_eq
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    pairedEtaGeometricUpperCoefficientGeometricMean q rho n ^ 2 =
      pairedEtaGeometricUpperCoefficientLeadingGeometricMean rho ^ 2 *
        ((q : ℝ) ^ n)⁻¹ := by
  unfold pairedEtaGeometricUpperCoefficientGeometricMean
  rw [Real.sq_sqrt (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    pairedEtaGeometricUpperCompletionCoefficientNormProduct_eq hq]
  unfold pairedEtaGeometricUpperCoefficientLeadingGeometricMean
  rw [Real.sq_sqrt (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

/-- The square of the reflected radial colour is exactly the norm of the
reflected-partner/original completion-coefficient ratio. -/
theorem pairedEtaGeometricUpperCoefficientRadialBalance_zero_sq_eq_ratio_norm
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    pairedEtaGeometricUpperCoefficientRadialBalance q rho n 0 ^ 2 =
      ‖pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio q rho n‖ := by
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
    pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio
  change (a / g) ^ 2 =
    ‖pairedEtaGeometricUpperCompletionCoefficientVector q rho n 0 /
      pairedEtaGeometricUpperCompletionCoefficientVector q rho n 1‖
  rw [norm_div]
  change (a / g) ^ 2 = a / b
  field_simp
  nlinarith

/-- For every upper representative, the squared reflected radial colour tends
to zero along the geometric block start. -/
theorem tendsto_pairedEtaGeometricUpperCoefficientRadialBalance_zero_sq
    {q : ℕ} (hq : 1 < q) {T : ℝ}
    (rho : ↑(spectralUpperZetaZeroWindow T)) :
    Tendsto
      (fun n ↦
        pairedEtaGeometricUpperCoefficientRadialBalance q rho n 0 ^ 2)
      atTop (nhds 0) := by
  rw [show
      (fun n ↦
        pairedEtaGeometricUpperCoefficientRadialBalance q rho n 0 ^ 2) =
      fun n ↦
        ‖pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio q rho n‖ by
    funext n
    exact
      pairedEtaGeometricUpperCoefficientRadialBalance_zero_sq_eq_ratio_norm
        hq.le rho n]
  simpa using
    (tendsto_pairedEtaGeometricUpperPartnerToOriginalCoefficientRatio
      hq rho).norm

/-- Every ordered-pair balance scale is the same universal `q ^ (-2*n)`
factor times a cutoff-independent positive leading scale. -/
theorem pairedEtaGeometricUpperPairBalanceScale_eq_universalScale_mul
    {q : ℕ} (hq : 0 < q) {T : ℝ}
    (zeta rho : ↑(spectralUpperZetaZeroWindow T)) (n : ℕ) :
    pairedEtaGeometricUpperPairBalanceScale q zeta rho n =
      (((q : ℝ) ^ n)⁻¹) ^ 2 *
        (pairedEtaGeometricUpperCoefficientLeadingGeometricMean zeta *
          pairedEtaGeometricUpperCoefficientLeadingGeometricMean rho) ^ 2 := by
  unfold pairedEtaGeometricUpperPairBalanceScale
  rw [mul_pow,
    pairedEtaGeometricUpperCoefficientGeometricMean_sq_eq hq,
    pairedEtaGeometricUpperCoefficientGeometricMean_sq_eq hq]
  ring

/-- Complete balanced upper-window reserve after removing the universal
cutoff scale while retaining each zero pair's leading amplitude. -/
def pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve
    (q : ℕ) (T : ℝ) (n M : ℕ) : ℝ :=
  ∑ rho : ↑(spectralUpperZetaZeroWindow T),
    ∑ zeta ∈ (Finset.univ :
        Finset ↑(spectralUpperZetaZeroWindow T)).erase rho,
      (pairedEtaGeometricUpperCoefficientLeadingGeometricMean zeta *
        pairedEtaGeometricUpperCoefficientLeadingGeometricMean rho) ^ 2 *
        pairedEtaGeometricUpperPairBalancedMetricReserve q zeta rho n M

/-- The literal signed upper-window reserve is exactly the universal
`q ^ (-2*n)` factor times the coefficient-normalized balanced carrier. -/
theorem pairedEtaGeometricUpperWindowSignedMetricReserve_eq_universalScale_mul_normalizedBalanced
    {q : ℕ} (hq : 0 < q) (T : ℝ) (n M : ℕ) :
    pairedEtaGeometricUpperWindowSignedMetricReserve q T n M =
      (((q : ℝ) ^ n)⁻¹) ^ 2 *
        pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve
          q T n M := by
  rw [pairedEtaGeometricUpperWindowSignedMetricReserve_eq_scaled_balanced
    hq]
  unfold pairedEtaGeometricUpperWindowScaledBalancedMetricReserve
    pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho _hrho
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro zeta _hzeta
  rw [pairedEtaGeometricUpperPairBalanceScale_eq_universalScale_mul hq]
  ring

/-- Conversely, the coefficient-normalized carrier is the literal reserve
multiplied by the positive universal factor `q ^ (2*n)`. -/
theorem pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve_eq_scale_mul_signed
    {q : ℕ} (hq : 0 < q) (T : ℝ) (n M : ℕ) :
    pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve
        q T n M =
      ((q : ℝ) ^ n) ^ 2 *
        pairedEtaGeometricUpperWindowSignedMetricReserve q T n M := by
  rw [pairedEtaGeometricUpperWindowSignedMetricReserve_eq_universalScale_mul_normalizedBalanced
    hq]
  have hqn : (q : ℝ) ^ n ≠ 0 := pow_ne_zero n (by exact_mod_cast hq.ne')
  field_simp

/-- The coefficient-normalized balanced upper-window reserve is
nonnegative. -/
theorem pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve_nonneg
    {q : ℕ} (hqOdd : Odd q) (hq : 1 < q) (T : ℝ)
    {n : ℕ} (hn : 1 ≤ n) (M : ℕ) :
    0 ≤ pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve
      q T n M := by
  rw [pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve_eq_scale_mul_signed
    hq.le]
  exact mul_nonneg (sq_nonneg _) <|
    pairedEtaGeometricUpperWindowSignedMetricReserve_nonneg
      hqOdd hq T hn M

/-- Full literal frame potential multiplied by the same positive universal
coefficient scale removed from the upper reserve. -/
def pairedEtaGeometricReflectionEvenCoefficientNormalizedFramePotential
    (q : ℕ) (T : ℝ) (n M : ℕ) : ℝ :=
  ((q : ℝ) ^ n) ^ 2 *
    pairedEtaReflectionEvenFramePotential
      (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T

/-- The `13/18` and finite-window `18/18` certificate implications after the
common positive coefficient scale is removed from both sides. -/
def PairedEtaGeometricReflectionEvenLongBlockCoefficientNormalizedBalancedMetricReserveTargets
    (q : ℕ) (T : ℝ) (n M : ℕ) : Prop :=
  ((((31 : ℝ) * (spectralZetaZeroWindow T).card - 36) *
        pairedEtaGeometricReflectionEvenCoefficientNormalizedFramePotential
          q T n M <
      36 *
        pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve
          q T n M) →
    (13 : ℝ) / 18 <
      (spectralCriticalZetaZeroWindow T).card /
        (spectralZetaZeroWindow T).card) ∧
  (((((spectralZetaZeroWindow T).card : ℝ) - 1) *
        pairedEtaGeometricReflectionEvenCoefficientNormalizedFramePotential
          q T n M ≤
      pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve
        q T n M) →
    (spectralCriticalZetaZeroWindow T).card =
      (spectralZetaZeroWindow T).card)

/-- Removing the universal positive coefficient scale changes neither of the
two exact balanced certificate implications. -/
theorem pairedEtaGeometricReflectionEvenLongBlockCoefficientNormalizedBalancedMetricReserveTargets_iff_scaledBalanced
    {q : ℕ} (hq : 0 < q) (T : ℝ) (n M : ℕ) :
    PairedEtaGeometricReflectionEvenLongBlockCoefficientNormalizedBalancedMetricReserveTargets
        q T n M ↔
      PairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveTargets
        q T n M := by
  let s : ℝ := ((q : ℝ) ^ n) ^ 2
  have hs : 0 < s := by
    unfold s
    positivity
  have hlt (x y : ℝ) : s * x < s * y ↔ x < y :=
    mul_lt_mul_iff_of_pos_left hs
  have hle (x y : ℝ) : s * x ≤ s * y ↔ x ≤ y :=
    mul_le_mul_iff_of_pos_left hs
  have hreserve :
      pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve
          q T n M =
        s * pairedEtaGeometricUpperWindowScaledBalancedMetricReserve
          q T n M := by
    rw [pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve_eq_scale_mul_signed
      hq,
      pairedEtaGeometricUpperWindowSignedMetricReserve_eq_scaled_balanced hq]
  unfold
    PairedEtaGeometricReflectionEvenLongBlockCoefficientNormalizedBalancedMetricReserveTargets
    PairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveTargets
    pairedEtaGeometricReflectionEvenCoefficientNormalizedFramePotential
  change
    (((((31 : ℝ) * (spectralZetaZeroWindow T).card - 36) *
          (s * pairedEtaReflectionEvenFramePotential
            (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T) <
        36 *
          pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve
            q T n M) → _) ∧
      (((((spectralZetaZeroWindow T).card : ℝ) - 1) *
          (s * pairedEtaReflectionEvenFramePotential
            (fun j : Fin M ↦ pairedEtaGeometricHyperbolicCutoff q n j) T) ≤
        pairedEtaGeometricUpperWindowCoefficientNormalizedBalancedMetricReserve
          q T n M) → _)) ↔ _
  rw [hreserve]
  constructor <;> intro htargets
  · constructor
    · intro hthreshold
      exact htargets.1 <| by
        have hscaled := (hlt _ _).2 hthreshold
        nlinarith [hscaled]
    · intro hthreshold
      exact htargets.2 <| by
        have hscaled := (hle _ _).2 hthreshold
        nlinarith [hscaled]
  · constructor
    · intro hthreshold
      apply htargets.1
      apply (hlt _ _).1
      nlinarith
    · intro hthreshold
      apply htargets.2
      apply (hle _ _).1
      nlinarith

/-- Every eligible finite zero window admits one odd prime whose sufficiently
late blocks expose the equivalent coefficient-normalized certificate targets. -/
theorem exists_prime_eventually_pairedEtaGeometricReflectionEvenLongBlockCoefficientNormalizedBalancedMetricReserveCertificateInterface
    {T : ℝ} (hT : 0 ≤ T)
    (hwindow : (spectralZetaZeroWindow T).Nonempty)
    {M : ℕ} (hKM : (spectralZetaZeroWindow T).card ≤ M) :
    ∃ q : ℕ, q.Prime ∧ Odd q ∧ 1 < q ∧
      ∀ᶠ n in atTop,
        PairedEtaGeometricReflectionEvenLongBlockCoefficientNormalizedBalancedMetricReserveTargets
          q T n M := by
  obtain ⟨q, hqPrime, hqOdd, hq, hcert⟩ :=
    exists_prime_eventually_pairedEtaGeometricReflectionEvenLongBlockScaledBalancedMetricReserveCertificateInterface
      hT hwindow hKM
  refine ⟨q, hqPrime, hqOdd, hq, ?_⟩
  filter_upwards [hcert] with n hn
  rw [pairedEtaGeometricReflectionEvenLongBlockCoefficientNormalizedBalancedMetricReserveTargets_iff_scaledBalanced
    hq.le]
  exact hn

end

end RiemannGaussian
