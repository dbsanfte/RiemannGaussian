import RiemannGaussian.EtaCurrentEulerMoments

/-!
# Summable arithmetic errors in the completed Euler current pairs

The exact two-channel pair is retained. Its finite-prefix factors are
replaced by their explicit complex Euler terms only after the signed
product error is identified. The actual head is retained in its own
branch. Every comparison has an explicit arithmetic majorant.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The signed pair of the two explicit completed Euler endpoint terms. -/
def pairedEtaCurrentEulerMomentPair (rho : NontrivialZetaZero) (N k l : ℕ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaCurrentEulerMoment (NontrivialZetaZero.conjugatePartner rho) N k)
    (pairedEtaCurrentEulerMoment (NontrivialZetaZero.conjugatePartner rho) N l)
    (pairedEtaCurrentEulerMoment rho N k) (pairedEtaCurrentEulerMoment rho N l)

/-- The signed actual-head pair with its successor Euler endpoint term. -/
def pairedEtaCurrentEulerHeadPair (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  etaSignedCompletedPair
    (pairedEtaHeadCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N 0)
    (pairedEtaCurrentEulerMoment (NontrivialZetaZero.conjugatePartner rho) N 0)
    (pairedEtaHeadCompletedMoment rho N 0) (pairedEtaCurrentEulerMoment rho N 0)

/-- The exact product error retains both positions and their complex orientation. -/
theorem etaCurrent_product_sub_euler (A B a b : ℂ) :
    A * starRingEnd ℂ B - a * starRingEnd ℂ b =
      (A - a) * starRingEnd ℂ B + a * starRingEnd ℂ (B - b) := by
  rw [map_sub]
  ring

/-- A norm estimate downstream of the exact two-position product identity. -/
theorem norm_etaCurrent_product_sub_euler_le (A B a b : ℂ) :
    ‖A * starRingEnd ℂ B - a * starRingEnd ℂ b‖ ≤
      ‖A - a‖ * ‖B‖ + ‖a‖ * ‖B - b‖ := by
  rw [etaCurrent_product_sub_euler]
  simpa only [norm_mul, norm_conj] using norm_add_le ((A - a) * starRingEnd ℂ B) (a * starRingEnd ℂ (B - b))

/-- One explicit constant controls the two positions in a completed Euler pair. -/
def pairedEtaCurrentEulerPairErrorConstant (rho : NontrivialZetaZero) (k l : ℕ) : ℝ :=
  pairedEtaCurrentEulerMomentErrorConstant rho k * pairedEtaCurrentMomentConstant rho +
    pairedEtaCurrentEulerMomentAmplitude rho k * pairedEtaCurrentEulerMomentErrorConstant rho l

/-- Every completed pair error constant is nonnegative. -/
theorem pairedEtaCurrentEulerPairErrorConstant_nonneg (rho : NontrivialZetaZero) (k l : ℕ) :
    0 ≤ pairedEtaCurrentEulerPairErrorConstant rho k l := by
  have hk := pairedEtaCurrentEulerMomentErrorConstant_nonneg rho k
  have hl := pairedEtaCurrentEulerMomentErrorConstant_nonneg rho l
  have hQ := pairedEtaCurrentMomentConstant_nonneg rho
  unfold pairedEtaCurrentEulerPairErrorConstant pairedEtaCurrentEulerMomentAmplitude
  positivity

/-- Both positions in one actual lower-prefix product gain an extra
inverse-cutoff power after its explicit Euler product is subtracted. -/
theorem norm_pairedEtaCurrent_product_sub_euler_le (rho : NontrivialZetaZero) {k l : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (hl : l < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMoment rho (N + 2) k * starRingEnd ℂ (pairedEtaFiniteCompletedMoment rho (N + 2) l) -
      pairedEtaCurrentEulerMoment rho N k * starRingEnd ℂ (pairedEtaCurrentEulerMoment rho N l)‖ ≤
      pairedEtaCurrentEulerPairErrorConstant rho k l * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) := by
  have hAk := norm_pairedEtaFiniteCompletedMoment_sub_euler_le rho hk N
  have hAl := norm_pairedEtaFiniteCompletedMoment_sub_euler_le rho hl N
  have hQ := pairedEtaCurrentMomentConstant_nonneg rho
  have hDk := pairedEtaCurrentEulerMomentErrorConstant_nonneg rho k
  have hDl := pairedEtaCurrentEulerMomentErrorConstant_nonneg rho l
  have hd := (pairedEtaCurrentMomentDecay_bounds rho N).1
  have ha : 0 ≤ pairedEtaCurrentEulerMomentAmplitude rho k := by
    unfold pairedEtaCurrentEulerMomentAmplitude
    positivity
  have hmodel : ‖pairedEtaCurrentEulerMoment rho N k‖ ≤ pairedEtaCurrentEulerMomentAmplitude rho k :=
    (norm_pairedEtaCurrentEulerMoment_le rho N k).trans
      (mul_le_of_le_one_right ha (pairedEtaCurrentMomentDecay_bounds rho N).2)
  calc
    _ ≤ ‖pairedEtaFiniteCompletedMoment rho (N + 2) k - pairedEtaCurrentEulerMoment rho N k‖ *
        ‖pairedEtaFiniteCompletedMoment rho (N + 2) l‖ + ‖pairedEtaCurrentEulerMoment rho N k‖ *
        ‖pairedEtaFiniteCompletedMoment rho (N + 2) l - pairedEtaCurrentEulerMoment rho N l‖ :=
      norm_etaCurrent_product_sub_euler_le _ _ _ _
    _ ≤ (pairedEtaCurrentEulerMomentErrorConstant rho k * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)) *
        pairedEtaCurrentMomentConstant rho + pairedEtaCurrentEulerMomentAmplitude rho k *
        (pairedEtaCurrentEulerMomentErrorConstant rho l * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)) :=
      add_le_add (mul_le_mul hAk (norm_pairedEtaFiniteCompletedMoment_le rho hl.le N) (norm_nonneg _) (by positivity))
        (mul_le_mul hmodel hAl (norm_nonneg _) ha)
    _ = _ := by unfold pairedEtaCurrentEulerPairErrorConstant; ring

/-- The original complex signed pair error is the partner product error
minus the conjugate original product error. No completion channel is discarded. -/
theorem pairedEtaFiniteCompletedMomentPair_sub_euler (rho : NontrivialZetaZero) (N k l : ℕ) :
    pairedEtaFiniteCompletedMomentPair rho (N + 2) k l - pairedEtaCurrentEulerMomentPair rho N k l =
      (pairedEtaFiniteCompletedMoment (NontrivialZetaZero.conjugatePartner rho) (N + 2) k *
          starRingEnd ℂ (pairedEtaFiniteCompletedMoment (NontrivialZetaZero.conjugatePartner rho) (N + 2) l) -
        pairedEtaCurrentEulerMoment (NontrivialZetaZero.conjugatePartner rho) N k *
          starRingEnd ℂ (pairedEtaCurrentEulerMoment (NontrivialZetaZero.conjugatePartner rho) N l)) -
        starRingEnd ℂ (pairedEtaFiniteCompletedMoment rho (N + 2) k *
            starRingEnd ℂ (pairedEtaFiniteCompletedMoment rho (N + 2) l) -
          pairedEtaCurrentEulerMoment rho N k * starRingEnd ℂ (pairedEtaCurrentEulerMoment rho N l)) := by
  simp only [pairedEtaFiniteCompletedMomentPair, pairedEtaCurrentEulerMomentPair, etaSignedCompletedPair,
    map_sub, map_mul, starRingEnd_apply, star_star]
  ring

/-- The actual signed pair error has an explicit summable endpoint
majorant in both completed channels. -/
theorem norm_pairedEtaFiniteCompletedMomentPair_sub_euler_le (rho : NontrivialZetaZero) {k l : ℕ}
    (hk : k < analyticZetaZeroMultiplicity rho) (hl : l < analyticZetaZeroMultiplicity rho) (N : ℕ) :
    ‖pairedEtaFiniteCompletedMomentPair rho (N + 2) k l - pairedEtaCurrentEulerMomentPair rho N k l‖ ≤
      pairedEtaCurrentEulerPairErrorConstant (NontrivialZetaZero.conjugatePartner rho) k l *
          pairedEtaCurrentMomentDecay (NontrivialZetaZero.conjugatePartner rho) N / (N + 1 : ℝ) +
        pairedEtaCurrentEulerPairErrorConstant rho k l * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ) := by
  have hp := norm_pairedEtaCurrent_product_sub_euler_le (NontrivialZetaZero.conjugatePartner rho)
    (by simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hk)
    (by simpa only [analyticZetaZeroMultiplicity_conjugatePartner] using hl) N
  rw [pairedEtaFiniteCompletedMomentPair_sub_euler]
  exact (norm_sub_le _ _).trans (add_le_add hp
    (by simpa only [norm_conj] using norm_pairedEtaCurrent_product_sub_euler_le rho hk hl N))

/-- The head comparison retains the actual head and replaces only the
successor prefix, with its signed error explicit. -/
theorem pairedEtaHeadCompletedMomentPair_sub_euler (rho : NontrivialZetaZero) (N : ℕ) :
    pairedEtaHeadCompletedMomentPair rho N 0 0 - pairedEtaCurrentEulerHeadPair rho N =
      etaSignedCompletedPair
        (pairedEtaHeadCompletedMoment (NontrivialZetaZero.conjugatePartner rho) N 0)
        (pairedEtaFiniteCompletedMoment (NontrivialZetaZero.conjugatePartner rho) (N + 2) 0 -
          pairedEtaCurrentEulerMoment (NontrivialZetaZero.conjugatePartner rho) N 0)
        (pairedEtaHeadCompletedMoment rho N 0)
        (pairedEtaFiniteCompletedMoment rho (N + 2) 0 - pairedEtaCurrentEulerMoment rho N 0) := by
  simp only [pairedEtaHeadCompletedMomentPair, pairedEtaCurrentEulerHeadPair, etaSignedCompletedPair, map_sub]
  ring

/-- The actual head times the prefix Euler error retains its cutoff
increment and an additional summable endpoint power. -/
theorem norm_pairedEtaCurrent_head_mul_prefix_error_le (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaHeadCompletedMoment rho N 0‖ *
        ‖pairedEtaFiniteCompletedMoment rho (N + 2) 0 - pairedEtaCurrentEulerMoment rho N 0‖ ≤
      pairedEtaLogTailShiftIncrement (N + 1) *
        (pairedEtaCurrentMomentConstant rho * pairedEtaCurrentEulerMomentErrorConstant rho 0 *
          pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)) := by
  have hQ := pairedEtaCurrentMomentConstant_nonneg rho
  have hD := pairedEtaCurrentEulerMomentErrorConstant_nonneg rho 0
  have hdelta := (pairedEtaLogTailShiftIncrement_pos (N + 1)).le
  have hd := (pairedEtaCurrentMomentDecay_bounds rho N).1
  have hh : ‖pairedEtaHeadCompletedMoment rho N 0‖ ≤
      pairedEtaCurrentMomentConstant rho * pairedEtaLogTailShiftIncrement (N + 1) :=
    (norm_pairedEtaHeadCompletedMoment_le rho N 0).trans
      (mul_le_of_le_one_right (mul_nonneg hQ hdelta) (pairedEtaCurrentMomentDecay_bounds rho N).2)
  calc
    _ ≤ (pairedEtaCurrentMomentConstant rho * pairedEtaLogTailShiftIncrement (N + 1)) *
        (pairedEtaCurrentEulerMomentErrorConstant rho 0 * pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)) :=
      mul_le_mul hh (norm_pairedEtaFiniteCompletedMoment_sub_euler_le rho (analyticZetaZeroMultiplicity_positive rho) N)
        (norm_nonneg _) (mul_nonneg hQ hdelta)
    _ = _ := by ring

/-- Both actual head channels satisfy the explicit signed-pair comparison. -/
theorem norm_pairedEtaHeadCompletedMomentPair_sub_euler_le (rho : NontrivialZetaZero) (N : ℕ) :
    ‖pairedEtaHeadCompletedMomentPair rho N 0 0 - pairedEtaCurrentEulerHeadPair rho N‖ ≤
      pairedEtaLogTailShiftIncrement (N + 1) *
        (pairedEtaCurrentMomentConstant (NontrivialZetaZero.conjugatePartner rho) *
            pairedEtaCurrentEulerMomentErrorConstant (NontrivialZetaZero.conjugatePartner rho) 0 *
            pairedEtaCurrentMomentDecay (NontrivialZetaZero.conjugatePartner rho) N / (N + 1 : ℝ) +
          pairedEtaCurrentMomentConstant rho * pairedEtaCurrentEulerMomentErrorConstant rho 0 *
            pairedEtaCurrentMomentDecay rho N / (N + 1 : ℝ)) := by
  rw [pairedEtaHeadCompletedMomentPair_sub_euler, mul_add]
  exact (norm_etaSignedCompletedPair_le _ _ _ _).trans
    (add_le_add (norm_pairedEtaCurrent_head_mul_prefix_error_le (NontrivialZetaZero.conjugatePartner rho) N)
      (norm_pairedEtaCurrent_head_mul_prefix_error_le rho N))

end

end RiemannGaussian
