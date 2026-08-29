import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevBaseline

/-!
# Coupling the Suzuki center displacement to the PNT remainder

The normalized frontier contains a convex defect in the canonical center
displacement and a centered PNT remainder.  They are not independent: the
center is selected by the weighted Chebyshev mass, while the remainder is the
centered first log-moment of the same arithmetic measure.

This file makes that coupling literal.  It separates the weighted mass and
log-moment into their continuous comparison values and arithmetic errors,
identifies the centered PNT remainder with their affine combination, and
shows that the mass error is the gradient of the convex reserve plus a
source-exact lower-order slope term.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## Continuous comparison statistics -/

/-- Weighted mass of the continuous comparison density on `[1,b]`. -/
def suzukiChebyshevContinuousMass (b : ℝ) : ℝ :=
  2 * b ^ (1 / 2 : ℝ) - 1

/-- Weighted log-moment of the continuous comparison density on `[1,b]`. -/
def suzukiChebyshevContinuousLogMoment (b : ℝ) : ℝ :=
  2 * b ^ (1 / 2 : ℝ) * (Real.log b - 2) + 4

/-- Difference between the arithmetic weighted mass and its continuous
comparison. -/
def suzukiChebyshevWeightedMassError (b : ℝ) : ℝ :=
  suzukiChebyshevWeightedMass b - suzukiChebyshevContinuousMass b

/-- Difference between the arithmetic weighted log-moment and its continuous
comparison. -/
def suzukiChebyshevWeightedLogMomentError (b : ℝ) : ℝ :=
  suzukiChebyshevWeightedLogMoment b -
    suzukiChebyshevContinuousLogMoment b

/-- The continuous centered moment is exactly continuous log-moment minus
`center` times continuous mass. -/
theorem suzukiChebyshevCenteredContinuousMain_eq_logMoment_sub_center_mul_mass
    (center : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    suzukiChebyshevCenteredContinuousMain center b =
      suzukiChebyshevContinuousLogMoment b -
        center * suzukiChebyshevContinuousMass b := by
  rw [suzukiChebyshevCenteredContinuousMain_eq_explicit center hb]
  unfold suzukiChebyshevContinuousLogMoment
    suzukiChebyshevContinuousMass
  ring_nf

/-- At every natural endpoint, the complete centered PNT remainder is
exactly log-moment error minus `center` times mass error. -/
theorem suzukiChebyshevCenteredPNTError_nat_eq_logMomentError_sub_center_mul_massError
    (center : ℝ) (cutoff : ℕ) :
    suzukiChebyshevCenteredPNTError center
        (((cutoff + 1 : ℕ) : ℝ)) =
      suzukiChebyshevWeightedLogMomentError
          (((cutoff + 1 : ℕ) : ℝ)) -
        center * suzukiChebyshevWeightedMassError
          (((cutoff + 1 : ℕ) : ℝ)) := by
  let b : ℝ := ((cutoff + 1 : ℕ) : ℝ)
  have hb : 1 ≤ b := by
    dsimp only [b]
    exact_mod_cast (show 1 ≤ cutoff + 1 by omega)
  have hcentered :=
    suzukiChebyshevWeightedCenteredLogMoment_nat_eq_continuousMain_add_pntError
      center cutoff
  have hcontinuous :=
    suzukiChebyshevCenteredContinuousMain_eq_logMoment_sub_center_mul_mass
      center hb
  change suzukiChebyshevCenteredPNTError center b =
    suzukiChebyshevWeightedLogMomentError b -
      center * suzukiChebyshevWeightedMassError b
  change suzukiChebyshevWeightedCenteredLogMoment center b =
    suzukiChebyshevCenteredContinuousMain center b +
      suzukiChebyshevCenteredPNTError center b at hcentered
  unfold suzukiChebyshevWeightedCenteredLogMoment at hcentered
  unfold suzukiChebyshevWeightedLogMomentError
    suzukiChebyshevWeightedMassError
  rw [hcontinuous] at hcentered
  linarith

/-- Canonical specialization of the exact centered mass--moment coupling. -/
theorem suzukiChebyshevCenteredPNTError_firstTail_eq_coupledErrors
    (count : ℕ) :
    suzukiChebyshevCenteredPNTError
        (suzukiFirstTailChebyshevCenter count)
        (((count + 2 : ℕ) : ℝ)) =
      suzukiChebyshevWeightedLogMomentError
          (((count + 2 : ℕ) : ℝ)) -
        suzukiFirstTailChebyshevCenter count *
          suzukiChebyshevWeightedMassError
            (((count + 2 : ℕ) : ℝ)) := by
  simpa only [show count + 2 = (count + 1) + 1 by omega] using
    suzukiChebyshevCenteredPNTError_nat_eq_logMomentError_sub_center_mul_massError
      (suzukiFirstTailChebyshevCenter count) (count + 1)

/-! ## The mass error as convex-reserve gradient -/

/-- Source-exact slope terms left after removing the leading positive
exponential from the Archimedean slope and the `-1` in continuous mass. -/
def suzukiChebyshevArchimedeanSlopeLowerOrder (center : ℝ) : ℝ :=
  -2 * Real.exp (-center / 2) +
    ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1 +
    1 / 4 * suzukiPointwiseLerchGapSlope center

/-- The derivative of the convex reserve with respect to its center is the
leading square-root-scale mass displacement. -/
theorem hasDerivAt_suzukiChebyshevArchimedeanConvexReserve
    {center b : ℝ} :
    HasDerivAt
      (fun r : ℝ => suzukiChebyshevArchimedeanConvexReserve r b)
      (2 * b ^ (1 / 2 : ℝ) *
        (Real.exp ((center - Real.log b) / 2) - 1))
      center := by
  have hinner : HasDerivAt
      (fun r : ℝ => (r - Real.log b) / 2) (1 / 2) center := by
    simpa only [id_eq] using
      ((hasDerivAt_id center).sub_const (Real.log b)).div_const 2
  have hexponential :=
    (Real.hasDerivAt_exp ((center - Real.log b) / 2)).comp center hinner
  unfold suzukiChebyshevArchimedeanConvexReserve
  have hscaled := ((hexponential.sub_const 1).sub hinner).const_mul
    (4 * b ^ (1 / 2 : ℝ))
  exact hscaled.congr_deriv (by ring_nf)

/-- Exact slope decomposition relative to continuous weighted mass. -/
theorem suzukiPointwiseArchimedeanSlope_sub_continuousMass_eq
    (center : ℝ) {b : ℝ} (hb : 0 < b) :
    suzukiPointwiseArchimedeanSlope center -
        suzukiChebyshevContinuousMass b =
      2 * b ^ (1 / 2 : ℝ) *
          (Real.exp ((center - Real.log b) / 2) - 1) +
        suzukiChebyshevArchimedeanSlopeLowerOrder center := by
  have hscale :
      b ^ (1 / 2 : ℝ) *
          Real.exp ((center - Real.log b) / 2) =
        Real.exp (center / 2) := by
    rw [Real.rpow_def_of_pos hb, ← Real.exp_add]
    congr 1
    ring_nf
  unfold suzukiPointwiseArchimedeanSlope
    suzukiChebyshevContinuousMass
    suzukiChebyshevArchimedeanSlopeLowerOrder
  rw [← hscale]
  ring_nf

/-- At the canonical slope-matching point, the arithmetic mass error is the
gradient of the convex reserve plus the lower-order slope term. -/
theorem suzukiChebyshevWeightedMassError_firstTail_eq_reserveGradient_add_lowerOrder
    (count : ℕ) :
    suzukiChebyshevWeightedMassError (((count + 2 : ℕ) : ℝ)) =
      2 * (((count + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          (Real.exp
              ((suzukiFirstTailChebyshevCenter count -
                Real.log (((count + 2 : ℕ) : ℝ))) / 2) - 1) +
        suzukiChebyshevArchimedeanSlopeLowerOrder
          (suzukiFirstTailChebyshevCenter count) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  change suzukiChebyshevWeightedMassError b = _
  have hbpos : 0 < b := by
    dsimp only [b]
    exact_mod_cast (show 0 < count + 2 by omega)
  have hmatch :
      suzukiPointwiseArchimedeanSlope r =
        suzukiChebyshevWeightedMass b := by
    dsimp only [r, b]
    exact
      suzukiPointwiseArchimedeanSlope_firstTailChebyshevCenter_eq_mass
        count
  have hdecomposition :=
    suzukiPointwiseArchimedeanSlope_sub_continuousMass_eq r hbpos
  unfold suzukiChebyshevWeightedMassError
  rw [← hmatch]
  exact hdecomposition

/-! ## Square-root normalization of the mass coupling -/

private theorem suzukiPointwiseLerchGapSlopeSummand_nonnegative
    (center : ℝ) (n : ℕ) :
    0 ≤ suzukiPointwiseLerchGapSlopeSummand center n := by
  unfold suzukiPointwiseLerchGapSlopeSummand
  positivity

private theorem suzukiPointwiseLerchGapSlopeSummand_le_logTwo
    {center : ℝ} (hcenter : Real.log 2 ≤ center) (n : ℕ) :
    suzukiPointwiseLerchGapSlopeSummand center n ≤
      suzukiPointwiseLerchGapSlopeSummand (Real.log 2) n := by
  let a : ℝ := (n : ℝ) + 1 / 4
  have ha : 0 < a := by
    dsimp only [a]
    positivity
  have hexponential :
      Real.exp (-2 * a * center) ≤
        Real.exp (-2 * a * Real.log 2) :=
    Real.exp_le_exp.mpr (by nlinarith)
  unfold suzukiPointwiseLerchGapSlopeSummand
  change 2 * Real.exp (-2 * a * center) / a ≤
    2 * Real.exp (-2 * a * Real.log 2) / a
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexponential (by norm_num)) ha.le

/-- The positive Lerch slope decreases after the first-event base. -/
theorem suzukiPointwiseLerchGapSlope_le_logTwo
    {center : ℝ} (hcenter : Real.log 2 ≤ center) :
    suzukiPointwiseLerchGapSlope center ≤
      suzukiPointwiseLerchGapSlope (Real.log 2) := by
  have hlogPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hcenterPos : 0 < center := hlogPos.trans_le hcenter
  unfold suzukiPointwiseLerchGapSlope
  exact
    (summable_suzukiPointwiseLerchGapSlopeSummand hcenterPos).tsum_le_tsum
      (suzukiPointwiseLerchGapSlopeSummand_le_logTwo hcenter)
      (summable_suzukiPointwiseLerchGapSlopeSummand hlogPos)

/-- The source-exact lower-order slope is uniformly bounded on the complete
first tail. -/
theorem abs_suzukiChebyshevArchimedeanSlopeLowerOrder_le
    {center : ℝ} (hcenter : Real.log 2 ≤ center) :
    |suzukiChebyshevArchimedeanSlopeLowerOrder center| ≤
      2 +
        |((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1| +
        1 / 4 * suzukiPointwiseLerchGapSlope (Real.log 2) := by
  let coefficient : ℝ :=
    ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1
  let slope : ℝ := suzukiPointwiseLerchGapSlope center
  have hlogPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hcenterNonneg : 0 ≤ center := hlogPos.le.trans hcenter
  have hdecay : Real.exp (-center / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hdecayAbs : |-2 * Real.exp (-center / 2)| ≤ 2 := by
    rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
      (by norm_num) (Real.exp_pos _).le)]
    nlinarith [Real.exp_pos (-center / 2)]
  have hslopeNonneg : 0 ≤ slope := by
    dsimp only [slope, suzukiPointwiseLerchGapSlope]
    exact tsum_nonneg fun n =>
      suzukiPointwiseLerchGapSlopeSummand_nonnegative center n
  have hslopeUpper :
      slope ≤ suzukiPointwiseLerchGapSlope (Real.log 2) := by
    dsimp only [slope]
    exact suzukiPointwiseLerchGapSlope_le_logTwo hcenter
  have hslopeAbs : |(1 / 4 : ℝ) * slope| ≤
      1 / 4 * suzukiPointwiseLerchGapSlope (Real.log 2) := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hslopeNonneg)]
    exact mul_le_mul_of_nonneg_left hslopeUpper (by norm_num)
  have hbound :
      |-2 * Real.exp (-center / 2) + coefficient +
          (1 / 4 : ℝ) * slope| ≤
        2 + |coefficient| +
          1 / 4 * suzukiPointwiseLerchGapSlope (Real.log 2) := by
    calc
    |-2 * Real.exp (-center / 2) + coefficient +
        (1 / 4 : ℝ) * slope| ≤
        |-2 * Real.exp (-center / 2)| + |coefficient| +
          |(1 / 4 : ℝ) * slope| := by
      calc
        |-2 * Real.exp (-center / 2) + coefficient +
            (1 / 4 : ℝ) * slope| ≤
            |-2 * Real.exp (-center / 2) + coefficient| +
              |(1 / 4 : ℝ) * slope| := abs_add_le _ _
        _ ≤ (|-2 * Real.exp (-center / 2)| + |coefficient|) +
              |(1 / 4 : ℝ) * slope| := by
          have habs := abs_add_le (-2 * Real.exp (-center / 2)) coefficient
          linarith
    _ ≤ 2 + |coefficient| +
          1 / 4 * suzukiPointwiseLerchGapSlope (Real.log 2) :=
      add_le_add (add_le_add hdecayAbs le_rfl) hslopeAbs
  unfold suzukiChebyshevArchimedeanSlopeLowerOrder
  dsimp only [coefficient, slope] at hbound
  convert hbound using 1
  ring_nf

/-- The lower-order slope vanishes after normalization by the square root of
the canonical endpoint. -/
theorem
    tendsto_archimedeanSlopeLowerOrder_firstTail_div_sqrt_endpoint_zero :
    Tendsto
      (fun count : ℕ =>
        suzukiChebyshevArchimedeanSlopeLowerOrder
            (suzukiFirstTailChebyshevCenter count) /
          Real.sqrt (((count + 2 : ℕ) : ℝ)))
      atTop (nhds 0) := by
  let bound : ℝ :=
    2 +
      |((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1| +
      1 / 4 * suzukiPointwiseLerchGapSlope (Real.log 2)
  let endpoint : ℕ → ℝ := fun count => ((count + 2 : ℕ) : ℝ)
  have hendpointTop : Tendsto endpoint atTop atTop := by
    dsimp only [endpoint]
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_atTop_add_const_right atTop (2 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hendpointPos (count : ℕ) : 0 < endpoint count := by
    dsimp only [endpoint]
    exact_mod_cast (show 0 < count + 2 by omega)
  have hinvSqrt :
      Tendsto (fun count : ℕ => endpoint count ^ (-1 / 2 : ℝ))
        atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_div] using
      ((tendsto_rpow_neg_atTop
          (by norm_num : (0 : ℝ) < 1 / 2)).comp hendpointTop)
  have hmajor :
      Tendsto (fun count : ℕ =>
        bound * endpoint count ^ (-1 / 2 : ℝ))
        atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hinvSqrt
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun _count => norm_nonneg _
  · exact Eventually.of_forall fun count => by
      let b : ℝ := endpoint count
      let r : ℝ := suzukiFirstTailChebyshevCenter count
      change ‖suzukiChebyshevArchimedeanSlopeLowerOrder r /
          Real.sqrt b‖ ≤ bound * b ^ (-1 / 2 : ℝ)
      have hbpos : 0 < b := by
        dsimp only [b]
        exact hendpointPos count
      have hsqrtPos : 0 < Real.sqrt b := Real.sqrt_pos.2 hbpos
      have hlowerOrder :
          |suzukiChebyshevArchimedeanSlopeLowerOrder r| ≤ bound := by
        dsimp only [r, bound]
        exact abs_suzukiChebyshevArchimedeanSlopeLowerOrder_le
          (log_two_le_suzukiFirstTailChebyshevCenter count)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hsqrtPos]
      calc
        |suzukiChebyshevArchimedeanSlopeLowerOrder r| /
              Real.sqrt b ≤ bound / Real.sqrt b :=
          div_le_div_of_nonneg_right hlowerOrder hsqrtPos.le
        _ = bound * b ^ (-1 / 2 : ℝ) := by
          rw [div_eq_mul_inv, Real.sqrt_eq_rpow,
            ← Real.rpow_neg hbpos.le]
          congr 2
          ring
  · exact hmajor

/-- Dimensionless mass coupling: the normalized arithmetic mass error is
asymptotic to the gradient of the exponential convexity defect. -/
theorem
    tendsto_normalizedMassError_sub_exponentialGradient_firstTail_zero :
    Tendsto
      (fun count : ℕ =>
        suzukiChebyshevWeightedMassError
              (((count + 2 : ℕ) : ℝ)) /
            Real.sqrt (((count + 2 : ℕ) : ℝ)) -
          2 *
            (Real.exp
                ((suzukiFirstTailChebyshevCenter count -
                  Real.log (((count + 2 : ℕ) : ℝ))) / 2) - 1))
      atTop (nhds 0) := by
  apply
    tendsto_archimedeanSlopeLowerOrder_firstTail_div_sqrt_endpoint_zero.congr'
  exact Eventually.of_forall fun count => by
    let b : ℝ := ((count + 2 : ℕ) : ℝ)
    let r : ℝ := suzukiFirstTailChebyshevCenter count
    simp only
    change suzukiChebyshevArchimedeanSlopeLowerOrder r /
        Real.sqrt b =
      suzukiChebyshevWeightedMassError b / Real.sqrt b -
        2 * (Real.exp ((r - Real.log b) / 2) - 1)
    have hbpos : 0 < b := by
      dsimp only [b]
      exact_mod_cast (show 0 < count + 2 by omega)
    have hcoupling :=
      suzukiChebyshevWeightedMassError_firstTail_eq_reserveGradient_add_lowerOrder
        count
    change suzukiChebyshevWeightedMassError b =
      2 * b ^ (1 / 2 : ℝ) *
          (Real.exp ((r - Real.log b) / 2) - 1) +
        suzukiChebyshevArchimedeanSlopeLowerOrder r at hcoupling
    rw [hcoupling, Real.sqrt_eq_rpow]
    have hpower : b ^ (1 / 2 : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos hbpos _).ne'
    field_simp [hpower]
    ring_nf

end

end RiemannGaussian
