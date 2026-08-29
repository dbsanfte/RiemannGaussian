import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevCumulativeEnvelope

/-!
# Convex Archimedean reserve at the Suzuki frontier

The centered PNT remainder is now known to have square-root magnitude.  To
compare it with the smooth side at the correct scale, this file splits the
exact Archimedean baseline into

* a nonnegative exponential convexity reserve of square-root scale, and
* a source-exact lower-order term with an explicit logarithmic loss.

The resulting lower bound is transferred back to the literal transport gap.
It does not assert that the arithmetic remainder has the required sign.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## Exact smooth decomposition -/

/-- The complete smooth term which accompanies the centered PNT remainder
at endpoint `b`. -/
def suzukiChebyshevArchimedeanBaseline (center b : ℝ) : ℝ :=
  suzukiPointwiseArchimedean center +
    2 * (b ^ (1 / 2 : ℝ) * (Real.log b - center - 2)) +
      center + 4

/-- The leading square-root contribution, written as the Bregman remainder
of the exponential at the logarithmic endpoint. -/
def suzukiChebyshevArchimedeanConvexReserve
    (center b : ℝ) : ℝ :=
  4 * b ^ (1 / 2 : ℝ) *
    (Real.exp ((center - Real.log b) / 2) - 1 -
      (center - Real.log b) / 2)

/-- The source-exact terms left after extracting the exponential convexity
reserve from the smooth baseline. -/
def suzukiChebyshevArchimedeanLowerOrder (center : ℝ) : ℝ :=
  4 * Real.exp (-center / 2) - 4 +
    center *
      (((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1) +
    1 / 4 *
      (suzukiHurwitzLerchTwo 1 -
        Real.exp (-center / 2) *
          suzukiHurwitzLerchTwo (Real.exp (-2 * center)))

/-- Exact decomposition of the smooth baseline into its convex reserve and
lower-order source terms. -/
theorem suzukiChebyshevArchimedeanBaseline_eq_reserve_add_lowerOrder
    (center : ℝ) {b : ℝ} (hb : 0 < b) :
    suzukiChebyshevArchimedeanBaseline center b =
      suzukiChebyshevArchimedeanConvexReserve center b +
        suzukiChebyshevArchimedeanLowerOrder center := by
  have hscale :
      b ^ (1 / 2 : ℝ) *
          Real.exp ((center - Real.log b) / 2) =
        Real.exp (center / 2) := by
    rw [Real.rpow_def_of_pos hb, ← Real.exp_add]
    congr 1
    ring_nf
  unfold suzukiChebyshevArchimedeanBaseline
    suzukiChebyshevArchimedeanConvexReserve
    suzukiChebyshevArchimedeanLowerOrder
    suzukiPointwiseArchimedean
  rw [← hscale]
  ring_nf

/-- The extracted leading reserve is nonnegative by convexity of the real
exponential. -/
theorem suzukiChebyshevArchimedeanConvexReserve_nonnegative
    (center : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ suzukiChebyshevArchimedeanConvexReserve center b := by
  have hexponential :=
    Real.add_one_le_exp ((center - Real.log b) / 2)
  unfold suzukiChebyshevArchimedeanConvexReserve
  exact mul_nonneg
    (mul_nonneg (by norm_num) (Real.rpow_nonneg hb _)) (by linarith)

/-- Dividing by the endpoint square root exposes the dimensionless
exponential convexity defect exactly. -/
theorem suzukiChebyshevArchimedeanConvexReserve_div_sqrt
    (center : ℝ) {b : ℝ} (hb : 0 < b) :
    suzukiChebyshevArchimedeanConvexReserve center b / Real.sqrt b =
      4 * (Real.exp ((center - Real.log b) / 2) - 1 -
        (center - Real.log b) / 2) := by
  unfold suzukiChebyshevArchimedeanConvexReserve
  rw [Real.sqrt_eq_rpow]
  field_simp [(Real.rpow_pos_of_pos hb (1 / 2 : ℝ)).ne']

/-! ## An explicit logarithmic lower loss -/

private theorem log_pi_lt_three_halves :
    Real.log Real.pi < (3 / 2 : ℝ) := by
  have hexponential :=
    Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) 4
  have hpiExp : Real.pi < Real.exp (3 / 2 : ℝ) := by
    calc
      Real.pi < 4 := Real.pi_lt_four
      _ < ∑ i ∈ Finset.range 4,
          (3 / 2 : ℝ) ^ i / i.factorial := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp (3 / 2 : ℝ) := hexponential
  exact (Real.log_lt_iff_lt_exp Real.pi_pos).2 hpiExp

private theorem neg_fifteen_eighths_lt_archimedeanLinearCoefficient :
    (-15 / 8 : ℝ) <
      ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1 := by
  nlinarith [re_digamma_quarter_gt_strong_lower_bound,
    log_pi_lt_three_halves]

/-- The lower-order source term loses at most a fixed constant plus
`(15/8) * center` on nonnegative time. -/
theorem neg_four_sub_fifteen_eighths_mul_le_archimedeanLowerOrder
    {center : ℝ} (hcenter : 0 ≤ center) :
    -4 - (15 / 8 : ℝ) * center ≤
      suzukiChebyshevArchimedeanLowerOrder center := by
  have hgap :
      0 ≤ suzukiHurwitzLerchTwo 1 -
        Real.exp (-center / 2) *
          suzukiHurwitzLerchTwo (Real.exp (-2 * center)) := by
    rw [suzukiHurwitzLerchTwo_sub_damped_eq_tsum_gap hcenter]
    exact tsum_nonneg fun n =>
      suzukiPointwiseLerchGapSummand_nonnegative hcenter n
  have hlinear :=
    neg_fifteen_eighths_lt_archimedeanLinearCoefficient
  have hexponential := Real.exp_pos (-center / 2)
  unfold suzukiChebyshevArchimedeanLowerOrder
  nlinarith

private theorem suzukiHurwitzLerchTwo_nonnegative
    {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ suzukiHurwitzLerchTwo q := by
  unfold suzukiHurwitzLerchTwo
  exact tsum_nonneg fun n => by
    unfold suzukiHurwitzLerchTwoSummand
    positivity

/-- A two-sided envelope for the source-exact lower-order term.  Its only
unbounded contribution is linear in the center. -/
theorem abs_suzukiChebyshevArchimedeanLowerOrder_le
    {center : ℝ} (hcenter : 0 ≤ center) :
    |suzukiChebyshevArchimedeanLowerOrder center| ≤
      4 + center *
          |((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1| +
        1 / 4 * suzukiHurwitzLerchTwo 1 := by
  let coefficient : ℝ :=
    ((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1
  let gap : ℝ :=
    suzukiHurwitzLerchTwo 1 -
      Real.exp (-center / 2) *
        suzukiHurwitzLerchTwo (Real.exp (-2 * center))
  have hgapNonneg : 0 ≤ gap := by
    dsimp only [gap]
    rw [suzukiHurwitzLerchTwo_sub_damped_eq_tsum_gap hcenter]
    exact tsum_nonneg fun n =>
      suzukiPointwiseLerchGapSummand_nonnegative hcenter n
  have hmovingNonneg :
      0 ≤ Real.exp (-center / 2) *
        suzukiHurwitzLerchTwo (Real.exp (-2 * center)) :=
    mul_nonneg (Real.exp_pos _).le
      (suzukiHurwitzLerchTwo_nonnegative (Real.exp_pos _).le)
  have hgapUpper : gap ≤ suzukiHurwitzLerchTwo 1 := by
    dsimp only [gap]
    linarith
  have hdecay : Real.exp (-center / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hexponentialAbs :
      |4 * Real.exp (-center / 2) - 4| ≤ 4 := by
    have hexponentialPos := Real.exp_pos (-center / 2)
    rw [abs_of_nonpos (by nlinarith)]
    nlinarith
  have hlinearAbs : |center * coefficient| = center * |coefficient| := by
    rw [abs_mul, abs_of_nonneg hcenter]
  have hgapAbs : |(1 / 4 : ℝ) * gap| ≤
      1 / 4 * suzukiHurwitzLerchTwo 1 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num) hgapNonneg)]
    exact mul_le_mul_of_nonneg_left hgapUpper (by norm_num)
  unfold suzukiChebyshevArchimedeanLowerOrder
  change |(4 * Real.exp (-center / 2) - 4) +
      center * coefficient + (1 / 4 : ℝ) * gap| ≤ _
  calc
    |(4 * Real.exp (-center / 2) - 4) +
        center * coefficient + (1 / 4 : ℝ) * gap| ≤
        |4 * Real.exp (-center / 2) - 4| +
          |center * coefficient| + |(1 / 4 : ℝ) * gap| := by
      calc
        |(4 * Real.exp (-center / 2) - 4) +
            center * coefficient + (1 / 4 : ℝ) * gap| ≤
            |(4 * Real.exp (-center / 2) - 4) +
              center * coefficient| + |(1 / 4 : ℝ) * gap| :=
          abs_add_le _ _
        _ ≤ (|4 * Real.exp (-center / 2) - 4| +
              |center * coefficient|) + |(1 / 4 : ℝ) * gap| :=
          by
            have habs := abs_add_le
              (4 * Real.exp (-center / 2) - 4)
              (center * coefficient)
            linarith
    _ ≤ 4 + center * |coefficient| +
          1 / 4 * suzukiHurwitzLerchTwo 1 := by
      rw [hlinearAbs]
      exact add_le_add (add_le_add hexponentialAbs le_rfl) hgapAbs
    _ = 4 + center *
          |((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1| +
        1 / 4 * suzukiHurwitzLerchTwo 1 := by rfl

/-! ## Canonical endpoints and the literal gap -/

/-- At every canonical center, the full smooth baseline is bounded below by
the nonnegative convex reserve minus an explicit logarithmic loss. -/
theorem
    suzukiChebyshevArchimedeanConvexReserve_sub_logLoss_le_canonicalBaseline
    (count : ℕ) :
    suzukiChebyshevArchimedeanConvexReserve
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) -
        (15 / 8 : ℝ) * Real.log (((count + 2 : ℕ) : ℝ)) -
        107 / 8 ≤
      suzukiChebyshevArchimedeanBaseline
        (suzukiFirstTailChebyshevCenter count)
        (((count + 2 : ℕ) : ℝ)) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  change suzukiChebyshevArchimedeanConvexReserve r b -
      (15 / 8 : ℝ) * Real.log b - 107 / 8 ≤
    suzukiChebyshevArchimedeanBaseline r b
  have hbpos : 0 < b := by
    dsimp only [b]
    exact_mod_cast (show 0 < count + 2 by omega)
  have hrbase : Real.log 2 ≤ r := by
    dsimp only [r]
    exact log_two_le_suzukiFirstTailChebyshevCenter count
  have hrnonneg : 0 ≤ r :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hrbase
  have hlowerOrder :=
    neg_four_sub_fifteen_eighths_mul_le_archimedeanLowerOrder hrnonneg
  have hcenter : r < Real.log b + 5 := by
    dsimp only [r, b]
    exact
      suzukiFirstTailChebyshevCenter_lt_log_endpoint_add_five count
  rw [suzukiChebyshevArchimedeanBaseline_eq_reserve_add_lowerOrder
    r hbpos]
  nlinarith

/-- The exact difference between the canonical smooth baseline and its
square-root convex reserve has an explicit logarithmic envelope. -/
theorem abs_canonicalBaseline_sub_convexReserve_le_logEnvelope
    (count : ℕ) :
    |suzukiChebyshevArchimedeanBaseline
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) -
        suzukiChebyshevArchimedeanConvexReserve
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ))| ≤
      4 + (Real.log (((count + 2 : ℕ) : ℝ)) + 5) *
          |((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1| +
        1 / 4 * suzukiHurwitzLerchTwo 1 := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  change |suzukiChebyshevArchimedeanBaseline r b -
      suzukiChebyshevArchimedeanConvexReserve r b| ≤
    4 + (Real.log b + 5) *
        |((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1| +
      1 / 4 * suzukiHurwitzLerchTwo 1
  have hbpos : 0 < b := by
    dsimp only [b]
    exact_mod_cast (show 0 < count + 2 by omega)
  have hrbase : Real.log 2 ≤ r := by
    dsimp only [r]
    exact log_two_le_suzukiFirstTailChebyshevCenter count
  have hrnonneg : 0 ≤ r :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hrbase
  have hlowerOrder :=
    abs_suzukiChebyshevArchimedeanLowerOrder_le hrnonneg
  have hcenter : r ≤ Real.log b + 5 := by
    dsimp only [r, b]
    exact
      (suzukiFirstTailChebyshevCenter_lt_log_endpoint_add_five count).le
  have hlinearEnvelope :
      r * |((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1| ≤
        (Real.log b + 5) *
          |((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1| :=
    mul_le_mul_of_nonneg_right hcenter (abs_nonneg _)
  rw [suzukiChebyshevArchimedeanBaseline_eq_reserve_add_lowerOrder
    r hbpos, add_sub_cancel_left]
  exact hlowerOrder.trans (by linarith)

/-- After square-root normalization, the canonical smooth baseline is
asymptotic to the extracted convex reserve.  All source-exact terms omitted
from the reserve vanish at this scale. -/
theorem
    tendsto_canonicalBaseline_sub_convexReserve_div_sqrt_endpoint_zero :
    Tendsto
      (fun count : ℕ =>
        (suzukiChebyshevArchimedeanBaseline
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ)) -
            suzukiChebyshevArchimedeanConvexReserve
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ))) /
          Real.sqrt (((count + 2 : ℕ) : ℝ)))
      atTop (nhds 0) := by
  let coefficient : ℝ :=
    |((Complex.digamma (1 / 4)).re - Real.log Real.pi) / 2 + 1|
  let constant : ℝ :=
    4 + 5 * coefficient + 1 / 4 * suzukiHurwitzLerchTwo 1
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
  have hlogInvSqrt :
      Tendsto
        (fun count : ℕ =>
          Real.log (endpoint count) *
            endpoint count ^ (-1 / 2 : ℝ))
        atTop (nhds 0) := by
    have hraw : Tendsto
        (fun x : ℝ => Real.log x / x ^ (1 / 2 : ℝ))
        atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop
        (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
    refine (hraw.comp hendpointTop).congr'
      (Eventually.of_forall fun count => ?_)
    simp only [Function.comp_apply]
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring_nf]
    rw [Real.rpow_neg (hendpointPos count).le]
    ring_nf
  have hmajor :
      Tendsto
        (fun count : ℕ =>
          constant * endpoint count ^ (-1 / 2 : ℝ) +
            coefficient *
              (Real.log (endpoint count) *
                endpoint count ^ (-1 / 2 : ℝ)))
        atTop (nhds 0) := by
    have hconstant :
        Tendsto
          (fun count : ℕ =>
            constant * endpoint count ^ (-1 / 2 : ℝ))
          atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hinvSqrt
    have hlogarithmic :
        Tendsto
          (fun count : ℕ => coefficient *
            (Real.log (endpoint count) *
              endpoint count ^ (-1 / 2 : ℝ)))
          atTop (nhds 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hlogInvSqrt
    simpa only [zero_add] using hconstant.add hlogarithmic
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun _count => norm_nonneg _
  · exact Eventually.of_forall fun count => by
      let b : ℝ := endpoint count
      let difference : ℝ :=
        suzukiChebyshevArchimedeanBaseline
            (suzukiFirstTailChebyshevCenter count) b -
          suzukiChebyshevArchimedeanConvexReserve
            (suzukiFirstTailChebyshevCenter count) b
      change ‖difference / Real.sqrt b‖ ≤
        constant * b ^ (-1 / 2 : ℝ) +
          coefficient * (Real.log b * b ^ (-1 / 2 : ℝ))
      have hbpos : 0 < b := by
        dsimp only [b]
        exact hendpointPos count
      have hsqrtPos : 0 < Real.sqrt b := Real.sqrt_pos.2 hbpos
      have hdifference :
          |difference| ≤
            4 + (Real.log b + 5) * coefficient +
              1 / 4 * suzukiHurwitzLerchTwo 1 := by
        dsimp only [difference, b, endpoint, coefficient]
        exact
          abs_canonicalBaseline_sub_convexReserve_le_logEnvelope count
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hsqrtPos]
      calc
        |difference| / Real.sqrt b ≤
            (4 + (Real.log b + 5) * coefficient +
              1 / 4 * suzukiHurwitzLerchTwo 1) /
                Real.sqrt b :=
          div_le_div_of_nonneg_right hdifference hsqrtPos.le
        _ = constant * b ^ (-1 / 2 : ℝ) +
              coefficient * (Real.log b * b ^ (-1 / 2 : ℝ)) := by
          rw [div_eq_mul_inv, Real.sqrt_eq_rpow,
            ← Real.rpow_neg hbpos.le]
          dsimp only [constant]
          ring_nf
  · exact hmajor

/-- The exact explicit frontier is the smooth baseline plus the complete
centered PNT remainder. -/
theorem
    suzukiFirstTailResetTransportGap_succ_eq_baseline_add_pntError
    (count : ℕ) :
    curvatureTransportGap
        (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
        (Real.log 2) suzukiSmoothCurvature
        (suzukiResetLocation (Real.log 2) 1)
        (suzukiResetWeight
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
        (suzukiResetTransportMassPoint (Real.log 2)
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
          (le_refl (Real.log 2))
          suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
        (count + 1) =
      suzukiChebyshevArchimedeanBaseline
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) +
        suzukiChebyshevCenteredPNTError
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) := by
  rw [
    suzukiFirstTailResetTransportGap_succ_eq_explicitMain_add_pntError]
  unfold suzukiChebyshevArchimedeanBaseline
  ring_nf

/-- Hence the literal canonical transport gap is bounded below by the
positive convex reserve, the centered arithmetic remainder, and only an
explicit logarithmic smooth loss. -/
theorem suzukiFirstTailConvexReserve_add_pntError_sub_logLoss_le_gap
    (count : ℕ) :
    suzukiChebyshevArchimedeanConvexReserve
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) +
        suzukiChebyshevCenteredPNTError
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) -
        (15 / 8 : ℝ) * Real.log (((count + 2 : ℕ) : ℝ)) -
        107 / 8 ≤
      curvatureTransportGap
        (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
        (Real.log 2) suzukiSmoothCurvature
        (suzukiResetLocation (Real.log 2) 1)
        (suzukiResetWeight
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
        (suzukiResetTransportMassPoint (Real.log 2)
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
          (le_refl (Real.log 2))
          suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
        (count + 1) := by
  rw [suzukiFirstTailResetTransportGap_succ_eq_baseline_add_pntError]
  have hbaseline :=
    suzukiChebyshevArchimedeanConvexReserve_sub_logLoss_le_canonicalBaseline
      count
  linarith

/-- At square-root scale, the literal canonical gap is exactly the convex
reserve plus the centered PNT remainder, up to a term tending to zero. -/
theorem
    tendsto_firstTailGap_sub_convexReserve_sub_pntError_div_sqrt_zero :
    Tendsto
      (fun count : ℕ =>
        (curvatureTransportGap
              (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
              (Real.log 2) suzukiSmoothCurvature
              (suzukiResetLocation (Real.log 2) 1)
              (suzukiResetWeight
                (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
              (suzukiResetTransportMassPoint (Real.log 2)
                (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
                (le_refl (Real.log 2))
                suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
              (count + 1) -
            suzukiChebyshevArchimedeanConvexReserve
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ)) -
            suzukiChebyshevCenteredPNTError
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ))) /
          Real.sqrt (((count + 2 : ℕ) : ℝ)))
      atTop (nhds 0) := by
  apply
    tendsto_canonicalBaseline_sub_convexReserve_div_sqrt_endpoint_zero.congr'
  exact Eventually.of_forall fun count => by
    simp only
    rw [suzukiFirstTailResetTransportGap_succ_eq_baseline_add_pntError]
    ring_nf

/-- Fully dimensionless asymptotic frontier: the normalized literal gap is
the normalized centered PNT remainder plus the explicit nonnegative
exponential defect, with an error tending to zero. -/
theorem
    tendsto_normalizedFirstTailGap_sub_exponentialDefect_sub_normalizedPNTError_zero :
    Tendsto
      (fun count : ℕ =>
        curvatureTransportGap
              (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
              (Real.log 2) suzukiSmoothCurvature
              (suzukiResetLocation (Real.log 2) 1)
              (suzukiResetWeight
                (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
              (suzukiResetTransportMassPoint (Real.log 2)
                (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
                (le_refl (Real.log 2))
                suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
              (count + 1) /
            Real.sqrt (((count + 2 : ℕ) : ℝ)) -
          4 *
            (Real.exp
                ((suzukiFirstTailChebyshevCenter count -
                    Real.log (((count + 2 : ℕ) : ℝ))) / 2) -
              1 -
              (suzukiFirstTailChebyshevCenter count -
                  Real.log (((count + 2 : ℕ) : ℝ))) / 2) -
          suzukiChebyshevCenteredPNTError
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ)) /
            Real.sqrt (((count + 2 : ℕ) : ℝ)))
      atTop (nhds 0) := by
  apply
    tendsto_firstTailGap_sub_convexReserve_sub_pntError_div_sqrt_zero.congr'
  exact Eventually.of_forall fun count => by
    let b : ℝ := ((count + 2 : ℕ) : ℝ)
    let r : ℝ := suzukiFirstTailChebyshevCenter count
    let gap : ℝ := curvatureTransportGap
      (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
      (Real.log 2) suzukiSmoothCurvature
      (suzukiResetLocation (Real.log 2) 1)
      (suzukiResetWeight
        (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
      (suzukiResetTransportMassPoint (Real.log 2)
        (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
        (le_refl (Real.log 2))
        suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
      (count + 1)
    let error : ℝ := suzukiChebyshevCenteredPNTError r b
    simp only
    change (gap - suzukiChebyshevArchimedeanConvexReserve r b - error) /
        Real.sqrt b =
      gap / Real.sqrt b -
        4 * (Real.exp ((r - Real.log b) / 2) - 1 -
          (r - Real.log b) / 2) -
        error / Real.sqrt b
    have hbpos : 0 < b := by
      dsimp only [b]
      exact_mod_cast (show 0 < count + 2 by omega)
    rw [← suzukiChebyshevArchimedeanConvexReserve_div_sqrt r hbpos]
    ring

end

end RiemannGaussian
