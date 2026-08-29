import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevCoupling

/-!
# Entropy dual of the canonical Suzuki center

The canonical Suzuki center is chosen by matching the Archimedean slope to
the weighted Chebyshev mass.  The preceding coupling theorem identifies its
displacement from the logarithmic endpoint with the arithmetic mass error.

This file performs the corresponding Legendre elimination.  The convex
reserve plus the centered PNT remainder becomes an endpoint-centered
Chebyshev error minus a nonnegative relative-entropy cost, up to one
source-exact smooth correction.  The correction vanishes at square-root
scale, leaving a center-eliminated asymptotic frontier.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## Endpoint statistic and entropy coordinate -/

/-- The mass--moment error centered at the logarithmic endpoint.  Unlike the
canonical centered PNT error, this statistic has no moving center. -/
def suzukiChebyshevEndpointCenteredError (b : ℝ) : ℝ :=
  suzukiChebyshevWeightedLogMomentError b -
    Real.log b * suzukiChebyshevWeightedMassError b

/-- The mass ratio after removing the source-exact lower-order slope.  At a
canonical Suzuki center it is exactly the exponential of half the center
displacement. -/
def suzukiChebyshevCorrectedMassRatio (center b : ℝ) : ℝ :=
  1 +
    (suzukiChebyshevWeightedMassError b -
        suzukiChebyshevArchimedeanSlopeLowerOrder center) /
      (2 * b ^ (1 / 2 : ℝ))

/-- Scalar relative entropy with reference ratio one. -/
def suzukiChebyshevRelativeEntropy (ratio : ℝ) : ℝ :=
  ratio * Real.log ratio - ratio + 1

/-- The complete source-exact term left after Legendre elimination of the
moving center. -/
def suzukiChebyshevLegendreLowerOrder (center ratio : ℝ) : ℝ :=
  suzukiChebyshevArchimedeanLowerOrder center -
    2 * Real.log ratio *
      suzukiChebyshevArchimedeanSlopeLowerOrder center

/-- The endpoint-centered error is the PNT remainder centered at `log b` on
every natural endpoint. -/
theorem suzukiChebyshevCenteredPNTError_log_endpoint_eq_endpointCenteredError
    (cutoff : ℕ) :
    suzukiChebyshevCenteredPNTError
        (Real.log (((cutoff + 1 : ℕ) : ℝ)))
        (((cutoff + 1 : ℕ) : ℝ)) =
      suzukiChebyshevEndpointCenteredError
        (((cutoff + 1 : ℕ) : ℝ)) := by
  rw [
    suzukiChebyshevCenteredPNTError_nat_eq_logMomentError_sub_center_mul_massError]
  rfl

/-- At a natural endpoint, the fixed-center error is exactly the direct
weighted von-Mangoldt endpoint sum plus its evaluated continuous offset. -/
theorem suzukiChebyshevEndpointCenteredError_nat_eq_sum_add_offset
    (cutoff : ℕ) :
    suzukiChebyshevEndpointCenteredError
        (((cutoff + 1 : ℕ) : ℝ)) =
      (∑ n ∈ Finset.Ioc 1 (cutoff + 1),
          suzukiChebyshevCenteredKernel
              (Real.log (((cutoff + 1 : ℕ) : ℝ))) n *
            ArithmeticFunction.vonMangoldt n) +
        4 * (((cutoff + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) -
        Real.log (((cutoff + 1 : ℕ) : ℝ)) - 4 := by
  have hmain :=
    suzukiChebyshevWeightedCenteredLogMoment_nat_eq_explicitMain_add_pntError
      (Real.log (((cutoff + 1 : ℕ) : ℝ))) cutoff
  rw [suzukiChebyshevWeightedCenteredLogMoment_nat_eq_sum,
    suzukiChebyshevCenteredPNTError_log_endpoint_eq_endpointCenteredError]
    at hmain
  ring_nf at hmain ⊢
  linarith

/-- Scalar relative entropy is nonnegative on nonnegative ratios. -/
theorem suzukiChebyshevRelativeEntropy_nonnegative
    {ratio : ℝ} (hratio : 0 ≤ ratio) :
    0 ≤ suzukiChebyshevRelativeEntropy ratio := by
  have hlog := Real.self_sub_one_le_mul_log hratio
  unfold suzukiChebyshevRelativeEntropy
  linarith

/-! ## Exact canonical Legendre elimination -/

/-- The corrected arithmetic mass ratio is exactly the exponential center
coordinate at every canonical first-tail endpoint. -/
theorem suzukiChebyshevCorrectedMassRatio_firstTail_eq_exp_displacement
    (count : ℕ) :
    suzukiChebyshevCorrectedMassRatio
        (suzukiFirstTailChebyshevCenter count)
        (((count + 2 : ℕ) : ℝ)) =
      Real.exp
        ((suzukiFirstTailChebyshevCenter count -
          Real.log (((count + 2 : ℕ) : ℝ))) / 2) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  have hbpos : 0 < b := by
    dsimp only [b]
    exact_mod_cast (show 0 < count + 2 by omega)
  have hmass :=
    suzukiChebyshevWeightedMassError_firstTail_eq_reserveGradient_add_lowerOrder
      count
  change suzukiChebyshevWeightedMassError b =
    2 * b ^ (1 / 2 : ℝ) *
        (Real.exp ((r - Real.log b) / 2) - 1) +
      suzukiChebyshevArchimedeanSlopeLowerOrder r at hmass
  change suzukiChebyshevCorrectedMassRatio r b =
    Real.exp ((r - Real.log b) / 2)
  unfold suzukiChebyshevCorrectedMassRatio
  rw [hmass]
  have hpower : b ^ (1 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hbpos _).ne'
  field_simp [hpower]
  ring

/-- Consequently the canonical corrected mass ratio is strictly positive. -/
theorem suzukiChebyshevCorrectedMassRatio_firstTail_pos (count : ℕ) :
    0 < suzukiChebyshevCorrectedMassRatio
      (suzukiFirstTailChebyshevCenter count)
      (((count + 2 : ℕ) : ℝ)) := by
  rw [suzukiChebyshevCorrectedMassRatio_firstTail_eq_exp_displacement]
  exact Real.exp_pos _

/-- The entropy cost at every canonical endpoint is nonnegative. -/
theorem suzukiChebyshevRelativeEntropy_correctedMassRatio_firstTail_nonnegative
    (count : ℕ) :
    0 ≤ suzukiChebyshevRelativeEntropy
      (suzukiChebyshevCorrectedMassRatio
        (suzukiFirstTailChebyshevCenter count)
        (((count + 2 : ℕ) : ℝ))) :=
  suzukiChebyshevRelativeEntropy_nonnegative
    (suzukiChebyshevCorrectedMassRatio_firstTail_pos count).le

/-- Exact Legendre identity at the canonical center.  The convex reserve and
centered PNT error equal the endpoint-centered arithmetic error minus the
nonnegative entropy cost and one source-exact smooth correction. -/
theorem
    suzukiFirstTailConvexReserve_add_pntError_eq_endpointError_sub_entropy_sub_correction
    (count : ℕ) :
    suzukiChebyshevArchimedeanConvexReserve
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) +
        suzukiChebyshevCenteredPNTError
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) =
      suzukiChebyshevEndpointCenteredError
          (((count + 2 : ℕ) : ℝ)) -
        4 * (((count + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          suzukiChebyshevRelativeEntropy
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ))) -
        2 * Real.log
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ))) *
          suzukiChebyshevArchimedeanSlopeLowerOrder
            (suzukiFirstTailChebyshevCenter count) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  let ratio : ℝ := suzukiChebyshevCorrectedMassRatio r b
  have hratio : ratio = Real.exp ((r - Real.log b) / 2) := by
    dsimp only [ratio, r, b]
    exact
      suzukiChebyshevCorrectedMassRatio_firstTail_eq_exp_displacement count
  have hlogRatio : Real.log ratio = (r - Real.log b) / 2 := by
    rw [hratio, Real.log_exp]
  have hcenter : r = Real.log b + 2 * Real.log ratio := by
    linarith
  have hmass :=
    suzukiChebyshevWeightedMassError_firstTail_eq_reserveGradient_add_lowerOrder
      count
  change suzukiChebyshevWeightedMassError b =
    2 * b ^ (1 / 2 : ℝ) *
        (Real.exp ((r - Real.log b) / 2) - 1) +
      suzukiChebyshevArchimedeanSlopeLowerOrder r at hmass
  rw [← hratio] at hmass
  have hpnt :=
    suzukiChebyshevCenteredPNTError_firstTail_eq_coupledErrors count
  change suzukiChebyshevCenteredPNTError r b =
    suzukiChebyshevWeightedLogMomentError b -
      r * suzukiChebyshevWeightedMassError b at hpnt
  change
    suzukiChebyshevArchimedeanConvexReserve r b +
        suzukiChebyshevCenteredPNTError r b =
      suzukiChebyshevEndpointCenteredError b -
        4 * b ^ (1 / 2 : ℝ) *
          suzukiChebyshevRelativeEntropy ratio -
        2 * Real.log ratio *
          suzukiChebyshevArchimedeanSlopeLowerOrder r
  rw [hpnt]
  unfold suzukiChebyshevArchimedeanConvexReserve
    suzukiChebyshevEndpointCenteredError
    suzukiChebyshevRelativeEntropy
  rw [← hratio, hmass, hcenter]
  ring

/-- Exact finite-prefix gap after eliminating the canonical center from the
leading Legendre pair.  The only smooth residue is the displayed
source-exact lower-order term. -/
theorem suzukiFirstTailResetTransportGap_succ_eq_endpointError_sub_entropy_add_lowerOrder
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
      suzukiChebyshevEndpointCenteredError
          (((count + 2 : ℕ) : ℝ)) -
        4 * (((count + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          suzukiChebyshevRelativeEntropy
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ))) +
        suzukiChebyshevLegendreLowerOrder
          (suzukiFirstTailChebyshevCenter count)
          (suzukiChebyshevCorrectedMassRatio
            (suzukiFirstTailChebyshevCenter count)
            (((count + 2 : ℕ) : ℝ))) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  let ratio : ℝ := suzukiChebyshevCorrectedMassRatio r b
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
  have hbpos : 0 < b := by
    dsimp only [b]
    exact_mod_cast (show 0 < count + 2 by omega)
  change gap =
    suzukiChebyshevEndpointCenteredError b -
      4 * b ^ (1 / 2 : ℝ) *
        suzukiChebyshevRelativeEntropy ratio +
      suzukiChebyshevLegendreLowerOrder r ratio
  calc
    gap = suzukiChebyshevArchimedeanBaseline r b +
        suzukiChebyshevCenteredPNTError r b := by
      dsimp only [gap, r, b]
      exact
        suzukiFirstTailResetTransportGap_succ_eq_baseline_add_pntError
          count
    _ = (suzukiChebyshevArchimedeanConvexReserve r b +
          suzukiChebyshevCenteredPNTError r b) +
        suzukiChebyshevArchimedeanLowerOrder r := by
      rw [
        suzukiChebyshevArchimedeanBaseline_eq_reserve_add_lowerOrder r hbpos]
      ring
    _ = suzukiChebyshevEndpointCenteredError b -
          4 * b ^ (1 / 2 : ℝ) *
            suzukiChebyshevRelativeEntropy ratio +
          suzukiChebyshevLegendreLowerOrder r ratio := by
      have hidentity :=
        suzukiFirstTailConvexReserve_add_pntError_eq_endpointError_sub_entropy_sub_correction
          count
      change
        suzukiChebyshevArchimedeanConvexReserve r b +
            suzukiChebyshevCenteredPNTError r b =
          suzukiChebyshevEndpointCenteredError b -
            4 * b ^ (1 / 2 : ℝ) *
              suzukiChebyshevRelativeEntropy ratio -
            2 * Real.log ratio *
              suzukiChebyshevArchimedeanSlopeLowerOrder r at hidentity
      unfold suzukiChebyshevLegendreLowerOrder
      rw [hidentity]
      ring

/-- Exact scalar obstruction at each canonical prefix: positivity of the
literal gap is equivalent to the endpoint-centered arithmetic error plus its
smooth correction dominating the nonnegative entropy cost. -/
theorem suzukiFirstTailResetTransportGap_succ_nonnegative_iff_entropy_le
    (count : ℕ) :
    0 ≤ curvatureTransportGap
        (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
        (Real.log 2) suzukiSmoothCurvature
        (suzukiResetLocation (Real.log 2) 1)
        (suzukiResetWeight
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
        (suzukiResetTransportMassPoint (Real.log 2)
          (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
          (le_refl (Real.log 2))
          suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
        (count + 1) ↔
      4 * (((count + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          suzukiChebyshevRelativeEntropy
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ))) ≤
        suzukiChebyshevEndpointCenteredError
            (((count + 2 : ℕ) : ℝ)) +
          suzukiChebyshevLegendreLowerOrder
            (suzukiFirstTailChebyshevCenter count)
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ))) := by
  rw [
    suzukiFirstTailResetTransportGap_succ_eq_endpointError_sub_entropy_add_lowerOrder]
  constructor <;> intro h <;> linarith

/-! ## Square-root entropy frontier -/

/-- The canonical center displacement is uniformly bounded in absolute value
by five logarithmic units. -/
theorem abs_suzukiFirstTailChebyshevCenter_sub_log_endpoint_le_five
    (count : ℕ) :
    |suzukiFirstTailChebyshevCenter count -
        Real.log (((count + 2 : ℕ) : ℝ))| ≤ 5 := by
  rw [abs_le]
  constructor
  · have hlower :=
      log_endpoint_sub_two_le_suzukiFirstTailChebyshevCenter count
    linarith
  · have hupper :=
      suzukiFirstTailChebyshevCenter_lt_log_endpoint_add_five count
    linarith

/-- The source-exact correction left by Legendre elimination vanishes after
normalization by the square root of the endpoint. -/
theorem tendsto_entropyCorrection_firstTail_div_sqrt_endpoint_zero :
    Tendsto
      (fun count : ℕ =>
        2 * Real.log
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ))) *
          suzukiChebyshevArchimedeanSlopeLowerOrder
            (suzukiFirstTailChebyshevCenter count) /
          Real.sqrt (((count + 2 : ℕ) : ℝ)))
      atTop (nhds 0) := by
  let displacement : ℕ → ℝ := fun count =>
    suzukiFirstTailChebyshevCenter count -
      Real.log (((count + 2 : ℕ) : ℝ))
  let normalizedSlope : ℕ → ℝ := fun count =>
    suzukiChebyshevArchimedeanSlopeLowerOrder
        (suzukiFirstTailChebyshevCenter count) /
      Real.sqrt (((count + 2 : ℕ) : ℝ))
  have hdisplacementBound :
      IsBoundedUnder (· ≤ ·) atTop (norm ∘ displacement) := by
    apply isBoundedUnder_of_eventually_le (a := (5 : ℝ))
    exact Eventually.of_forall fun count => by
      change ‖suzukiFirstTailChebyshevCenter count -
        Real.log (((count + 2 : ℕ) : ℝ))‖ ≤ 5
      rw [Real.norm_eq_abs]
      exact
        abs_suzukiFirstTailChebyshevCenter_sub_log_endpoint_le_five count
  have hnormalizedSlope : Tendsto normalizedSlope atTop (nhds 0) := by
    exact
      tendsto_archimedeanSlopeLowerOrder_firstTail_div_sqrt_endpoint_zero
  have hproduct :
      Tendsto
        (fun count : ℕ => displacement count * normalizedSlope count)
        atTop (nhds 0) :=
    Filter.isBoundedUnder_le_mul_tendsto_zero
      hdisplacementBound hnormalizedSlope
  apply hproduct.congr'
  exact Eventually.of_forall fun count => by
    dsimp only [displacement, normalizedSlope]
    rw [
      suzukiChebyshevCorrectedMassRatio_firstTail_eq_exp_displacement,
      Real.log_exp]
    ring

/-- The complete source-exact Legendre correction in the finite gap identity
is little-o of the endpoint square root. -/
theorem tendsto_legendreLowerOrder_firstTail_div_sqrt_endpoint_zero :
    Tendsto
      (fun count : ℕ =>
        suzukiChebyshevLegendreLowerOrder
            (suzukiFirstTailChebyshevCenter count)
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ))) /
          Real.sqrt (((count + 2 : ℕ) : ℝ)))
      atTop (nhds 0) := by
  have hlowerOrder :
      Tendsto
        (fun count : ℕ =>
          suzukiChebyshevArchimedeanLowerOrder
              (suzukiFirstTailChebyshevCenter count) /
            Real.sqrt (((count + 2 : ℕ) : ℝ)))
        atTop (nhds 0) := by
    apply
      tendsto_canonicalBaseline_sub_convexReserve_div_sqrt_endpoint_zero.congr'
    exact Eventually.of_forall fun count => by
      simp only
      have hbpos : 0 < (((count + 2 : ℕ) : ℝ)) := by
        exact_mod_cast (show 0 < count + 2 by omega)
      rw [
        suzukiChebyshevArchimedeanBaseline_eq_reserve_add_lowerOrder
          (suzukiFirstTailChebyshevCenter count) hbpos]
      ring
  have hcombined :=
    hlowerOrder.sub
      tendsto_entropyCorrection_firstTail_div_sqrt_endpoint_zero
  have htarget :
      Tendsto
        (fun count : ℕ =>
          suzukiChebyshevLegendreLowerOrder
              (suzukiFirstTailChebyshevCenter count)
              (suzukiChebyshevCorrectedMassRatio
                (suzukiFirstTailChebyshevCenter count)
                (((count + 2 : ℕ) : ℝ))) /
            Real.sqrt (((count + 2 : ℕ) : ℝ)))
        atTop (nhds (0 - 0)) := by
    apply hcombined.congr'
    exact Eventually.of_forall fun count => by
      unfold suzukiChebyshevLegendreLowerOrder
      ring
  simpa only [sub_zero] using htarget

/-- Pointwise center elimination at square-root scale.  The normalized gap
minus the endpoint-centered arithmetic error plus the entropy cost is exactly
the already controlled smooth remainder minus the vanishing correction. -/
theorem
    normalizedFirstTailGap_sub_endpointError_add_entropy_eq_remainder_sub_correction
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
            (count + 1) /
          Real.sqrt (((count + 2 : ℕ) : ℝ)) -
        suzukiChebyshevEndpointCenteredError
            (((count + 2 : ℕ) : ℝ)) /
          Real.sqrt (((count + 2 : ℕ) : ℝ)) +
        4 * suzukiChebyshevRelativeEntropy
          (suzukiChebyshevCorrectedMassRatio
            (suzukiFirstTailChebyshevCenter count)
            (((count + 2 : ℕ) : ℝ))) =
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
          Real.sqrt (((count + 2 : ℕ) : ℝ)) -
        2 * Real.log
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ))) *
          suzukiChebyshevArchimedeanSlopeLowerOrder
            (suzukiFirstTailChebyshevCenter count) /
          Real.sqrt (((count + 2 : ℕ) : ℝ)) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  let ratio : ℝ := suzukiChebyshevCorrectedMassRatio r b
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
  have hidentity :=
    suzukiFirstTailConvexReserve_add_pntError_eq_endpointError_sub_entropy_sub_correction
      count
  change
    suzukiChebyshevArchimedeanConvexReserve r b +
        suzukiChebyshevCenteredPNTError r b =
      suzukiChebyshevEndpointCenteredError b -
        4 * b ^ (1 / 2 : ℝ) *
          suzukiChebyshevRelativeEntropy ratio -
        2 * Real.log ratio *
          suzukiChebyshevArchimedeanSlopeLowerOrder r at hidentity
  have hsolved :
      suzukiChebyshevEndpointCenteredError b =
        suzukiChebyshevArchimedeanConvexReserve r b +
          suzukiChebyshevCenteredPNTError r b +
          4 * b ^ (1 / 2 : ℝ) *
            suzukiChebyshevRelativeEntropy ratio +
          2 * Real.log ratio *
            suzukiChebyshevArchimedeanSlopeLowerOrder r := by
    linarith
  change
    gap / Real.sqrt b -
          suzukiChebyshevEndpointCenteredError b / Real.sqrt b +
        4 * suzukiChebyshevRelativeEntropy ratio =
      (gap - suzukiChebyshevArchimedeanConvexReserve r b -
          suzukiChebyshevCenteredPNTError r b) / Real.sqrt b -
        2 * Real.log ratio *
          suzukiChebyshevArchimedeanSlopeLowerOrder r / Real.sqrt b
  have hbpos : 0 < b := by
    dsimp only [b]
    exact_mod_cast (show 0 < count + 2 by omega)
  have hpower : b ^ (1 / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hbpos _).ne'
  rw [Real.sqrt_eq_rpow, hsolved]
  field_simp [hpower]
  ring

/-- Center-eliminated dimensionless frontier.  The normalized literal gap is
the endpoint-centered Chebyshev error minus a verified nonnegative entropy
cost, up to a term tending to zero. -/
theorem
    tendsto_normalizedFirstTailGap_sub_endpointError_add_entropy_zero :
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
          suzukiChebyshevEndpointCenteredError
              (((count + 2 : ℕ) : ℝ)) /
            Real.sqrt (((count + 2 : ℕ) : ℝ)) +
          4 * suzukiChebyshevRelativeEntropy
            (suzukiChebyshevCorrectedMassRatio
              (suzukiFirstTailChebyshevCenter count)
              (((count + 2 : ℕ) : ℝ))))
      atTop (nhds 0) := by
  have hremainders :=
    tendsto_firstTailGap_sub_convexReserve_sub_pntError_div_sqrt_zero.sub
      tendsto_entropyCorrection_firstTail_div_sqrt_endpoint_zero
  have htarget :
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
            suzukiChebyshevEndpointCenteredError
                (((count + 2 : ℕ) : ℝ)) /
              Real.sqrt (((count + 2 : ℕ) : ℝ)) +
            4 * suzukiChebyshevRelativeEntropy
              (suzukiChebyshevCorrectedMassRatio
                (suzukiFirstTailChebyshevCenter count)
                (((count + 2 : ℕ) : ℝ))))
        atTop (nhds (0 - 0)) := by
    apply hremainders.congr'
    exact Eventually.of_forall fun count =>
      (normalizedFirstTailGap_sub_endpointError_add_entropy_eq_remainder_sub_correction
        count).symm
  simpa only [sub_zero] using htarget

end

end RiemannGaussian
