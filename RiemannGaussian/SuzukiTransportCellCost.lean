import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevEntropy
import RiemannGaussian.EtaCurrentEndpointSeries

/-!
# Summable nonlinear costs in the actual Suzuki transport recurrence

Adding a prime-power atom changes the canonical gap by its signed work at
the old center minus the positive first moment of the new transport cell.
This file retains that exact recurrence and bounds the actual cell cost by
`2 * log(count + 3)^2 / (count + 1)^(3/2)`, with no zero hypothesis.

The proof combines the existing center localization and exponential
curvature lower bound with a sharp elementary transport-cell inequality.
The logarithmic summability estimate developed for the eta endpoint then
proves that these nonlinear costs have finite total. Every later finite
band has a uniform error bounded by the corresponding convergent tail.

The signed linear work is retained exactly. Its required lower bound is
not proved here, and summability of the local costs does not establish
the global endpoint entropy inequality or any zero exclusion.
-/

open Filter MeasureTheory
open scoped BigOperators Topology

namespace RiemannGaussian
noncomputable section

private theorem cell_cost_bound {f : ℝ → ℝ} {a b c w : ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hf : ContinuousOn f (Set.Icc a b))
    (hlower : ∀ s ∈ Set.Icc a b, c ≤ f s)
    (hmass : (∫ s in a..b, f s) = w) :
    0 ≤ (∫ s in a..b, (s - a) * f s) ∧
      (∫ s in a..b, (s - a) * f s) ≤ w ^ 2 / (2 * c) := by
  have hleft : ContinuousOn (fun s : ℝ => (s - a) * f s) (Set.Icc a b) :=
    (continuousOn_id.sub continuousOn_const).mul hf
  have hright : ContinuousOn (fun s : ℝ => (b - s) * f s) (Set.Icc a b) :=
    (continuousOn_const.sub continuousOn_id).mul hf
  have hlinear : ContinuousOn (fun s : ℝ => (b - s) * c) (Set.Icc a b) := by
    fun_prop
  have hsplit : (∫ s in a..b, (s - a) * f s) +
      (∫ s in a..b, (b - s) * f s) = (b - a) * w := by
    rw [← intervalIntegral.integral_add (hleft.intervalIntegrable_of_Icc hab)
      (hright.intervalIntegrable_of_Icc hab)]
    calc
      _ = ∫ s in a..b, (b - a) * f s := by
        apply intervalIntegral.integral_congr
        intro s hs
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul, hmass]
  have htri : (∫ s in a..b, (b - s) * c) = c * (b - a) ^ 2 / 2 := by
    have hid : IntervalIntegrable (fun s : ℝ => s) volume a b :=
      continuous_id.intervalIntegrable a b
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub intervalIntegrable_const hid,
      intervalIntegral.integral_const, integral_id]
    simp only [smul_eq_mul]
    ring
  have hrightLower : c * (b - a) ^ 2 / 2 ≤
      ∫ s in a..b, (b - s) * f s := by
    rw [← htri]
    apply intervalIntegral.integral_mono_on hab
      (hlinear.intervalIntegrable_of_Icc hab) (hright.intervalIntegrable_of_Icc hab)
    intro s hs
    exact mul_le_mul_of_nonneg_left (hlower s hs) (sub_nonneg.mpr hs.2)
  constructor
  · apply intervalIntegral.integral_nonneg hab
    intro s hs
    exact mul_nonneg (sub_nonneg.mpr hs.1) (hc.le.trans (hlower s hs))
  · apply (le_div_iff₀ (by positivity : 0 < 2 * c)).2
    have hquad : 0 ≤ (w - c * (b - a)) ^ 2 := sq_nonneg _
    have hscaled := mul_le_mul_of_nonneg_left hrightLower hc.le
    nlinarith

/-- Short notation for the unchanged canonical gap of the complete prefix
ending at `count + 2`, including its original reset data. -/
abbrev suzukiFirstTailCanonicalGap (count : ℕ) : ℝ :=
  curvatureTransportGap
    (suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
    (Real.log 2) suzukiSmoothCurvature
    (suzukiResetLocation (Real.log 2) 1)
    (suzukiResetWeight (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) 1)
    (suzukiResetTransportMassPoint (Real.log 2)
      (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
      (le_refl (Real.log 2))
      suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
    (count + 1)

/-- Positive displacement moment of the actual smooth-mass cell added by
the next integer. It vanishes whenever that integer has zero weight. -/
def suzukiFirstTailTransportCellCost (count : ℕ) : ℝ :=
  ∫ s in suzukiFirstTailChebyshevCenter count..
      suzukiFirstTailChebyshevCenter (count + 1),
    (s - suzukiFirstTailChebyshevCenter count) * suzukiSmoothCurvature s

/-- Signed work of the actual next prime-power atom, evaluated at the old
canonical center. No sign or absolute-value replacement is made. -/
def suzukiFirstTailTransportLinearWork (count : ℕ) : ℝ :=
  suzukiPrimeWeight (count + 1) *
    (suzukiPrimeLocation (count + 1) - suzukiFirstTailChebyshevCenter count)

private theorem curvatureContinuous :
    ContinuousOn suzukiSmoothCurvature (Set.Ici (Real.log 2)) :=
  continuousOn_suzukiSmoothCurvature_Ioi.mono (by
    intro s hs
    exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).trans_le hs)

/-- Nonnegative von-Mangoldt weights move the canonical centers monotonically. -/
theorem suzukiFirstTailChebyshevCenter_le_succ (count : ℕ) :
    suzukiFirstTailChebyshevCenter count ≤ suzukiFirstTailChebyshevCenter (count + 1) := by
  by_contra h
  have hstrict := (strictlyMonoOn_suzukiTransportCurvatureMass (le_refl (Real.log 2)))
    (log_two_le_suzukiFirstTailChebyshevCenter (count + 1))
    (log_two_le_suzukiFirstTailChebyshevCenter count) (lt_of_not_ge h)
  unfold suzukiFirstTailChebyshevCenter at hstrict
  rw [suzukiResetTransportMassPoint_mass_eq,
    suzukiResetTransportMassPoint_mass_eq, screwPrefixMass_succ] at hstrict
  have hn := suzukiResetWeight_nonnegative
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1 (count + 1)
  linarith

/-- The mass of each actual canonical cell equals the next arithmetic atom. -/
theorem integral_suzukiSmoothCurvature_firstTailCell (count : ℕ) :
    (∫ s in suzukiFirstTailChebyshevCenter count..
        suzukiFirstTailChebyshevCenter (count + 1), suzukiSmoothCurvature s) =
      suzukiPrimeWeight (count + 1) := by
  have h := integral_curvature_transportCell_eq_weight curvatureContinuous
    (base_le_suzukiResetTransportMassPoint (Real.log 2)
      (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) (le_refl (Real.log 2))
      suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
    (suzukiResetTransportMassPoint_mass_eq (Real.log 2)
      (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) (le_refl (Real.log 2))
      suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1) (count + 1)
  simpa only [suzukiFirstTailChebyshevCenter, suzukiResetWeight_succ] using h

/-- Exact gap recurrence: signed arithmetic work minus the complete cell cost. -/
theorem suzukiFirstTailCanonicalGap_succ (count : ℕ) :
    suzukiFirstTailCanonicalGap (count + 1) = suzukiFirstTailCanonicalGap count +
      suzukiFirstTailTransportLinearWork count - suzukiFirstTailTransportCellCost count := by
  have h := curvatureTransportGap_succ (baseValue :=
      suzukiPointwiseFrozenBaseValue (Real.log 2) 1)
    (location := suzukiResetLocation (Real.log 2) 1) curvatureContinuous
    (base_le_suzukiResetTransportMassPoint (Real.log 2)
      (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) (le_refl (Real.log 2))
      suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1)
    (suzukiResetTransportMassPoint_mass_eq (Real.log 2)
      (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) (le_refl (Real.log 2))
      suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1) (count + 1)
  change suzukiFirstTailCanonicalGap (count + 1) = suzukiFirstTailCanonicalGap count + _ at h
  rw [h]
  have hab := suzukiFirstTailChebyshevCenter_le_succ count
  have hc : ContinuousOn suzukiSmoothCurvature
      (Set.Icc (suzukiFirstTailChebyshevCenter count)
        (suzukiFirstTailChebyshevCenter (count + 1))) :=
    curvatureContinuous.mono (by
      intro s hs
      exact (log_two_le_suzukiFirstTailChebyshevCenter count).trans hs.1)
  have hi : IntervalIntegrable suzukiSmoothCurvature volume
      (suzukiFirstTailChebyshevCenter count) (suzukiFirstTailChebyshevCenter (count + 1)) :=
    hc.intervalIntegrable_of_Icc hab
  have hcost : IntervalIntegrable
      (fun s : ℝ => (s - suzukiFirstTailChebyshevCenter count) * suzukiSmoothCurvature s) volume
      (suzukiFirstTailChebyshevCenter count) (suzukiFirstTailChebyshevCenter (count + 1)) :=
    ((continuousOn_id.sub continuousOn_const).mul hc).intervalIntegrable_of_Icc hab
  have he : curvatureTransportCellSurplus suzukiSmoothCurvature
      (suzukiResetLocation (Real.log 2) 1)
      (suzukiResetTransportMassPoint (Real.log 2)
        (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1) (le_refl (Real.log 2))
        suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1) (count + 1) =
      suzukiFirstTailTransportLinearWork count - suzukiFirstTailTransportCellCost count := by
    change (∫ s in suzukiFirstTailChebyshevCenter count..
        suzukiFirstTailChebyshevCenter (count + 1),
        (suzukiPrimeLocation (count + 1) - s) * suzukiSmoothCurvature s) = _
    calc
      _ = ∫ s in suzukiFirstTailChebyshevCenter count..
          suzukiFirstTailChebyshevCenter (count + 1),
          (suzukiPrimeLocation (count + 1) - suzukiFirstTailChebyshevCenter count) *
              suzukiSmoothCurvature s -
            (s - suzukiFirstTailChebyshevCenter count) * suzukiSmoothCurvature s := by
        apply intervalIntegral.integral_congr
        intro s hs
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (hi.const_mul _) hcost,
          intervalIntegral.integral_const_mul, integral_suzukiSmoothCurvature_firstTailCell]
        unfold suzukiFirstTailTransportLinearWork suzukiFirstTailTransportCellCost
        ring
  rw [he]
  ring

/-- The established logarithmic center localization supplies a curvature
lower bound at square-root scale throughout every later transport cell. -/
theorem quarter_sqrt_le_suzukiSmoothCurvature_after_firstTailCenter
    (count : ℕ) {s : ℝ} (hs : suzukiFirstTailChebyshevCenter count ≤ s) :
    Real.sqrt (count + 1 : ℝ) / 4 ≤ suzukiSmoothCurvature s := by
  have hr := log_endpoint_sub_two_le_suzukiFirstTailChebyshevCenter count
  have hbase := (log_two_le_suzukiFirstTailChebyshevCenter count).trans hs
  have hexp : Real.exp (Real.log ((count + 2 : ℕ) : ℝ) / 2 - 1) ≤ Real.exp (s / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_sub, Real.exp_half, Real.exp_log (by positivity), div_eq_mul_inv,
    ← Real.exp_neg] at hexp
  have he : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
    linarith [Real.exp_neg_one_gt_d9]
  have hm := mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg ((count + 2 : ℕ) : ℝ))
  have hsqrt : Real.sqrt (count + 1 : ℝ) ≤ Real.sqrt ((count + 2 : ℕ) : ℝ) :=
    Real.sqrt_le_sqrt (by push_cast; linarith)
  have hc := five_sixths_exp_half_le_suzukiSmoothCurvature_of_logTwo_le hbase
  nlinarith [Real.sqrt_nonneg (count + 1 : ℝ)]

/-- The actual cell cost is nonnegative and at most twice the squared
arithmetic weight divided by the old endpoint square root. -/
theorem suzukiFirstTailTransportCellCost_bounds (count : ℕ) :
    0 ≤ suzukiFirstTailTransportCellCost count ∧
      suzukiFirstTailTransportCellCost count ≤
        2 * suzukiPrimeWeight (count + 1) ^ 2 / Real.sqrt (count + 1 : ℝ) := by
  have h := cell_cost_bound (suzukiFirstTailChebyshevCenter_le_succ count)
    (show 0 < Real.sqrt (count + 1 : ℝ) / 4 by positivity)
    (curvatureContinuous.mono (by
      intro s hs
      exact (log_two_le_suzukiFirstTailChebyshevCenter count).trans hs.1))
    (fun s hs => quarter_sqrt_le_suzukiSmoothCurvature_after_firstTailCenter count hs.1)
    (integral_suzukiSmoothCurvature_firstTailCell count)
  change 0 ≤ suzukiFirstTailTransportCellCost count ∧
    suzukiFirstTailTransportCellCost count ≤
      suzukiPrimeWeight (count + 1) ^ 2 / (2 * (Real.sqrt (count + 1 : ℝ) / 4)) at h
  refine ⟨h.1, h.2.trans_eq ?_⟩
  ring

/-- A completely explicit, summable majorant for every canonical cell cost. -/
theorem suzukiFirstTailTransportCellCost_le_log_sq (count : ℕ) :
    suzukiFirstTailTransportCellCost count ≤
      2 * Real.log (count + 3 : ℝ) ^ 2 / (count + 1 : ℝ) ^ (3 / 2 : ℝ) := by
  have hweight : suzukiPrimeWeight (count + 1) ^ 2 ≤
      Real.log (count + 3 : ℝ) ^ 2 / (count + 1 : ℝ) := by
    have hn := ArithmeticFunction.vonMangoldt_nonneg (n := count + 3)
    have hl := ArithmeticFunction.vonMangoldt_le_log (n := count + 3)
    have hsq : ArithmeticFunction.vonMangoldt (count + 3) ^ 2 ≤
        Real.log (count + 3 : ℝ) ^ 2 := by
      push_cast at hl
      nlinarith
    have he : suzukiPrimeWeight (count + 1) ^ 2 =
        ArithmeticFunction.vonMangoldt (count + 3) ^ 2 / (count + 3 : ℝ) := by
      unfold suzukiPrimeWeight
      rw [div_pow, Real.sq_sqrt (by positivity)]
      norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      ring_nf
    rw [he]
    exact div_le_div₀ (sq_nonneg _) hsq (by positivity) (by linarith)
  calc
    suzukiFirstTailTransportCellCost count ≤
        2 * suzukiPrimeWeight (count + 1) ^ 2 / Real.sqrt (count + 1 : ℝ) :=
      (suzukiFirstTailTransportCellCost_bounds count).2
    _ ≤ 2 * (Real.log (count + 3 : ℝ) ^ 2 / (count + 1 : ℝ)) /
        Real.sqrt (count + 1 : ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hweight (by norm_num))
        (Real.sqrt_nonneg _)
    _ = 2 * Real.log (count + 3 : ℝ) ^ 2 / (count + 1 : ℝ) ^ (3 / 2 : ℝ) := by
      have hx : 0 < (count + 1 : ℝ) := by positivity
      have hp : (count + 1 : ℝ) * Real.sqrt (count + 1 : ℝ) =
          (count + 1 : ℝ) ^ (3 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        calc
          _ = (count + 1 : ℝ) ^ (1 : ℝ) * (count + 1 : ℝ) ^ (1 / 2 : ℝ) := by
            rw [Real.rpow_one]
          _ = (count + 1 : ℝ) ^ ((1 : ℝ) + 1 / 2) := (Real.rpow_add hx _ _).symm
          _ = _ := by norm_num
      rw [mul_div_assoc, div_div, hp]
      ring

/-- All nonlinear costs in the actual prime-event recurrence have finite total. -/
theorem summable_suzukiFirstTailTransportCellCost :
    Summable suzukiFirstTailTransportCellCost := by
  have hm := (summable_pairedEtaCurrent_logPower_div_rpow 2
    (show (1 : ℝ) < 3 / 2 by norm_num)).mul_left 2
  apply hm.of_nonneg_of_le (fun count => (suzukiFirstTailTransportCellCost_bounds count).1)
  intro count
  have hlog : Real.log (count + 3 : ℝ) ≤ 1 + pairedEtaLogTailCutoff (count + 2) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < count + 3)
      (show (count + 3 : ℝ) ≤ 2 * ((count + 2 : ℕ) : ℝ) + 1 by push_cast; linarith)
    unfold pairedEtaLogTailCutoff
    push_cast at h ⊢
    linarith
  have hlogNonneg : 0 ≤ Real.log (count + 3 : ℝ) :=
    Real.log_nonneg (by have hn : (0 : ℝ) ≤ count := Nat.cast_nonneg count; linarith)
  have hsq : Real.log (count + 3 : ℝ) ^ 2 ≤ (1 + pairedEtaLogTailCutoff (count + 2)) ^ 2 := by
    nlinarith
  calc
    _ ≤ 2 * Real.log (count + 3 : ℝ) ^ 2 / (count + 1 : ℝ) ^ (3 / 2 : ℝ) :=
      suzukiFirstTailTransportCellCost_le_log_sq count
    _ ≤ _ := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq (by positivity)) (by norm_num)

/-- Exact finite-band telescoping, retaining both the signed work and cost. -/
theorem suzukiFirstTailCanonicalGap_add_eq_signed_work_sub_cost
    (start count : ℕ) :
    suzukiFirstTailCanonicalGap (start + count) =
      suzukiFirstTailCanonicalGap start +
        (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork (start + n)) -
        ∑ n ∈ Finset.range count, suzukiFirstTailTransportCellCost (start + n) := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Nat.add_succ, suzukiFirstTailCanonicalGap_succ, ih,
      Finset.sum_range_succ, Finset.sum_range_succ]
    ring

/-- The original gap differs from cumulative signed linear work by a
quantity converging to the explicit negative total of the actual costs. -/
theorem suzukiFirstTailCanonicalGap_sub_linearWork_tendsto :
    Tendsto (fun count : ℕ => suzukiFirstTailCanonicalGap count -
      (suzukiFirstTailCanonicalGap 0 +
        ∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork n))
      atTop (𝓝 (-∑' n : ℕ, suzukiFirstTailTransportCellCost n)) := by
  have ht := summable_suzukiFirstTailTransportCellCost.hasSum.tendsto_sum_nat.neg
  apply ht.congr'
  filter_upwards [] with count
  have h := suzukiFirstTailCanonicalGap_add_eq_signed_work_sub_cost 0 count
  simp only [zero_add] at h
  linarith

/-- Every finite band's nonlinear cost is bounded by the same infinite
tail, independently of band length. -/
theorem suzukiFirstTailTransportCellCost_block_le_tail (start count : ℕ) :
    (∑ n ∈ Finset.range count, suzukiFirstTailTransportCellCost (start + n)) ≤
      ∑' n : ℕ, suzukiFirstTailTransportCellCost (start + n) := by
  have hs : Summable (fun n : ℕ => suzukiFirstTailTransportCellCost (start + n)) := by
    simpa only [Nat.add_comm] using
      (summable_nat_add_iff start).2 summable_suzukiFirstTailTransportCellCost
  exact hs.sum_le_tsum (Finset.range count)
    (fun n hn => (suzukiFirstTailTransportCellCost_bounds (start + n)).1)

/-- The error in replacing an actual gap change by its signed linear work
has a definite nonpositive sign and is bounded by the summable tail. -/
theorem suzukiFirstTailCanonicalGap_block_error_bounds (start count : ℕ) :
    -(∑' n : ℕ, suzukiFirstTailTransportCellCost (start + n)) ≤
      suzukiFirstTailCanonicalGap (start + count) - suzukiFirstTailCanonicalGap start -
        (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork (start + n)) ∧
    suzukiFirstTailCanonicalGap (start + count) - suzukiFirstTailCanonicalGap start -
        (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork (start + n)) ≤ 0 := by
  rw [suzukiFirstTailCanonicalGap_add_eq_signed_work_sub_cost]
  have hle := suzukiFirstTailTransportCellCost_block_le_tail start count
  have hnonneg : 0 ≤ ∑ n ∈ Finset.range count, suzukiFirstTailTransportCellCost (start + n) :=
    Finset.sum_nonneg (fun n hn => (suzukiFirstTailTransportCellCost_bounds (start + n)).1)
  constructor <;> linarith

/-- The common bound for all later finite bands tends to zero. -/
theorem suzukiFirstTailTransportCellCost_tail_tendsto_zero :
    Tendsto (fun start : ℕ => ∑' n : ℕ, suzukiFirstTailTransportCellCost (start + n))
      atTop (𝓝 0) := by
  simpa only [Nat.add_comm] using tendsto_sum_nat_add suzukiFirstTailTransportCellCost

/-- Uniform approximation of every sufficiently late finite-band gap
change by its unchanged signed prime work, with arbitrary positive accuracy. -/
theorem suzukiFirstTailCanonicalGap_block_error_uniformly_small
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ start : ℕ in atTop, ∀ count : ℕ,
      |suzukiFirstTailCanonicalGap (start + count) - suzukiFirstTailCanonicalGap start -
        (∑ n ∈ Finset.range count, suzukiFirstTailTransportLinearWork (start + n))| < ε := by
  have ht := suzukiFirstTailTransportCellCost_tail_tendsto_zero.eventually (gt_mem_nhds hε)
  filter_upwards [ht] with start hstart
  intro count
  have h := suzukiFirstTailCanonicalGap_block_error_bounds start count
  rw [abs_of_nonpos h.2]
  linarith

end
end RiemannGaussian
