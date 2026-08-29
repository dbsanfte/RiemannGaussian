import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevEnvelope

/-!
# Quantitative envelope for the cumulative Suzuki frontier

The exact cumulative-error reduction contains two arithmetic boundary terms
and one interior moment.  The preceding localization theorem controls the
center in every one of their kernels.  This file combines that control with
the elementary Chebyshev estimate to prove unconditional square-root-scale
envelopes for all three pieces and for the complete centered PNT remainder.

These estimates do not decide the sign of the remainder.  They isolate its
true scale without assuming a prime number theorem or differentiating the
Chebyshev step function.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## Elementary PNT-error envelopes -/

/-- On the full multiplicative range, the elementary Chebyshev bound traps
the pointwise PNT error in absolute value by `5x`. -/
theorem abs_chebyshevPsi_sub_self_le_five_mul_self_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    |Chebyshev.psi x - x| ≤ 5 * x := by
  have hxnonneg : 0 ≤ x := zero_le_one.trans hx
  have hpsiUpper := chebyshevPsi_le_six_mul_self_of_one_le hx
  have hpsiNonneg := Chebyshev.psi_nonneg x
  rw [abs_le]
  constructor <;> linarith

private theorem intervalIntegrable_chebyshevPNTError_envelope
    {b : ℝ} (hb : 1 ≤ b) :
    IntervalIntegrable (fun x : ℝ => Chebyshev.psi x - x)
      volume 1 b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb]
  have hone : IntegrableOn (fun _x : ℝ => (1 : ℝ))
      (Set.Icc 1 b) :=
    continuousOn_const.integrableOn_Icc
  have hpsi := integrableOn_mul_sum_Icc
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (a := (1 : ℝ)) (b := b) (m := 0) (by norm_num) hone
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at hpsi
  have hpsi' : IntegrableOn (fun x : ℝ => Chebyshev.psi x)
      (Set.Icc 1 b) := by
    simpa only [one_mul] using hpsi
  exact hpsi'.sub continuous_id.integrableOn_Icc

/-- The cumulative PNT error has the unconditional quadratic envelope
`(5/2) * (b^2 - 1)`. -/
theorem abs_suzukiChebyshevCumulativePNTError_le
    {b : ℝ} (hb : 1 ≤ b) :
    |suzukiChebyshevCumulativePNTError b| ≤
      (5 / 2 : ℝ) * (b ^ 2 - 1) := by
  have herror := intervalIntegrable_chebyshevPNTError_envelope hb
  have hmajor : IntervalIntegrable (fun x : ℝ => 5 * x)
      volume 1 b :=
    (continuous_const.mul continuous_id).intervalIntegrable 1 b
  have habsIntegral :
      |∫ x in (1 : ℝ)..b, (Chebyshev.psi x - x)| ≤
        ∫ x in (1 : ℝ)..b, |Chebyshev.psi x - x| :=
    intervalIntegral.abs_integral_le_integral_abs hb
  have hmono :
      (∫ x in (1 : ℝ)..b, |Chebyshev.psi x - x|) ≤
        ∫ x in (1 : ℝ)..b, 5 * x := by
    apply intervalIntegral.integral_mono_on hb herror.abs hmajor
    intro x hx
    exact abs_chebyshevPsi_sub_self_le_five_mul_self_of_one_le hx.1
  unfold suzukiChebyshevCumulativePNTError
  calc
    |∫ x in (1 : ℝ)..b, (Chebyshev.psi x - x)| ≤
        ∫ x in (1 : ℝ)..b, |Chebyshev.psi x - x| := habsIntegral
    _ ≤ ∫ x in (1 : ℝ)..b, 5 * x := hmono
    _ = (5 / 2 : ℝ) * (b ^ 2 - 1) := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring

/-! ## Canonical kernel envelopes -/

/-- At the canonical endpoint the first cumulative-error coefficient is at
most `(7/2) * endpoint^(-3/2)` in absolute value. -/
theorem abs_suzukiChebyshevCenteredPNTWeight_firstTailEndpoint_le
    (count : ℕ) :
    |suzukiChebyshevCenteredPNTWeight
        (suzukiFirstTailChebyshevCenter count)
        (((count + 2 : ℕ) : ℝ))| ≤
      (7 / 2 : ℝ) *
        (((count + 2 : ℕ) : ℝ) ^ (-3 / 2 : ℝ)) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  change |suzukiChebyshevCenteredPNTWeight r b| ≤
    (7 / 2 : ℝ) * b ^ (-3 / 2 : ℝ)
  have hb1 : 1 ≤ b := by
    dsimp only [b]
    exact_mod_cast (show 1 ≤ count + 2 by omega)
  have hbpos : 0 < b := zero_lt_one.trans_le hb1
  have hweightNonneg :
      0 ≤ suzukiChebyshevCenteredPNTWeight r b := by
    dsimp only [r, b]
    exact
      suzukiChebyshevCenteredPNTWeight_nonneg_on_firstTailPrefix
        count (by exact_mod_cast (show 1 ≤ count + 2 by omega)) le_rfl
  have hcenter : r < Real.log b + 5 := by
    dsimp only [r, b]
    exact
      suzukiFirstTailChebyshevCenter_lt_log_endpoint_add_five count
  rw [abs_of_nonneg hweightNonneg]
  unfold suzukiChebyshevCenteredPNTWeight
  calc
    b ^ (-3 / 2 : ℝ) * (1 - (Real.log b - r) / 2) ≤
        b ^ (-3 / 2 : ℝ) * (7 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith)
        (Real.rpow_nonneg hbpos.le _)
    _ = (7 / 2 : ℝ) * b ^ (-3 / 2 : ℝ) := by ring

/-- The positive cumulative weight has an explicit logarithmic upper
envelope on every canonical prefix. -/
theorem suzukiChebyshevCenteredCumulativeWeight_le_of_one_le
    (count : ℕ) {x : ℝ} (hxone : 1 ≤ x) :
    suzukiChebyshevCenteredCumulativeWeight
        (suzukiFirstTailChebyshevCenter count) x ≤
      x ^ (-5 / 2 : ℝ) *
        ((23 / 4 : ℝ) + (3 / 4 : ℝ) *
          (Real.log (((count + 2 : ℕ) : ℝ)) - Real.log x)) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hcenter :=
    suzukiFirstTailChebyshevCenter_lt_log_endpoint_add_five count
  unfold suzukiChebyshevCenteredCumulativeWeight
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hxpos.le _)
  linarith

/-- Exact elementary integral of the logarithmic ratio kernel which occurs
in the cumulative-weight envelope. -/
theorem integral_rpow_neg_half_mul_log_endpoint_sub_log
    {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in Set.Ioc (1 : ℝ) b,
        x ^ (-1 / 2 : ℝ) * (Real.log b - Real.log x)) =
      4 * (Real.sqrt b - 1) - 2 * Real.log b := by
  have hnegativeKernel :
      (∫ x in Set.Ioc (1 : ℝ) b,
          x ^ (-1 / 2 : ℝ) * (Real.log b - Real.log x)) =
        -∫ x in Set.Ioc (1 : ℝ) b,
          suzukiChebyshevCenteredKernel (Real.log b) x := by
    rw [← MeasureTheory.integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _hx
    unfold suzukiChebyshevCenteredKernel suzukiChebyshevMassKernel
    ring
  rw [hnegativeKernel,
    integral_suzukiChebyshevCenteredKernel (Real.log b) hb]
  unfold suzukiChebyshevCenteredPrimitive
  rw [← Real.sqrt_eq_rpow]
  simp only [Real.log_one, Real.one_rpow, zero_sub]
  ring

/-! ## The interior cumulative moment -/

/-- Explicit integrable majorant for the cumulative PNT-error moment at
endpoint `b`. -/
def suzukiChebyshevCumulativeMomentEnvelope (b x : ℝ) : ℝ :=
  (5 / 2 : ℝ) * x ^ (-1 / 2 : ℝ) *
    ((23 / 4 : ℝ) + (3 / 4 : ℝ) * (Real.log b - Real.log x))

/-- Pointwise domination of the canonical cumulative-error integrand by its
explicit elementary envelope. -/
theorem abs_suzukiChebyshevCenteredCumulativeWeight_mul_error_le
    (count : ℕ) {x : ℝ} (hxone : 1 ≤ x)
    (hxend : x ≤ ((count + 2 : ℕ) : ℝ)) :
    |suzukiChebyshevCenteredCumulativeWeight
          (suzukiFirstTailChebyshevCenter count) x *
        suzukiChebyshevCumulativePNTError x| ≤
      suzukiChebyshevCumulativeMomentEnvelope
        (((count + 2 : ℕ) : ℝ)) x := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  change |suzukiChebyshevCenteredCumulativeWeight r x *
      suzukiChebyshevCumulativePNTError x| ≤
    suzukiChebyshevCumulativeMomentEnvelope b x
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hweightPos :
      0 < suzukiChebyshevCenteredCumulativeWeight r x := by
    dsimp only [r, b] at hxend ⊢
    exact
      suzukiChebyshevCenteredCumulativeWeight_pos_on_firstTailPrefix
        count hxone hxend
  have hweightUpper :
      suzukiChebyshevCenteredCumulativeWeight r x ≤
        x ^ (-5 / 2 : ℝ) *
          ((23 / 4 : ℝ) + (3 / 4 : ℝ) *
            (Real.log b - Real.log x)) := by
    dsimp only [r, b]
    exact
      suzukiChebyshevCenteredCumulativeWeight_le_of_one_le count hxone
  have herror := abs_suzukiChebyshevCumulativePNTError_le hxone
  have herrorQuadratic :
      |suzukiChebyshevCumulativePNTError x| ≤
        (5 / 2 : ℝ) * x ^ 2 := by
    nlinarith
  have hupperNonneg :
      0 ≤ x ^ (-5 / 2 : ℝ) *
        ((23 / 4 : ℝ) + (3 / 4 : ℝ) *
          (Real.log b - Real.log x)) :=
    hweightPos.le.trans hweightUpper
  have hpower :
      x ^ (-5 / 2 : ℝ) * x ^ 2 = x ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hxpos]
    congr 1
    ring
  rw [abs_mul, abs_of_nonneg hweightPos.le]
  calc
    suzukiChebyshevCenteredCumulativeWeight r x *
          |suzukiChebyshevCumulativePNTError x| ≤
        (x ^ (-5 / 2 : ℝ) *
            ((23 / 4 : ℝ) + (3 / 4 : ℝ) *
              (Real.log b - Real.log x))) *
          ((5 / 2 : ℝ) * x ^ 2) :=
      mul_le_mul hweightUpper herrorQuadratic (abs_nonneg _) hupperNonneg
    _ = (5 / 2 : ℝ) *
          (x ^ (-5 / 2 : ℝ) * x ^ 2) *
            ((23 / 4 : ℝ) + (3 / 4 : ℝ) *
              (Real.log b - Real.log x)) := by ring
    _ = suzukiChebyshevCumulativeMomentEnvelope b x := by
      rw [hpower]
      rfl

private theorem integrableOn_suzukiChebyshevCumulativeMomentEnvelope_Ioc
    (b : ℝ) :
    IntegrableOn (suzukiChebyshevCumulativeMomentEnvelope b)
      (Set.Ioc 1 b) := by
  apply IntegrableOn.mono_set _ Set.Ioc_subset_Icc_self
  apply ContinuousOn.integrableOn_Icc
  intro x hx
  have hxpos : 0 < x := zero_lt_one.trans_le hx.1
  unfold suzukiChebyshevCumulativeMomentEnvelope
  exact
    (continuousAt_const.mul
      (Real.continuousAt_rpow_const x (-1 / 2 : ℝ)
        (Or.inl hxpos.ne'))).mul
      (continuousAt_const.add
        (continuousAt_const.mul
          (continuousAt_const.sub
            (Real.continuousAt_log hxpos.ne')))) |>.continuousWithinAt

/-- The majorant has an exact square-root-minus-log integral. -/
theorem integral_suzukiChebyshevCumulativeMomentEnvelope_eq
    {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in Set.Ioc (1 : ℝ) b,
        suzukiChebyshevCumulativeMomentEnvelope b x) =
      (145 / 4 : ℝ) * (Real.sqrt b - 1) -
        (15 / 4 : ℝ) * Real.log b := by
  have hpure :
      (∫ x in Set.Ioc (1 : ℝ) b, x ^ (-1 / 2 : ℝ)) =
        2 * (Real.sqrt b - 1) := by
    rw [← intervalIntegral.integral_of_le hb,
      integral_rpow
        (r := (-1 / 2 : ℝ)) (Or.inl (by norm_num))]
    rw [Real.sqrt_eq_rpow]
    ring_nf
  have hlog := integral_rpow_neg_half_mul_log_endpoint_sub_log hb
  have hpowerIntegrable : IntegrableOn
      (fun x : ℝ => x ^ (-1 / 2 : ℝ)) (Set.Ioc 1 b) := by
    apply IntegrableOn.mono_set _ Set.Ioc_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc
    intro x hx
    exact (Real.continuousAt_rpow_const x (-1 / 2 : ℝ)
      (Or.inl (zero_lt_one.trans_le hx.1).ne')).continuousWithinAt
  have hlogIntegrable : IntegrableOn
      (fun x : ℝ => x ^ (-1 / 2 : ℝ) *
        (Real.log b - Real.log x)) (Set.Ioc 1 b) := by
    apply IntegrableOn.mono_set _ Set.Ioc_subset_Icc_self
    apply ContinuousOn.integrableOn_Icc
    intro x hx
    have hxpos : 0 < x := zero_lt_one.trans_le hx.1
    exact
      ((Real.continuousAt_rpow_const x (-1 / 2 : ℝ)
          (Or.inl hxpos.ne')).mul
        (continuousAt_const.sub
          (Real.continuousAt_log hxpos.ne'))).continuousWithinAt
  have hsplit :
      (∫ x in Set.Ioc (1 : ℝ) b,
          suzukiChebyshevCumulativeMomentEnvelope b x) =
        ∫ x in Set.Ioc (1 : ℝ) b,
          (115 / 8 : ℝ) * x ^ (-1 / 2 : ℝ) +
            (15 / 8 : ℝ) *
              (x ^ (-1 / 2 : ℝ) *
                (Real.log b - Real.log x)) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _hx
    unfold suzukiChebyshevCumulativeMomentEnvelope
    ring
  rw [hsplit,
    MeasureTheory.integral_add
      (hpowerIntegrable.const_mul (115 / 8 : ℝ))
      (hlogIntegrable.const_mul (15 / 8 : ℝ)),
    MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, hpure, hlog]
  ring

/-- The cumulative-error endpoint term is bounded by
`(35/4) * sqrt(endpoint)`. -/
theorem abs_suzukiChebyshevCenteredPNTWeight_mul_cumulativeError_endpoint_le
    (count : ℕ) :
    |suzukiChebyshevCenteredPNTWeight
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) *
        suzukiChebyshevCumulativePNTError
          (((count + 2 : ℕ) : ℝ))| ≤
      (35 / 4 : ℝ) * Real.sqrt (((count + 2 : ℕ) : ℝ)) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  change |suzukiChebyshevCenteredPNTWeight r b *
      suzukiChebyshevCumulativePNTError b| ≤
    (35 / 4 : ℝ) * Real.sqrt b
  have hb1 : 1 ≤ b := by
    dsimp only [b]
    exact_mod_cast (show 1 ≤ count + 2 by omega)
  have hbpos : 0 < b := zero_lt_one.trans_le hb1
  have hweight :
      |suzukiChebyshevCenteredPNTWeight r b| ≤
        (7 / 2 : ℝ) * b ^ (-3 / 2 : ℝ) := by
    dsimp only [r, b]
    exact
      abs_suzukiChebyshevCenteredPNTWeight_firstTailEndpoint_le count
  have herror := abs_suzukiChebyshevCumulativePNTError_le hb1
  have herrorQuadratic :
      |suzukiChebyshevCumulativePNTError b| ≤
        (5 / 2 : ℝ) * b ^ 2 := by
    nlinarith
  have hpower :
      b ^ (-3 / 2 : ℝ) * b ^ 2 = Real.sqrt b := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hbpos]
    rw [Real.sqrt_eq_rpow]
    congr 1
    ring
  rw [abs_mul]
  calc
    |suzukiChebyshevCenteredPNTWeight r b| *
          |suzukiChebyshevCumulativePNTError b| ≤
        ((7 / 2 : ℝ) * b ^ (-3 / 2 : ℝ)) *
          ((5 / 2 : ℝ) * b ^ 2) :=
      mul_le_mul hweight herrorQuadratic (abs_nonneg _) (by positivity)
    _ = (35 / 4 : ℝ) *
          (b ^ (-3 / 2 : ℝ) * b ^ 2) := by ring
    _ = (35 / 4 : ℝ) * Real.sqrt b := by rw [hpower]

/-- The entire interior cumulative-error moment is bounded by
`(145/4) * sqrt(endpoint)`. -/
theorem abs_integral_suzukiChebyshevCenteredCumulativeWeight_mul_error_le
    (count : ℕ) :
    |∫ x in Set.Ioc (1 : ℝ) ((count + 2 : ℕ) : ℝ),
        suzukiChebyshevCenteredCumulativeWeight
            (suzukiFirstTailChebyshevCenter count) x *
          suzukiChebyshevCumulativePNTError x| ≤
      (145 / 4 : ℝ) * Real.sqrt (((count + 2 : ℕ) : ℝ)) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  change |∫ x in Set.Ioc (1 : ℝ) b,
      suzukiChebyshevCenteredCumulativeWeight r x *
        suzukiChebyshevCumulativePNTError x| ≤
    (145 / 4 : ℝ) * Real.sqrt b
  have hb1 : 1 ≤ b := by
    dsimp only [b]
    exact_mod_cast (show 1 ≤ count + 2 by omega)
  have hnorm :
      |∫ x in Set.Ioc (1 : ℝ) b,
          suzukiChebyshevCenteredCumulativeWeight r x *
            suzukiChebyshevCumulativePNTError x| ≤
        ∫ x in Set.Ioc (1 : ℝ) b,
          suzukiChebyshevCumulativeMomentEnvelope b x := by
    change ‖∫ x in Set.Ioc (1 : ℝ) b,
        suzukiChebyshevCenteredCumulativeWeight r x *
          suzukiChebyshevCumulativePNTError x‖ ≤ _
    apply norm_integral_le_of_norm_le
      (integrableOn_suzukiChebyshevCumulativeMomentEnvelope_Ioc b)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs]
    dsimp only [r, b]
    exact
      abs_suzukiChebyshevCenteredCumulativeWeight_mul_error_le
        count hx.1.le hx.2
  rw [integral_suzukiChebyshevCumulativeMomentEnvelope_eq hb1] at hnorm
  have hlog : 0 ≤ Real.log b := Real.log_nonneg hb1
  linarith

/-- The complete endpoint-plus-interior cumulative moment has the uniform
square-root envelope `45 * sqrt(endpoint)`. -/
theorem abs_suzukiChebyshevCumulativePositiveKernelMoment_le
    (count : ℕ) :
    |suzukiChebyshevCenteredPNTWeight
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) *
        suzukiChebyshevCumulativePNTError
          (((count + 2 : ℕ) : ℝ)) +
      (∫ x in Set.Ioc (1 : ℝ) ((count + 2 : ℕ) : ℝ),
        suzukiChebyshevCenteredCumulativeWeight
            (suzukiFirstTailChebyshevCenter count) x *
          suzukiChebyshevCumulativePNTError x)| ≤
      45 * Real.sqrt (((count + 2 : ℕ) : ℝ)) := by
  calc
    |suzukiChebyshevCenteredPNTWeight
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) *
        suzukiChebyshevCumulativePNTError
          (((count + 2 : ℕ) : ℝ)) +
      (∫ x in Set.Ioc (1 : ℝ) ((count + 2 : ℕ) : ℝ),
        suzukiChebyshevCenteredCumulativeWeight
            (suzukiFirstTailChebyshevCenter count) x *
          suzukiChebyshevCumulativePNTError x)| ≤
        |suzukiChebyshevCenteredPNTWeight
            (suzukiFirstTailChebyshevCenter count)
            (((count + 2 : ℕ) : ℝ)) *
          suzukiChebyshevCumulativePNTError
            (((count + 2 : ℕ) : ℝ))| +
        |∫ x in Set.Ioc (1 : ℝ) ((count + 2 : ℕ) : ℝ),
          suzukiChebyshevCenteredCumulativeWeight
              (suzukiFirstTailChebyshevCenter count) x *
            suzukiChebyshevCumulativePNTError x| := abs_add_le _ _
    _ ≤ (35 / 4 : ℝ) * Real.sqrt (((count + 2 : ℕ) : ℝ)) +
          (145 / 4 : ℝ) * Real.sqrt (((count + 2 : ℕ) : ℝ)) :=
      add_le_add
        (abs_suzukiChebyshevCenteredPNTWeight_mul_cumulativeError_endpoint_le
          count)
        (abs_integral_suzukiChebyshevCenteredCumulativeWeight_mul_error_le
          count)
    _ = 45 * Real.sqrt (((count + 2 : ℕ) : ℝ)) := by ring

/-! ## The complete centered PNT remainder -/

/-- The direct endpoint PNT-error boundary term has square-root envelope
`25 * sqrt(endpoint)`. -/
theorem abs_suzukiChebyshevCenteredKernel_mul_pntError_endpoint_le
    (count : ℕ) :
    |suzukiChebyshevCenteredKernel
          (suzukiFirstTailChebyshevCenter count)
          (((count + 2 : ℕ) : ℝ)) *
        (Chebyshev.psi (((count + 2 : ℕ) : ℝ)) -
          ((count + 2 : ℕ) : ℝ))| ≤
      25 * Real.sqrt (((count + 2 : ℕ) : ℝ)) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  change |suzukiChebyshevCenteredKernel r b *
      (Chebyshev.psi b - b)| ≤ 25 * Real.sqrt b
  have hb1 : 1 ≤ b := by
    dsimp only [b]
    exact_mod_cast (show 1 ≤ count + 2 by omega)
  have hbpos : 0 < b := zero_lt_one.trans_le hb1
  have hkernel :
      |suzukiChebyshevCenteredKernel r b| ≤
        5 * b ^ (-1 / 2 : ℝ) := by
    dsimp only [r, b]
    exact
      abs_suzukiChebyshevCenteredKernel_firstTailEndpoint_le count
  have herror :=
    abs_chebyshevPsi_sub_self_le_five_mul_self_of_one_le hb1
  have hpower :
      b ^ (-1 / 2 : ℝ) * b = Real.sqrt b := by
    rw [← Real.rpow_add_one hbpos.ne' (-1 / 2 : ℝ)]
    rw [Real.sqrt_eq_rpow]
    congr 1
    ring
  rw [abs_mul]
  calc
    |suzukiChebyshevCenteredKernel r b| *
          |Chebyshev.psi b - b| ≤
        (5 * b ^ (-1 / 2 : ℝ)) * (5 * b) :=
      mul_le_mul hkernel herror (abs_nonneg _) (by positivity)
    _ = 25 * (b ^ (-1 / 2 : ℝ) * b) := by ring
    _ = 25 * Real.sqrt b := by rw [hpower]

/-- The complete centered PNT remainder at every canonical endpoint is
unconditionally `O(sqrt(endpoint))`, with explicit constant `70`. -/
theorem abs_suzukiChebyshevCenteredPNTError_firstTailEndpoint_le
    (count : ℕ) :
    |suzukiChebyshevCenteredPNTError
        (suzukiFirstTailChebyshevCenter count)
        (((count + 2 : ℕ) : ℝ))| ≤
      70 * Real.sqrt (((count + 2 : ℕ) : ℝ)) := by
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  let r : ℝ := suzukiFirstTailChebyshevCenter count
  change |suzukiChebyshevCenteredPNTError r b| ≤
    70 * Real.sqrt b
  have hb1 : 1 ≤ b := by
    dsimp only [b]
    exact_mod_cast (show 1 ≤ count + 2 by omega)
  have hboundary :
      |suzukiChebyshevCenteredKernel r b *
        (Chebyshev.psi b - b)| ≤ 25 * Real.sqrt b := by
    dsimp only [r, b]
    exact
      abs_suzukiChebyshevCenteredKernel_mul_pntError_endpoint_le count
  have hmoment :
      |suzukiChebyshevCenteredPNTWeight r b *
          suzukiChebyshevCumulativePNTError b +
        (∫ x in Set.Ioc (1 : ℝ) b,
          suzukiChebyshevCenteredCumulativeWeight r x *
            suzukiChebyshevCumulativePNTError x)| ≤
        45 * Real.sqrt b := by
    dsimp only [r, b]
    exact abs_suzukiChebyshevCumulativePositiveKernelMoment_le count
  have hidentity :
      suzukiChebyshevCenteredPNTError r b =
        suzukiChebyshevCenteredKernel r b *
            (Chebyshev.psi b - b) -
          (suzukiChebyshevCenteredPNTWeight r b *
              suzukiChebyshevCumulativePNTError b +
            ∫ x in Set.Ioc (1 : ℝ) b,
              suzukiChebyshevCenteredCumulativeWeight r x *
                suzukiChebyshevCumulativePNTError x) := by
    unfold suzukiChebyshevCenteredPNTError
    rw [
      integral_deriv_suzukiChebyshevCenteredKernel_mul_error_eq_cumulative
        r hb1]
  rw [hidentity]
  calc
    |suzukiChebyshevCenteredKernel r b *
          (Chebyshev.psi b - b) -
        (suzukiChebyshevCenteredPNTWeight r b *
            suzukiChebyshevCumulativePNTError b +
          ∫ x in Set.Ioc (1 : ℝ) b,
            suzukiChebyshevCenteredCumulativeWeight r x *
              suzukiChebyshevCumulativePNTError x)| ≤
        |suzukiChebyshevCenteredKernel r b *
          (Chebyshev.psi b - b)| +
        |suzukiChebyshevCenteredPNTWeight r b *
            suzukiChebyshevCumulativePNTError b +
          ∫ x in Set.Ioc (1 : ℝ) b,
            suzukiChebyshevCenteredCumulativeWeight r x *
              suzukiChebyshevCumulativePNTError x| := abs_sub _ _
    _ ≤ 25 * Real.sqrt b + 45 * Real.sqrt b :=
      add_le_add hboundary hmoment
    _ = 70 * Real.sqrt b := by ring

/-- Consequently the complete centered PNT remainder is sublinear in its
integer endpoint, unconditionally and along the canonical centers. -/
theorem tendsto_suzukiChebyshevCenteredPNTError_div_endpoint_zero :
    Tendsto
      (fun count : ℕ =>
        suzukiChebyshevCenteredPNTError
            (suzukiFirstTailChebyshevCenter count)
            (((count + 2 : ℕ) : ℝ)) /
          (((count + 2 : ℕ) : ℝ)))
      atTop (nhds 0) := by
  have hendpointTop :
      Tendsto (fun count : ℕ => (((count + 2 : ℕ) : ℝ)))
        atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_atTop_add_const_right atTop (2 : ℝ)
        tendsto_natCast_atTop_atTop)
  have hdecay :
      Tendsto
        (fun count : ℕ =>
          (((count + 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)))
        atTop (nhds 0) := by
    simpa only [Function.comp_def, neg_div] using
      ((tendsto_rpow_neg_atTop
          (by norm_num : (0 : ℝ) < 1 / 2)).comp hendpointTop)
  have hmajor :
      Tendsto
        (fun count : ℕ =>
          70 * (((count + 2 : ℕ) : ℝ) ^ (-1 / 2 : ℝ)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdecay
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero'
  · exact Eventually.of_forall fun _count => norm_nonneg _
  · exact Eventually.of_forall fun count => by
      let b : ℝ := ((count + 2 : ℕ) : ℝ)
      let P : ℝ := suzukiChebyshevCenteredPNTError
        (suzukiFirstTailChebyshevCenter count) b
      change ‖P / b‖ ≤ 70 * b ^ (-1 / 2 : ℝ)
      have hbpos : 0 < b := by
        dsimp only [b]
        exact_mod_cast (show 0 < count + 2 by omega)
      have hP : |P| ≤ 70 * Real.sqrt b := by
        dsimp only [P, b]
        exact
          abs_suzukiChebyshevCenteredPNTError_firstTailEndpoint_le count
      have hratio :
          Real.sqrt b / b = b ^ (-1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg_one,
          ← Real.rpow_add hbpos]
        congr 1
        ring
      rw [Real.norm_eq_abs, abs_div, abs_of_pos hbpos]
      calc
        |P| / b ≤ (70 * Real.sqrt b) / b :=
          div_le_div_of_nonneg_right hP hbpos.le
        _ = 70 * (Real.sqrt b / b) := by ring
        _ = 70 * b ^ (-1 / 2 : ℝ) := by rw [hratio]
  · exact hmajor

end

end RiemannGaussian
