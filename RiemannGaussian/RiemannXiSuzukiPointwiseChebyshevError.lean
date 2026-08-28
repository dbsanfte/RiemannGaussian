import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevLegendre
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The explicit Chebyshev-error form of the Suzuki frontier

The Chebyshev--Legendre reduction leaves a centered weighted log-moment.  This
file gives that functional one direct Abel kernel and splits it exactly into

* an elementary continuous main term, and
* a single signed integral against `Chebyshev.psi x - x`.

The continuous term is evaluated in closed form.  The resulting terminal
criterion isolates the remaining arithmetic rigidity problem in the PNT
error itself; no finite cutoff certificates or unproved asymptotics enter.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## The centered Abel kernel -/

/-- The multiplicative kernel for a log-moment centered at `center`. -/
def suzukiChebyshevCenteredKernel (center x : ℝ) : ℝ :=
  (Real.log x - center) * suzukiChebyshevMassKernel x

/-- Elementary antiderivative of the centered kernel on the positive
half-line. -/
def suzukiChebyshevCenteredPrimitive (center x : ℝ) : ℝ :=
  2 * (x ^ (1 / 2 : ℝ) * (Real.log x - center - 2))

/-- The continuous `psi(x) = x` contribution to the centered Abel
functional. -/
def suzukiChebyshevCenteredContinuousMain
    (center b : ℝ) : ℝ :=
  suzukiChebyshevCenteredKernel center b * b -
    ∫ x in Set.Ioc (1 : ℝ) b,
      deriv (suzukiChebyshevCenteredKernel center) x * x

/-- The exact remaining centered functional of the PNT error
`Chebyshev.psi x - x`. -/
def suzukiChebyshevCenteredPNTError
    (center b : ℝ) : ℝ :=
  suzukiChebyshevCenteredKernel center b *
      (Chebyshev.psi b - b) -
    ∫ x in Set.Ioc (1 : ℝ) b,
      deriv (suzukiChebyshevCenteredKernel center) x *
        (Chebyshev.psi x - x)

private theorem contDiffOn_suzukiChebyshevCenteredKernel_Ioi
    (center : ℝ) :
    ContDiffOn ℝ 2 (suzukiChebyshevCenteredKernel center)
      (Set.Ioi 0) := by
  intro x hx
  unfold suzukiChebyshevCenteredKernel suzukiChebyshevMassKernel
  exact (((Real.contDiffAt_log (n := (2 : WithTop ℕ∞))).2 hx.ne')
    |>.contDiffWithinAt
    |>.sub contDiffWithinAt_const).mul
      ((Real.contDiffAt_rpow_const (n := 2) (Or.inl hx.ne'))
        |>.contDiffWithinAt)

private theorem integrableOn_deriv_suzukiChebyshevCenteredKernel_Icc
    (center : ℝ) {b : ℝ} :
    IntegrableOn (deriv (suzukiChebyshevCenteredKernel center))
      (Set.Icc 1 b) := by
  have hcontinuous : ContinuousOn
      (deriv (suzukiChebyshevCenteredKernel center)) (Set.Ioi 0) :=
    (contDiffOn_suzukiChebyshevCenteredKernel_Ioi center)
      |>.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  apply (hcontinuous.mono _).integrableOn_Icc
  intro x hx
  exact zero_lt_one.trans_le hx.1

/-- The displayed centered primitive differentiates to the centered Abel
kernel at every positive point. -/
theorem hasDerivAt_suzukiChebyshevCenteredPrimitive
    (center : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (suzukiChebyshevCenteredPrimitive center)
      (suzukiChebyshevCenteredKernel center x) x := by
  have hpower : HasDerivAt (fun y : ℝ => y ^ (1 / 2 : ℝ))
      ((1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ)) x := by
    convert Real.hasDerivAt_rpow_const
      (x := x) (p := (1 / 2 : ℝ)) (Or.inl hx.ne') using 1
    ring_nf
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log y - center - 2) x⁻¹ x :=
    (Real.hasDerivAt_log hx.ne').sub_const center |>.sub_const 2
  have hproduct := hpower.mul hlog
  have hscaled : HasDerivAt
      (suzukiChebyshevCenteredPrimitive center)
      (2 * (((1 / 2 : ℝ) * x ^ (-1 / 2 : ℝ)) *
        (Real.log x - center - 2) + x ^ (1 / 2 : ℝ) * x⁻¹)) x := by
    change HasDerivAt
      (fun y : ℝ =>
        2 * (y ^ (1 / 2 : ℝ) * (Real.log y - center - 2))) _ x
    exact hproduct.const_mul 2
  have hpowerMulInv :
      x ^ (1 / 2 : ℝ) * x⁻¹ = x ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx]
    congr 1
    ring_nf
  apply hscaled.congr_deriv
  unfold suzukiChebyshevCenteredKernel suzukiChebyshevMassKernel
  rw [hpowerMulInv]
  ring_nf

/-- Explicit derivative of the centered Abel kernel on the positive
half-line. -/
theorem deriv_suzukiChebyshevCenteredKernel
    (center : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (suzukiChebyshevCenteredKernel center) x =
      x ^ (-3 / 2 : ℝ) *
        (1 - (Real.log x - center) / 2) := by
  have hlog : HasDerivAt
      (fun y : ℝ => Real.log y - center) x⁻¹ x :=
    (Real.hasDerivAt_log hx.ne').sub_const center
  have hpower : HasDerivAt (fun y : ℝ => y ^ (-1 / 2 : ℝ))
      ((-1 / 2 : ℝ) * x ^ (-3 / 2 : ℝ)) x := by
    convert Real.hasDerivAt_rpow_const
      (x := x) (p := (-1 / 2 : ℝ)) (Or.inl hx.ne') using 1
    ring_nf
  have hkernel : HasDerivAt
      (suzukiChebyshevCenteredKernel center)
      (x⁻¹ * x ^ (-1 / 2 : ℝ) +
        (Real.log x - center) *
          ((-1 / 2 : ℝ) * x ^ (-3 / 2 : ℝ))) x := by
    change HasDerivAt
      (fun y : ℝ =>
        (Real.log y - center) * y ^ (-1 / 2 : ℝ)) _ x
    exact hlog.mul hpower
  have hinvMulPower :
      x⁻¹ * x ^ (-1 / 2 : ℝ) = x ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx]
    congr 1
    ring_nf
  rw [hkernel.deriv, hinvMulPower]
  ring

/-- The centered kernel has the displayed elementary definite integral on
every interval beginning at one. -/
theorem integral_suzukiChebyshevCenteredKernel
    (center : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in Set.Ioc (1 : ℝ) b,
        suzukiChebyshevCenteredKernel center x) =
      suzukiChebyshevCenteredPrimitive center b -
        suzukiChebyshevCenteredPrimitive center 1 := by
  have hintegrable : IntervalIntegrable
      (suzukiChebyshevCenteredKernel center) volume 1 b := by
    apply ContinuousOn.intervalIntegrable
    apply (contDiffOn_suzukiChebyshevCenteredKernel_Ioi center)
      |>.continuousOn.mono
    intro x hx
    rw [Set.uIcc_of_le hb] at hx
    exact zero_lt_one.trans_le hx.1
  rw [← intervalIntegral.integral_of_le hb]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [Set.uIcc_of_le hb] at hx
    exact hasDerivAt_suzukiChebyshevCenteredPrimitive center
      (zero_lt_one.trans_le hx.1)
  · exact hintegrable

/-- Direct finite Abel summation for the centered kernel. -/
theorem suzukiChebyshevCenteredAbel_eq
    (center : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    ∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
        suzukiChebyshevCenteredKernel center n *
          ArithmeticFunction.vonMangoldt n =
      suzukiChebyshevCenteredKernel center b * Chebyshev.psi b -
        ∫ x in Set.Ioc (1 : ℝ) b,
          deriv (suzukiChebyshevCenteredKernel center) x *
            Chebyshev.psi x := by
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (a := (1 : ℝ)) (b := b) (by norm_num) hb
    (fun x hx => by
      unfold suzukiChebyshevCenteredKernel
        suzukiChebyshevMassKernel
      exact ((Real.differentiableAt_log (by linarith [hx.1])).sub_const
        center).mul
          (Real.differentiableAt_rpow_const_of_ne _
            (by linarith [hx.1])))
    (integrableOn_deriv_suzukiChebyshevCenteredKernel_Icc center)
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at h
  simpa [Chebyshev.psi_eq_zero_of_lt_two (by norm_num : (1 : ℝ) < 2)]
    using h

/-- At an integer endpoint, the centered functional from the Legendre
frontier is exactly the finite sum of the direct centered kernel. -/
theorem suzukiChebyshevWeightedCenteredLogMoment_nat_eq_sum
    (center : ℝ) (cutoff : ℕ) :
    suzukiChebyshevWeightedCenteredLogMoment center
        ((cutoff + 1 : ℕ) : ℝ) =
      ∑ n ∈ Finset.Ioc 1 (cutoff + 1),
        suzukiChebyshevCenteredKernel center n *
          ArithmeticFunction.vonMangoldt n := by
  unfold suzukiChebyshevWeightedCenteredLogMoment
  rw [← screwPrefixMoment_suzukiPrime_eq_chebyshevWeightedLogMoment
      cutoff,
    ← screwPrefixMass_suzukiPrimeWeight_eq_chebyshevWeightedMass cutoff,
    screwPrefixMoment_suzukiPrime_eq_suzukiChebyshevLogMomentSum,
    screwPrefixMass_suzukiPrimeWeight_eq_suzukiChebyshevMassSum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  unfold suzukiChebyshevCenteredKernel
    suzukiChebyshevLogMomentKernel
  ring_nf

/-- At every integer endpoint, the centered Legendre functional has one
direct Abel representation against `Chebyshev.psi`. -/
theorem suzukiChebyshevWeightedCenteredLogMoment_nat_eq_abel
    (center : ℝ) (cutoff : ℕ) :
    suzukiChebyshevWeightedCenteredLogMoment center
        ((cutoff + 1 : ℕ) : ℝ) =
      suzukiChebyshevCenteredKernel center ((cutoff + 1 : ℕ) : ℝ) *
          Chebyshev.psi ((cutoff + 1 : ℕ) : ℝ) -
        ∫ x in Set.Ioc (1 : ℝ) ((cutoff + 1 : ℕ) : ℝ),
          deriv (suzukiChebyshevCenteredKernel center) x *
            Chebyshev.psi x := by
  rw [suzukiChebyshevWeightedCenteredLogMoment_nat_eq_sum]
  simpa only [Nat.floor_natCast] using
    (suzukiChebyshevCenteredAbel_eq center
      (b := ((cutoff + 1 : ℕ) : ℝ)) (by
        norm_num only [Nat.cast_add, Nat.cast_one]
        have hcutoff : (0 : ℝ) ≤ cutoff := Nat.cast_nonneg cutoff
        linarith))

/-! ## Exact separation of the PNT error -/

/-- The direct centered Abel functional is its continuous main term plus one
signed integral against `Chebyshev.psi x - x`. -/
theorem suzukiChebyshevCenteredAbel_eq_continuousMain_add_pntError
    (center b : ℝ) :
    suzukiChebyshevCenteredKernel center b * Chebyshev.psi b -
        (∫ x in Set.Ioc (1 : ℝ) b,
          deriv (suzukiChebyshevCenteredKernel center) x *
            Chebyshev.psi x) =
      suzukiChebyshevCenteredContinuousMain center b +
        suzukiChebyshevCenteredPNTError center b := by
  have hderivIcc :=
    integrableOn_deriv_suzukiChebyshevCenteredKernel_Icc
      center (b := b)
  have hpsiIcc := integrableOn_mul_sum_Icc
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (a := (1 : ℝ)) (b := b) (m := 0) (by norm_num) hderivIcc
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at hpsiIcc
  have hpsi := hpsiIcc.mono_set Set.Ioc_subset_Icc_self
  have hxderivIcc : IntegrableOn
      (fun x : ℝ => x *
        deriv (suzukiChebyshevCenteredKernel center) x)
      (Set.Icc (1 : ℝ) b) :=
    IntegrableOn.continuousOn_mul continuous_id.continuousOn
      hderivIcc isCompact_Icc
  have hxIcc : IntegrableOn
      (fun x : ℝ =>
        deriv (suzukiChebyshevCenteredKernel center) x * x)
      (Set.Icc (1 : ℝ) b) := by
    simpa only [mul_comm] using hxderivIcc
  have hx := hxIcc.mono_set Set.Ioc_subset_Icc_self
  have hintegral :
      (∫ x in Set.Ioc (1 : ℝ) b,
          deriv (suzukiChebyshevCenteredKernel center) x *
            Chebyshev.psi x) -
        (∫ x in Set.Ioc (1 : ℝ) b,
          deriv (suzukiChebyshevCenteredKernel center) x * x) =
        ∫ x in Set.Ioc (1 : ℝ) b,
          deriv (suzukiChebyshevCenteredKernel center) x *
            (Chebyshev.psi x - x) := by
    rw [← integral_sub hpsi hx]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _hx
    ring_nf
  unfold suzukiChebyshevCenteredContinuousMain
    suzukiChebyshevCenteredPNTError
  rw [← hintegral]
  ring_nf

/-! ## Closed evaluation of the continuous contribution -/

/-- Integration by parts identifies the continuous contribution with the
integral of the centered kernel plus its lower-endpoint boundary value. -/
theorem suzukiChebyshevCenteredContinuousMain_eq_kernel_one_add_integral
    (center : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    suzukiChebyshevCenteredContinuousMain center b =
      suzukiChebyshevCenteredKernel center 1 +
        ∫ x in Set.Ioc (1 : ℝ) b,
          suzukiChebyshevCenteredKernel center x := by
  have hderivInterval : IntervalIntegrable
      (deriv (suzukiChebyshevCenteredKernel center)) volume 1 b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb]
    exact integrableOn_deriv_suzukiChebyshevCenteredKernel_Icc center
  have hconstant : IntervalIntegrable (fun _ : ℝ => (1 : ℝ))
      volume 1 b := intervalIntegrable_const
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (1 : ℝ)) (b := b)
    (u := suzukiChebyshevCenteredKernel center)
    (u' := deriv (suzukiChebyshevCenteredKernel center))
    (v := fun x : ℝ => x) (v' := fun _ : ℝ => 1)
    (fun x hx => by
      rw [Set.uIcc_of_le hb] at hx
      unfold suzukiChebyshevCenteredKernel
        suzukiChebyshevMassKernel
      exact (((Real.differentiableAt_log
        (zero_lt_one.trans_le hx.1).ne').sub_const center).mul
          (Real.differentiableAt_rpow_const_of_ne _
            (zero_lt_one.trans_le hx.1).ne')).hasDerivAt)
    (fun x _hx => hasDerivAt_id x) hderivInterval hconstant
  rw [intervalIntegral.integral_of_le hb,
    intervalIntegral.integral_of_le hb] at hip
  simp only [mul_one] at hip
  unfold suzukiChebyshevCenteredContinuousMain
  linarith

/-- Exact elementary value of the continuous `psi(x) = x` contribution. -/
theorem suzukiChebyshevCenteredContinuousMain_eq
    (center : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    suzukiChebyshevCenteredContinuousMain center b =
      suzukiChebyshevCenteredPrimitive center b + center + 4 := by
  rw [suzukiChebyshevCenteredContinuousMain_eq_kernel_one_add_integral
      center hb,
    integral_suzukiChebyshevCenteredKernel center hb]
  simp [suzukiChebyshevCenteredKernel, suzukiChebyshevMassKernel,
    suzukiChebyshevCenteredPrimitive]
  ring

/-- Expanded closed form of the continuous centered contribution. -/
theorem suzukiChebyshevCenteredContinuousMain_eq_explicit
    (center : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    suzukiChebyshevCenteredContinuousMain center b =
      2 * (b ^ (1 / 2 : ℝ) * (Real.log b - center - 2)) +
        center + 4 := by
  rw [suzukiChebyshevCenteredContinuousMain_eq center hb]
  rfl

/-- At an integer endpoint, the centered Legendre functional is exactly its
closed continuous contribution plus the remaining PNT-error functional. -/
theorem
    suzukiChebyshevWeightedCenteredLogMoment_nat_eq_continuousMain_add_pntError
    (center : ℝ) (cutoff : ℕ) :
    suzukiChebyshevWeightedCenteredLogMoment center
        ((cutoff + 1 : ℕ) : ℝ) =
      suzukiChebyshevCenteredContinuousMain center
          ((cutoff + 1 : ℕ) : ℝ) +
        suzukiChebyshevCenteredPNTError center
          ((cutoff + 1 : ℕ) : ℝ) := by
  rw [suzukiChebyshevWeightedCenteredLogMoment_nat_eq_abel,
    suzukiChebyshevCenteredAbel_eq_continuousMain_add_pntError]

/-- Fully evaluated integer-endpoint form of the centered functional. -/
theorem
    suzukiChebyshevWeightedCenteredLogMoment_nat_eq_explicitMain_add_pntError
    (center : ℝ) (cutoff : ℕ) :
    suzukiChebyshevWeightedCenteredLogMoment center
        ((cutoff + 1 : ℕ) : ℝ) =
      2 * ((((cutoff + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          (Real.log ((cutoff + 1 : ℕ) : ℝ) - center - 2)) +
        center + 4 +
        suzukiChebyshevCenteredPNTError center
          ((cutoff + 1 : ℕ) : ℝ) := by
  rw [
    suzukiChebyshevWeightedCenteredLogMoment_nat_eq_continuousMain_add_pntError,
    suzukiChebyshevCenteredContinuousMain_eq_explicit center (by
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hcutoff : (0 : ℝ) ≤ cutoff := Nat.cast_nonneg cutoff
      linarith)]

/-- The PNT remainder with the derivative removed: it is one boundary term
and one signed integral against `Chebyshev.psi x - x` with an elementary
kernel. -/
theorem suzukiChebyshevCenteredPNTError_eq_explicit
    (center b : ℝ) :
    suzukiChebyshevCenteredPNTError center b =
      (Real.log b - center) * b ^ (-1 / 2 : ℝ) *
          (Chebyshev.psi b - b) -
        ∫ x in Set.Ioc (1 : ℝ) b,
          (x ^ (-3 / 2 : ℝ) *
              (1 - (Real.log x - center) / 2)) *
            (Chebyshev.psi x - x) := by
  unfold suzukiChebyshevCenteredPNTError
  rw [show suzukiChebyshevCenteredKernel center b =
      (Real.log b - center) * b ^ (-1 / 2 : ℝ) by rfl]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [deriv_suzukiChebyshevCenteredKernel center
    (zero_lt_one.trans hx.1)]

/-! ## The exact PNT-error frontier -/

/-- Canonical Archimedean slope-matching point for the complete prefix
ending at `count + 2`. -/
def suzukiFirstTailChebyshevCenter (count : ℕ) : ℝ :=
  suzukiResetTransportMassPoint (Real.log 2)
    (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
    (le_refl (Real.log 2))
    suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
    (count + 1)

/-- Every remaining canonical transport gap is exactly an elementary
Archimedean baseline plus the single centered PNT-error functional. -/
theorem
    suzukiFirstTailResetTransportGap_succ_eq_explicitMain_add_pntError
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
      suzukiPointwiseArchimedean
          (suzukiFirstTailChebyshevCenter count) +
        2 * ((((count + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
          (Real.log ((count + 2 : ℕ) : ℝ) -
            suzukiFirstTailChebyshevCenter count - 2)) +
        suzukiFirstTailChebyshevCenter count + 4 +
        suzukiChebyshevCenteredPNTError
          (suzukiFirstTailChebyshevCenter count)
          ((count + 2 : ℕ) : ℝ) := by
  rw [
    suzukiFirstTailResetTransportGap_succ_eq_archimedean_add_chebyshevCenteredMoment]
  unfold suzukiFirstTailChebyshevCenter
  have hendpoint : count + 1 + 1 = count + 2 := by omega
  have hmoment :=
    suzukiChebyshevWeightedCenteredLogMoment_nat_eq_explicitMain_add_pntError
      (suzukiResetTransportMassPoint (Real.log 2)
        (suzukiPointwiseFrozenBaseSlope (Real.log 2) 1)
        (le_refl (Real.log 2))
        suzukiPointwiseFrozenBaseSlope_logTwo_one_nonpositive 1
        (count + 1))
      (count + 1)
  rw [hendpoint] at hmoment
  rw [hmoment]
  ring

/-- Tail positivity is exactly nonnegativity of the explicit
Archimedean-plus-PNT-error defect for every undisposed complete prefix. -/
theorem
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_explicitChebyshevPNTDefect :
    (∀ t : ℝ, Real.log 2 ≤ t →
      0 ≤ riemannXiSuzukiPsiNonnegative t) ↔
      ∀ count : ℕ, 1 ≤ count →
        0 ≤ suzukiPointwiseArchimedean
              (suzukiFirstTailChebyshevCenter count) +
            2 * ((((count + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
              (Real.log ((count + 2 : ℕ) : ℝ) -
                suzukiFirstTailChebyshevCenter count - 2)) +
            suzukiFirstTailChebyshevCenter count + 4 +
            suzukiChebyshevCenteredPNTError
              (suzukiFirstTailChebyshevCenter count)
              ((count + 2 : ℕ) : ℝ) := by
  rw [
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_two_le_cutoff_transportGap]
  constructor
  · intro hgaps count hcount
    have hgap := hgaps (count + 1) (by omega)
    rw [
      suzukiFirstTailResetTransportGap_succ_eq_explicitMain_add_pntError]
      at hgap
    exact hgap
  · intro hdefects cutoff hcutoff
    let count := cutoff - 1
    have hcount : 1 ≤ count := by
      dsimp only [count]
      omega
    have hdefect := hdefects count hcount
    have hcutoffEq : cutoff = count + 1 := by
      dsimp only [count]
      omega
    rw [hcutoffEq,
      suzukiFirstTailResetTransportGap_succ_eq_explicitMain_add_pntError]
    exact hdefect

/-- Final PNT-error form: the open theorem is precisely a uniform lower
bound on one explicit signed functional of `Chebyshev.psi x - x`, against a
fully evaluated deterministic baseline at every canonical Legendre point. -/
theorem
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_chebyshevPNTErrorLowerBound :
    (∀ t : ℝ, Real.log 2 ≤ t →
      0 ≤ riemannXiSuzukiPsiNonnegative t) ↔
      ∀ count : ℕ, 1 ≤ count →
        -(suzukiPointwiseArchimedean
              (suzukiFirstTailChebyshevCenter count) +
            2 * ((((count + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
              (Real.log ((count + 2 : ℕ) : ℝ) -
                suzukiFirstTailChebyshevCenter count - 2)) +
            suzukiFirstTailChebyshevCenter count + 4) ≤
          suzukiChebyshevCenteredPNTError
            (suzukiFirstTailChebyshevCenter count)
            ((count + 2 : ℕ) : ℝ) := by
  rw [
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_explicitChebyshevPNTDefect]
  constructor
  · intro hdefects count hcount
    have hdefect := hdefects count hcount
    linarith
  · intro hlower count hcount
    have hbound := hlower count hcount
    linarith

end

end RiemannGaussian
