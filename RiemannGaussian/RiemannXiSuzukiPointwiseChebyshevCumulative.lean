import RiemannGaussian.RiemannXiSuzukiPointwiseChebyshevKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Cumulative-error form of the Suzuki Chebyshev frontier

The first PNT-error kernel on every unresolved Suzuki prefix is positive.
This file proves the stronger shape fact needed for a second Abel transform:
that kernel is decreasing, with an explicit strictly positive negative
derivative.  The moment against the rough step function
`Chebyshev.psi x - x` can therefore be integrated by parts against its
cumulative error.

The proof uses absolute continuity and the almost-everywhere fundamental
theorem of calculus, so it does not differentiate `Chebyshev.psi` across its
jumps.  The cumulative error is also evaluated as an exact triangular
von-Mangoldt sum.  The resulting terminal criterion remains an RH-strength
open inequality; it is a sign-preserving structural reduction, not a proof
of that inequality.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

/-! ## Two successive positive kernels -/

/-- The first PNT-error weight: the derivative of the centered Abel kernel. -/
def suzukiChebyshevCenteredPNTWeight (center x : ℝ) : ℝ :=
  x ^ (-3 / 2 : ℝ) * (1 - (Real.log x - center) / 2)

/-- The positive weight produced after integrating the first PNT-error
weight by parts once more. -/
def suzukiChebyshevCenteredCumulativeWeight (center x : ℝ) : ℝ :=
  x ^ (-5 / 2 : ℝ) *
    (2 - (3 / 4 : ℝ) * (Real.log x - center))

/-- On the positive half-line, the first PNT weight is exactly the derivative
of the centered Abel kernel already appearing in the frontier theorem. -/
theorem deriv_suzukiChebyshevCenteredKernel_eq_pntWeight
    (center : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (suzukiChebyshevCenteredKernel center) x =
      suzukiChebyshevCenteredPNTWeight center x := by
  rw [deriv_suzukiChebyshevCenteredKernel center hx]
  rfl

/-- The first PNT weight has derivative equal to the negative cumulative
weight. -/
theorem hasDerivAt_suzukiChebyshevCenteredPNTWeight
    (center : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (suzukiChebyshevCenteredPNTWeight center)
      (-suzukiChebyshevCenteredCumulativeWeight center x) x := by
  have hpower : HasDerivAt (fun y : ℝ => y ^ (-3 / 2 : ℝ))
      ((-3 / 2 : ℝ) * x ^ (-5 / 2 : ℝ)) x := by
    convert Real.hasDerivAt_rpow_const
      (x := x) (p := (-3 / 2 : ℝ)) (Or.inl hx.ne') using 1
    ring_nf
  have hlog : HasDerivAt
      (fun y : ℝ => 1 - (Real.log y - center) / 2)
      (-(x⁻¹) / 2) x := by
    have hquotient : HasDerivAt
        (fun y : ℝ => (Real.log y - center) / 2)
        (x⁻¹ / 2) x :=
      ((Real.hasDerivAt_log hx.ne').sub_const center).div_const 2
    have hdifference : HasDerivAt
        (fun y : ℝ => 1 - (Real.log y - center) / 2)
        (0 - x⁻¹ / 2) x :=
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub hquotient
    exact hdifference.congr_deriv (by ring)
  have hproduct := hpower.mul hlog
  apply hproduct.congr_deriv
  have hpowerInv :
      x ^ (-3 / 2 : ℝ) * x⁻¹ = x ^ (-5 / 2 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hx]
    congr 1
    ring_nf
  rw [show x ^ (-3 / 2 : ℝ) * (-x⁻¹ / 2) =
      -(x ^ (-3 / 2 : ℝ) * x⁻¹) / 2 by ring,
    hpowerInv]
  unfold suzukiChebyshevCenteredCumulativeWeight
  ring

/-- Explicit derivative of the first PNT weight. -/
theorem deriv_suzukiChebyshevCenteredPNTWeight
    (center : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (suzukiChebyshevCenteredPNTWeight center) x =
      -suzukiChebyshevCenteredCumulativeWeight center x :=
  (hasDerivAt_suzukiChebyshevCenteredPNTWeight center hx).deriv

private theorem contDiffOn_suzukiChebyshevCenteredPNTWeight_Ioi
    (center : ℝ) :
    ContDiffOn ℝ 1 (suzukiChebyshevCenteredPNTWeight center)
      (Set.Ioi 0) := by
  intro x hx
  unfold suzukiChebyshevCenteredPNTWeight
  have hcenter : ContDiffAt ℝ 1 (fun _y : ℝ => center) x :=
    contDiffAt_const
  have hlog : ContDiffAt ℝ 1
      (fun y : ℝ => Real.log y - center) x :=
    (Real.contDiffAt_log.2 hx.ne').sub hcenter
  have hbracket : ContDiffAt ℝ 1
      (fun y : ℝ => 1 - (Real.log y - center) / 2) x :=
    contDiffAt_const.sub (hlog.div_const 2)
  exact
    ((Real.contDiffAt_rpow_const (n := 1) (Or.inl hx.ne'))
      |>.contDiffWithinAt).mul hbracket.contDiffWithinAt

/-- On every canonical first-tail prefix, the cumulative weight is bounded
below by one half of its pure inverse-power factor. -/
theorem half_rpow_le_suzukiChebyshevCenteredCumulativeWeight_on_firstTailPrefix
    (count : ℕ) {x : ℝ} (hxone : 1 ≤ x)
    (hxend : x ≤ ((count + 2 : ℕ) : ℝ)) :
    (1 / 2 : ℝ) * x ^ (-5 / 2 : ℝ) ≤
      suzukiChebyshevCenteredCumulativeWeight
        (suzukiFirstTailChebyshevCenter count) x := by
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  have hlog := Real.log_le_log hxpos hxend
  have hcenter :=
    log_endpoint_sub_two_le_suzukiFirstTailChebyshevCenter count
  have hfactor : (1 / 2 : ℝ) ≤
      2 - (3 / 4 : ℝ) *
        (Real.log x - suzukiFirstTailChebyshevCenter count) := by
    nlinarith
  unfold suzukiChebyshevCenteredCumulativeWeight
  simpa only [mul_comm] using
    (mul_le_mul_of_nonneg_left hfactor
      (Real.rpow_nonneg hxpos.le (-5 / 2 : ℝ)))

/-- The first PNT weight is nonnegative on every canonical prefix. -/
theorem suzukiChebyshevCenteredPNTWeight_nonneg_on_firstTailPrefix
    (count : ℕ) {x : ℝ} (hxone : 1 ≤ x)
    (hxend : x ≤ ((count + 2 : ℕ) : ℝ)) :
    0 ≤ suzukiChebyshevCenteredPNTWeight
      (suzukiFirstTailChebyshevCenter count) x := by
  rw [← deriv_suzukiChebyshevCenteredKernel_eq_pntWeight
    (suzukiFirstTailChebyshevCenter count)
    (zero_lt_one.trans_le hxone)]
  exact deriv_suzukiChebyshevCenteredKernel_nonneg_on_firstTailPrefix
    count hxone hxend

/-- Consequently the cumulative weight is strictly positive everywhere on
every complete canonical prefix. -/
theorem suzukiChebyshevCenteredCumulativeWeight_pos_on_firstTailPrefix
    (count : ℕ) {x : ℝ} (hxone : 1 ≤ x)
    (hxend : x ≤ ((count + 2 : ℕ) : ℝ)) :
    0 < suzukiChebyshevCenteredCumulativeWeight
      (suzukiFirstTailChebyshevCenter count) x := by
  have hlower :=
    half_rpow_le_suzukiChebyshevCenteredCumulativeWeight_on_firstTailPrefix
      count hxone hxend
  have hxpos : 0 < x := zero_lt_one.trans_le hxone
  exact (mul_pos (by norm_num) (Real.rpow_pos_of_pos hxpos _)).trans_le
    hlower

/-- The positive PNT weight is strictly decreasing throughout every
canonical prefix. -/
theorem strictAntiOn_suzukiChebyshevCenteredPNTWeight_firstTailPrefix
    (count : ℕ) :
    StrictAntiOn
      (suzukiChebyshevCenteredPNTWeight
        (suzukiFirstTailChebyshevCenter count))
      (Set.Icc 1 (((count + 2 : ℕ) : ℝ))) := by
  let r := suzukiFirstTailChebyshevCenter count
  let b : ℝ := ((count + 2 : ℕ) : ℝ)
  have hb : (1 : ℝ) < b := by
    dsimp only [b]
    exact_mod_cast (show 1 < count + 2 by omega)
  apply strictAntiOn_of_deriv_neg (convex_Icc (1 : ℝ) b)
  · apply
      (contDiffOn_suzukiChebyshevCenteredPNTWeight_Ioi r).continuousOn.mono
    intro x hx
    exact zero_lt_one.trans_le hx.1
  · intro x hx
    rw [interior_Icc] at hx
    have hpositive :=
      suzukiChebyshevCenteredCumulativeWeight_pos_on_firstTailPrefix
        count hx.1.le hx.2.le
    rw [deriv_suzukiChebyshevCenteredPNTWeight r
      (zero_lt_one.trans hx.1)]
    exact neg_neg_of_pos hpositive

/-! ## The cumulative Chebyshev error -/

/-- The first continuous primitive of the PNT error, based at one. -/
def suzukiChebyshevCumulativePNTError (x : ℝ) : ℝ :=
  ∫ y in (1 : ℝ)..x, (Chebyshev.psi y - y)

private theorem intervalIntegrable_chebyshevPsi
    {b : ℝ} (hb : 1 ≤ b) :
    IntervalIntegrable Chebyshev.psi volume 1 b := by
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
  exact hpsi'

private theorem intervalIntegrable_chebyshevPNTError
    {b : ℝ} (hb : 1 ≤ b) :
    IntervalIntegrable (fun x : ℝ => Chebyshev.psi x - x)
      volume 1 b :=
  (intervalIntegrable_chebyshevPsi hb).sub
    (continuous_id.intervalIntegrable 1 b)

/-- The cumulative PNT error is absolutely continuous on every forward
finite interval. -/
theorem absolutelyContinuousOnInterval_suzukiChebyshevCumulativePNTError
    {b : ℝ} (hb : 1 ≤ b) :
    AbsolutelyContinuousOnInterval
      suzukiChebyshevCumulativePNTError 1 b := by
  exact (intervalIntegrable_chebyshevPNTError hb)
    |>.absolutelyContinuousOnInterval_intervalIntegral (by
      rw [Set.uIcc_of_le hb]
      exact (show (1 : ℝ) ∈ Set.Icc 1 b from ⟨le_rfl, hb⟩))

/-- The cumulative PNT error vanishes at its base point. -/
@[simp] theorem suzukiChebyshevCumulativePNTError_one :
    suzukiChebyshevCumulativePNTError 1 = 0 := by
  simp [suzukiChebyshevCumulativePNTError]

/-! ## Exact arithmetic evaluation of the cumulative error -/

/-- The integral of `Chebyshev.psi` is its exact triangular von-Mangoldt
sum.  This is a finite Abel identity, valid at every real endpoint. -/
theorem integral_chebyshevPsi_eq_triangularVonMangoldtSum
    {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in (1 : ℝ)..b, Chebyshev.psi x) =
      ∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
        (b - (n : ℝ)) * ArithmeticFunction.vonMangoldt n := by
  have hintegrable : IntegrableOn
      (deriv (fun y : ℝ => b - y)) (Set.Icc 1 b) := by
    change IntegrableOn (deriv (b - ·)) (Set.Icc 1 b)
    rw [deriv_const_sub_id']
    exact continuousOn_const.integrableOn_Icc
  have habel := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (f := fun y : ℝ => b - y)
    (a := (1 : ℝ)) (b := b) (by norm_num) hb
    (fun _x _hx => by fun_prop) hintegrable
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at habel
  simp_rw [deriv_const_sub_id] at habel
  have hpsiOne : Chebyshev.psi (1 : ℝ) = 0 :=
    Chebyshev.psi_eq_zero_of_lt_two (by norm_num)
  rw [hpsiOne] at habel
  calc
    ∫ x in (1 : ℝ)..b, Chebyshev.psi x =
        ∫ x in (1 : ℝ)..b, -((-1 : ℝ) * Chebyshev.psi x) := by
          apply intervalIntegral.integral_congr
          intro x _hx
          ring
    _ = ∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
          (b - (n : ℝ)) * ArithmeticFunction.vonMangoldt n := by
      rw [intervalIntegral.integral_neg,
        intervalIntegral.integral_of_le hb]
      simpa only [Nat.floor_one, sub_self, zero_mul, mul_zero,
        zero_sub] using habel.symm

/-- The cumulative PNT error is an exact finite triangular von-Mangoldt sum
minus its continuous quadratic main term. -/
theorem suzukiChebyshevCumulativePNTError_eq_triangularVonMangoldtSum
    {b : ℝ} (hb : 1 ≤ b) :
    suzukiChebyshevCumulativePNTError b =
      (∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
          (b - (n : ℝ)) * ArithmeticFunction.vonMangoldt n) -
        (b ^ 2 - 1) / 2 := by
  unfold suzukiChebyshevCumulativePNTError
  have hsplit :
      (∫ y in (1 : ℝ)..b, (Chebyshev.psi y - y)) =
        (∫ y in (1 : ℝ)..b, Chebyshev.psi y) -
          ∫ y in (1 : ℝ)..b, y := by
    simpa only [Pi.sub_apply, id_eq] using
      (intervalIntegral.integral_sub
        (intervalIntegrable_chebyshevPsi hb)
        (continuous_id.intervalIntegrable 1 b))
  rw [hsplit,
    integral_chebyshevPsi_eq_triangularVonMangoldtSum hb,
    integral_id]
  ring

/-! ## A second rigorous Abel transform -/

private theorem
    absolutelyContinuousOnInterval_suzukiChebyshevCenteredPNTWeight
    (center : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    AbsolutelyContinuousOnInterval
      (suzukiChebyshevCenteredPNTWeight center) 1 b := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  apply
    (contDiffOn_suzukiChebyshevCenteredPNTWeight_Ioi center).mono
  intro x hx
  rw [Set.uIcc_of_le hb] at hx
  exact zero_lt_one.trans_le hx.1

/-- Exact integration by parts against the absolutely continuous cumulative
PNT error.  Both coefficients on the right are the positive kernels proved
above. -/
theorem integral_suzukiChebyshevCenteredPNTWeight_mul_error_eq_cumulative
    (center : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in Set.Ioc (1 : ℝ) b,
        suzukiChebyshevCenteredPNTWeight center x *
          (Chebyshev.psi x - x)) =
      suzukiChebyshevCenteredPNTWeight center b *
          suzukiChebyshevCumulativePNTError b +
        ∫ x in Set.Ioc (1 : ℝ) b,
          suzukiChebyshevCenteredCumulativeWeight center x *
            suzukiChebyshevCumulativePNTError x := by
  let E : ℝ → ℝ := fun x => Chebyshev.psi x - x
  let C : ℝ → ℝ := suzukiChebyshevCumulativePNTError
  let W : ℝ → ℝ := suzukiChebyshevCenteredPNTWeight center
  let V : ℝ → ℝ := suzukiChebyshevCenteredCumulativeWeight center
  have hE : IntervalIntegrable E volume 1 b := by
    exact intervalIntegrable_chebyshevPNTError hb
  have hC : AbsolutelyContinuousOnInterval C 1 b := by
    exact absolutelyContinuousOnInterval_suzukiChebyshevCumulativePNTError hb
  have hW : AbsolutelyContinuousOnInterval W 1 b := by
    exact
      absolutelyContinuousOnInterval_suzukiChebyshevCenteredPNTWeight
        center hb
  have hbase : (1 : ℝ) ∈ Set.uIcc 1 b := by
    rw [Set.uIcc_of_le hb]
    exact ⟨le_rfl, hb⟩
  have hderivC : ∀ᵐ x : ℝ ∂volume,
      x ∈ Set.uIoc 1 b → deriv C x = E x := by
    filter_upwards [hE.ae_hasDerivAt_integral] with x hx
    intro hxmem
    exact (hx (Set.uIoc_subset_uIcc hxmem) 1 hbase).deriv
  have hleft :
      (∫ x in (1 : ℝ)..b, W x * deriv C x) =
        ∫ x in (1 : ℝ)..b, W x * E x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderivC] with x hx hxmem
    rw [hx hxmem]
  have hright :
      (∫ x in (1 : ℝ)..b, deriv W x * C x) =
        -∫ x in (1 : ℝ)..b, V x * C x := by
    calc
      (∫ x in (1 : ℝ)..b, deriv W x * C x) =
          ∫ x in (1 : ℝ)..b, -(V x * C x) := by
            apply intervalIntegral.integral_congr
            intro x hx
            have hxIcc : x ∈ Set.Icc (1 : ℝ) b := by
              rw [Set.uIcc_of_le hb] at hx
              exact hx
            have hxpos : 0 < x := zero_lt_one.trans_le hxIcc.1
            change deriv W x * C x = -(V x * C x)
            rw [show deriv W x = -V x by
              exact deriv_suzukiChebyshevCenteredPNTWeight center hxpos]
            ring
      _ = -∫ x in (1 : ℝ)..b, V x * C x := by
        exact intervalIntegral.integral_neg
  have hparts := hW.integral_mul_deriv_eq_deriv_mul hC
  rw [hleft, hright] at hparts
  have hCOne : C 1 = 0 := by
    exact suzukiChebyshevCumulativePNTError_one
  rw [hCOne, mul_zero, sub_zero] at hparts
  dsimp only [E, C, W, V] at hparts ⊢
  simpa only [sub_neg_eq_add, intervalIntegral.integral_of_le hb]
    using hparts

/-- The first integral in the terminal frontier can therefore be replaced
exactly by a boundary value of the cumulative error plus a second positive
kernel moment. -/
theorem
    integral_deriv_suzukiChebyshevCenteredKernel_mul_error_eq_cumulative
    (center : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in Set.Ioc (1 : ℝ) b,
        deriv (suzukiChebyshevCenteredKernel center) x *
          (Chebyshev.psi x - x)) =
      suzukiChebyshevCenteredPNTWeight center b *
          suzukiChebyshevCumulativePNTError b +
        ∫ x in Set.Ioc (1 : ℝ) b,
          suzukiChebyshevCenteredCumulativeWeight center x *
            suzukiChebyshevCumulativePNTError x := by
  calc
    (∫ x in Set.Ioc (1 : ℝ) b,
        deriv (suzukiChebyshevCenteredKernel center) x *
          (Chebyshev.psi x - x)) =
        ∫ x in Set.Ioc (1 : ℝ) b,
          suzukiChebyshevCenteredPNTWeight center x *
            (Chebyshev.psi x - x) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      change deriv (suzukiChebyshevCenteredKernel center) x *
          (Chebyshev.psi x - x) =
        suzukiChebyshevCenteredPNTWeight center x *
          (Chebyshev.psi x - x)
      rw [deriv_suzukiChebyshevCenteredKernel_eq_pntWeight center
        (zero_lt_one.trans hx.1)]
    _ = _ :=
      integral_suzukiChebyshevCenteredPNTWeight_mul_error_eq_cumulative
        center hb

/-! ## The cumulative-error terminal frontier -/

/-- Final two-level positive-kernel form.  Tail positivity is exactly an
upper bound on one endpoint value and one moment of the cumulative PNT error.
The endpoint coefficient is nonnegative and the integral coefficient is
strictly positive on every canonical prefix by the theorems above. -/
theorem
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_chebyshevCumulativePNTPositiveKernelMoment :
    (∀ t : ℝ, Real.log 2 ≤ t →
      0 ≤ riemannXiSuzukiPsiNonnegative t) ↔
      ∀ count : ℕ, 1 ≤ count →
        suzukiChebyshevCenteredPNTWeight
              (suzukiFirstTailChebyshevCenter count)
              ((count + 2 : ℕ) : ℝ) *
            suzukiChebyshevCumulativePNTError
              ((count + 2 : ℕ) : ℝ) +
          (∫ x in Set.Ioc (1 : ℝ) ((count + 2 : ℕ) : ℝ),
            suzukiChebyshevCenteredCumulativeWeight
                (suzukiFirstTailChebyshevCenter count) x *
              suzukiChebyshevCumulativePNTError x) ≤
          suzukiChebyshevCenteredKernel
              (suzukiFirstTailChebyshevCenter count)
              ((count + 2 : ℕ) : ℝ) *
            (Chebyshev.psi ((count + 2 : ℕ) : ℝ) -
              ((count + 2 : ℕ) : ℝ)) +
          suzukiPointwiseArchimedean
              (suzukiFirstTailChebyshevCenter count) +
          2 * ((((count + 2 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) *
            (Real.log ((count + 2 : ℕ) : ℝ) -
              suzukiFirstTailChebyshevCenter count - 2)) +
          suzukiFirstTailChebyshevCenter count + 4 := by
  rw [
    riemannXiSuzukiPsiNonnegative_on_logTwo_tail_iff_chebyshevPNTPositiveKernelMoment]
  constructor
  · intro hmoments count hcount
    have hmoment := hmoments count hcount
    have hb : (1 : ℝ) ≤ ((count + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ count + 2 by omega)
    rw [
      integral_deriv_suzukiChebyshevCenteredKernel_mul_error_eq_cumulative
        (suzukiFirstTailChebyshevCenter count) hb] at hmoment
    exact hmoment
  · intro hmoments count hcount
    have hmoment := hmoments count hcount
    have hb : (1 : ℝ) ≤ ((count + 2 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ count + 2 by omega)
    rw [
      integral_deriv_suzukiChebyshevCenteredKernel_mul_error_eq_cumulative
        (suzukiFirstTailChebyshevCenter count) hb]
    exact hmoment

end

end RiemannGaussian
