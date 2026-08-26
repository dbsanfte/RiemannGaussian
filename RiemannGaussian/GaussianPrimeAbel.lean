import RiemannGaussian.GaussianPrimeDiscrepancy
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Abel summation for the forward Gaussian prime discrepancy

The bilateral continuous main term has already been split into its natural
positive-log PNT part and a reflected Archimedean correction.  This file
turns every finite truncation of the forward atomic-minus-continuous
discrepancy into a classical Chebyshev-error integral.

For the exact Gaussian test kernel `K`, Abel summation gives

`sum_{n ≤ b} Lambda(n) K(n) - integral_1^b K(x) dx`

as a boundary term involving `psi(b) - b` plus the integral of the explicit
signed derivative `K'(x)` against `x - psi(x)`.  This is the precise bridge
from the Gaussian positivity frontier to the weighted-Chebyshev and screw
transport formulations.  Passing this finite identity to `b → ∞` remains a
separate analytic step.
-/

namespace RiemannGaussian

noncomputable section

open MeasureTheory
open scoped BigOperators Topology

/-! ## The multiplicative Gaussian test kernel -/

/-- The forward Gaussian oscillation kernel after the change of variables
`x = exp u`.  Multiplication by `Lambda(n)` gives exactly the unnormalized
prime-energy summand. -/
def gaussianPrimeAbelKernel (ε t x : ℝ) : ℝ :=
  1 / Real.sqrt x *
    Real.exp (-(Real.log x) ^ 2 / (4 * ε)) *
      (1 - Real.cos (t * Real.log x))

/-- Closed derivative of the multiplicative Gaussian test kernel. -/
def gaussianPrimeAbelKernelDerivative (ε t x : ℝ) : ℝ :=
  Real.exp (-(Real.log x) ^ 2 / (4 * ε)) /
      (x * Real.sqrt x) *
    (t * Real.sin (t * Real.log x) -
      (1 / 2 + Real.log x / (2 * ε)) *
        (1 - Real.cos (t * Real.log x)))

theorem hasDerivAt_gaussianPrimeAbelKernel
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (gaussianPrimeAbelKernel ε t)
      (gaussianPrimeAbelKernelDerivative ε t x) x := by
  have hxne : x ≠ 0 := hx.ne'
  have hsqrtne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hlog := Real.hasDerivAt_log hxne
  have hsqrt := Real.hasDerivAt_sqrt hxne
  have hinvSqrt := (hasDerivAt_const x (1 : ℝ)).div hsqrt hsqrtne
  have hgaussianExponent := ((hlog.pow 2).neg.div_const (4 * ε))
  have hgaussian := hgaussianExponent.exp
  have hphase := ((hasDerivAt_const x t).mul hlog).cos
  have hoscillation := (hasDerivAt_const x (1 : ℝ)).sub hphase
  have hproduct := (hinvSqrt.mul hgaussian).mul hoscillation
  change HasDerivAt (gaussianPrimeAbelKernel ε t) _ x at hproduct
  apply hproduct.congr_deriv
  unfold gaussianPrimeAbelKernelDerivative
  simp only [Pi.div_apply, Pi.mul_apply, Pi.sub_apply, Nat.cast_ofNat,
    zero_mul, zero_add, one_mul]
  field_simp [hε.ne', hxne, hsqrtne]
  ring_nf
  rw [Real.sq_sqrt hx.le]
  have hexp :
      Real.exp ((-Real.log ^ 2) x * ε⁻¹ * (1 / 4)) =
        Real.exp (ε⁻¹ * Real.log x ^ 2 * (-1 / 4)) := by
    congr 1
    dsimp
    ring
  rw [hexp]
  ring

theorem deriv_gaussianPrimeAbelKernel
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    deriv (gaussianPrimeAbelKernel ε t) x =
      gaussianPrimeAbelKernelDerivative ε t x :=
  (hasDerivAt_gaussianPrimeAbelKernel hε t hx).deriv

theorem differentiableAt_gaussianPrimeAbelKernel
    (ε t : ℝ) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (gaussianPrimeAbelKernel ε t) x := by
  have hxne : x ≠ 0 := hx.ne'
  have hsqrtne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  unfold gaussianPrimeAbelKernel
  fun_prop

/-- The kernel derivative is integrable on every finite PNT interval. -/
theorem integrableOn_deriv_gaussianPrimeAbelKernel_Icc
    (ε t b : ℝ) :
    IntegrableOn (deriv (gaussianPrimeAbelKernel ε t))
      (Set.Icc (1 : ℝ) b) := by
  have hsmooth : ContDiffOn ℝ 2 (gaussianPrimeAbelKernel ε t)
      (Set.Ioi 0) := by
    intro x hx
    have hxne : x ≠ 0 := hx.ne'
    have hsqrtne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
    have hlog : ContDiffWithinAt ℝ 2 Real.log (Set.Ioi 0) x :=
      (Real.contDiffAt_log.2 hxne).contDiffWithinAt
    have hsqrt : ContDiffWithinAt ℝ 2 (fun y : ℝ => Real.sqrt y)
        (Set.Ioi 0) x :=
      (Real.contDiffAt_sqrt hxne).contDiffWithinAt
    have hinvSqrt : ContDiffWithinAt ℝ 2 (fun y : ℝ => 1 / Real.sqrt y)
        (Set.Ioi 0) x :=
      contDiffWithinAt_const.div hsqrt hsqrtne
    have hgaussianExponent : ContDiffWithinAt ℝ 2
        (fun y : ℝ => -(Real.log y) ^ 2 / (4 * ε)) (Set.Ioi 0) x :=
      (hlog.pow 2).neg.div_const _
    have hgaussian : ContDiffWithinAt ℝ 2
        (fun y : ℝ => Real.exp (-(Real.log y) ^ 2 / (4 * ε)))
        (Set.Ioi 0) x :=
      hgaussianExponent.exp
    have hphase : ContDiffWithinAt ℝ 2
        (fun y : ℝ => t * Real.log y) (Set.Ioi 0) x :=
      contDiffWithinAt_const.mul hlog
    have hcosine : ContDiffWithinAt ℝ 2
        (fun y : ℝ => Real.cos (t * Real.log y)) (Set.Ioi 0) x :=
      hphase.cos
    exact (hinvSqrt.mul hgaussian).mul
      (contDiffWithinAt_const.sub hcosine)
  have hcontinuous : ContinuousOn (deriv (gaussianPrimeAbelKernel ε t))
      (Set.Ioi 0) :=
    hsmooth.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hsubset : Set.Icc (1 : ℝ) b ⊆ Set.Ioi 0 := by
    intro x hx
    exact zero_lt_one.trans_le hx.1
  exact (hcontinuous.mono hsubset).integrableOn_Icc

/-! ## Finite Abel summation and the Chebyshev error -/

/-- Abel summation specialized to von Mangoldt and the Gaussian kernel. -/
theorem gaussianPrimeAbelSum_eq
    (ε t : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    ∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
        gaussianPrimeAbelKernel ε t n *
          ArithmeticFunction.vonMangoldt n =
      gaussianPrimeAbelKernel ε t b * Chebyshev.psi b -
        ∫ x in Set.Ioc (1 : ℝ) b,
          deriv (gaussianPrimeAbelKernel ε t) x * Chebyshev.psi x := by
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (a := (1 : ℝ)) (b := b) (by norm_num) hb
    (fun x hx => differentiableAt_gaussianPrimeAbelKernel ε t
      (zero_lt_one.trans_le hx.1))
    (integrableOn_deriv_gaussianPrimeAbelKernel_Icc ε t b)
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at h
  simpa [gaussianPrimeAbelKernel] using h

/-- Ordinary integration by parts for the same kernel. -/
theorem gaussianPrimeAbelKernel_integral_Ioc
    (ε t : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in Set.Ioc (1 : ℝ) b, gaussianPrimeAbelKernel ε t x) =
      b * gaussianPrimeAbelKernel ε t b -
        ∫ x in Set.Ioc (1 : ℝ) b,
          x * deriv (gaussianPrimeAbelKernel ε t) x := by
  have hderivInterval : IntervalIntegrable
      (deriv (gaussianPrimeAbelKernel ε t)) volume 1 b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hb]
    exact integrableOn_deriv_gaussianPrimeAbelKernel_Icc ε t b
  have hconstant : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 1 b :=
    intervalIntegrable_const
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (1 : ℝ)) (b := b)
    (u := gaussianPrimeAbelKernel ε t)
    (u' := deriv (gaussianPrimeAbelKernel ε t))
    (v := fun x : ℝ => x) (v' := fun _ : ℝ => 1)
    (fun x hx => by
      rw [Set.uIcc_of_le hb] at hx
      exact (differentiableAt_gaussianPrimeAbelKernel ε t
        (zero_lt_one.trans_le hx.1)).hasDerivAt)
    (fun x _ => hasDerivAt_id x) hderivInterval hconstant
  rw [intervalIntegral.integral_of_le hb,
    intervalIntegral.integral_of_le hb] at hip
  simpa [gaussianPrimeAbelKernel, mul_comm] using hip

/-- Finite atomic-minus-continuous discrepancy after Abel summation. -/
theorem gaussianPrimeFiniteForwardDiscrepancy_eq
    (ε t : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    (∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
        gaussianPrimeAbelKernel ε t n *
          ArithmeticFunction.vonMangoldt n) -
        (∫ x in Set.Ioc (1 : ℝ) b,
          gaussianPrimeAbelKernel ε t x) =
      gaussianPrimeAbelKernel ε t b * (Chebyshev.psi b - b) +
        (∫ x in Set.Ioc (1 : ℝ) b,
          x * deriv (gaussianPrimeAbelKernel ε t) x) -
        ∫ x in Set.Ioc (1 : ℝ) b,
          deriv (gaussianPrimeAbelKernel ε t) x * Chebyshev.psi x := by
  rw [gaussianPrimeAbelSum_eq ε t hb,
    gaussianPrimeAbelKernel_integral_Ioc ε t hb]
  ring

/-- The same discrepancy paired directly with the classical PNT error. -/
theorem gaussianPrimeFiniteForwardDiscrepancy_eq_chebyshevErrorIntegral
    (ε t : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    (∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
        gaussianPrimeAbelKernel ε t n *
          ArithmeticFunction.vonMangoldt n) -
        (∫ x in Set.Ioc (1 : ℝ) b,
          gaussianPrimeAbelKernel ε t x) =
      gaussianPrimeAbelKernel ε t b * (Chebyshev.psi b - b) +
        ∫ x in Set.Ioc (1 : ℝ) b,
          deriv (gaussianPrimeAbelKernel ε t) x *
            (x - Chebyshev.psi x) := by
  have hderiv := integrableOn_deriv_gaussianPrimeAbelKernel_Icc ε t b
  have hxderivIcc : IntegrableOn
      (fun x : ℝ => x * deriv (gaussianPrimeAbelKernel ε t) x)
      (Set.Icc (1 : ℝ) b) :=
    MeasureTheory.IntegrableOn.continuousOn_mul
      continuous_id.continuousOn hderiv isCompact_Icc
  have hxderiv := hxderivIcc.mono_set Set.Ioc_subset_Icc_self
  have hpsiIcc := integrableOn_mul_sum_Icc
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n)
    (a := (1 : ℝ)) (b := b) (m := 0) (by norm_num) hderiv
  simp_rw [← Chebyshev.psi_eq_sum_Icc] at hpsiIcc
  have hpsi := hpsiIcc.mono_set Set.Ioc_subset_Icc_self
  have hintegral :
      (∫ x in Set.Ioc (1 : ℝ) b,
          x * deriv (gaussianPrimeAbelKernel ε t) x) -
        (∫ x in Set.Ioc (1 : ℝ) b,
          deriv (gaussianPrimeAbelKernel ε t) x * Chebyshev.psi x) =
        ∫ x in Set.Ioc (1 : ℝ) b,
          deriv (gaussianPrimeAbelKernel ε t) x *
            (x - Chebyshev.psi x) := by
    rw [← integral_sub hxderiv hpsi]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _
    ring
  rw [gaussianPrimeFiniteForwardDiscrepancy_eq ε t hb]
  linarith

/-- The finite discrepancy as one explicit signed Gaussian kernel paired
with the classical PNT error `x - psi(x)`. -/
theorem gaussianPrimeFiniteForwardDiscrepancy_eq_explicitChebyshevErrorIntegral
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    (∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
        gaussianPrimeAbelKernel ε t n *
          ArithmeticFunction.vonMangoldt n) -
        (∫ x in Set.Ioc (1 : ℝ) b,
          gaussianPrimeAbelKernel ε t x) =
      gaussianPrimeAbelKernel ε t b * (Chebyshev.psi b - b) +
        ∫ x in Set.Ioc (1 : ℝ) b,
          gaussianPrimeAbelKernelDerivative ε t x *
            (x - Chebyshev.psi x) := by
  rw [gaussianPrimeFiniteForwardDiscrepancy_eq_chebyshevErrorIntegral
    ε t hb]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  dsimp only
  rw [deriv_gaussianPrimeAbelKernel hε t
    (zero_lt_one.trans hx.1)]

/-! ## Compatibility with logarithmic and project energy coordinates -/

/-- The multiplicative kernel integral is exactly the positive-log
continuous Gaussian integral under `x = exp u`. -/
theorem gaussianPrimeAbelKernel_intervalIntegral_eq_log
    (ε t : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in (1 : ℝ)..b, gaussianPrimeAbelKernel ε t x) =
      ∫ u in (0 : ℝ)..Real.log b,
        Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
          (1 - Real.cos (t * u)) := by
  have hkernel : ContinuousOn (gaussianPrimeAbelKernel ε t)
      (Real.exp '' Set.uIcc (0 : ℝ) (Real.log b)) := by
    intro x hx
    obtain ⟨u, _, rfl⟩ := hx
    exact (differentiableAt_gaussianPrimeAbelKernel ε t
      (Real.exp_pos u)).continuousAt.continuousWithinAt
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := Real.log b)
    (f := Real.exp) (f' := Real.exp)
    (g := gaussianPrimeAbelKernel ε t)
    (fun u _ => Real.hasDerivAt_exp u)
    Real.continuous_exp.continuousOn hkernel
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  rw [Real.exp_zero, Real.exp_log hbpos] at hsubst
  have hpoint (u : ℝ) :
      gaussianPrimeAbelKernel ε t (Real.exp u) * Real.exp u =
        Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
          (1 - Real.cos (t * u)) := by
    unfold gaussianPrimeAbelKernel
    rw [Real.log_exp, ← Real.exp_half]
    have hexpSplit :
        Real.exp u = Real.exp (u / 2) * Real.exp (u / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hexpCombined :
        Real.exp (u / 2 - u ^ 2 / (4 * ε)) =
          Real.exp (u / 2) * Real.exp (-(u ^ 2 / (4 * ε))) := by
      rw [← Real.exp_add]
      congr 1
    rw [hexpSplit, hexpCombined]
    field_simp [Real.exp_ne_zero]
  simp_rw [Function.comp_apply, hpoint] at hsubst
  exact hsubst.symm

/-- The finite von-Mangoldt sum is the existing partial prime energy. -/
theorem gaussianPrimePartialOscillationEnergy_Ioc_eq_abelSum
    (ε t b : ℝ) :
    gaussianPrimePartialOscillationEnergy ε t (Finset.Ioc 1 ⌊b⌋₊) =
      2 / Real.sqrt (Real.pi * ε) *
        ∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
          gaussianPrimeAbelKernel ε t n *
            ArithmeticFunction.vonMangoldt n := by
  unfold gaussianPrimePartialOscillationEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  rw [gaussianPrimeOscillationSummand_eq]
  unfold gaussianPrimeAbelKernel
  ring

/-- A finite normalized approximation to the full forward PNT discrepancy. -/
def gaussianPrimeFiniteForwardEnergyDiscrepancy
    (ε t b : ℝ) : ℝ :=
  2 / Real.sqrt (Real.pi * ε) *
    ((∑ n ∈ Finset.Ioc 1 ⌊b⌋₊,
      gaussianPrimeAbelKernel ε t n *
        ArithmeticFunction.vonMangoldt n) -
      ∫ x in Set.Ioc (1 : ℝ) b,
        gaussianPrimeAbelKernel ε t x)

theorem gaussianPrimeFiniteForwardEnergyDiscrepancy_eq_partial_sub_continuous
    (ε t b : ℝ) :
    gaussianPrimeFiniteForwardEnergyDiscrepancy ε t b =
      gaussianPrimePartialOscillationEnergy ε t (Finset.Ioc 1 ⌊b⌋₊) -
        2 / Real.sqrt (Real.pi * ε) *
          ∫ x in Set.Ioc (1 : ℝ) b,
            gaussianPrimeAbelKernel ε t x := by
  unfold gaussianPrimeFiniteForwardEnergyDiscrepancy
  rw [gaussianPrimePartialOscillationEnergy_Ioc_eq_abelSum]
  ring

theorem gaussianPrimeFiniteForwardEnergyDiscrepancy_eq_logInterval
    (ε t : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    gaussianPrimeFiniteForwardEnergyDiscrepancy ε t b =
      gaussianPrimePartialOscillationEnergy ε t (Finset.Ioc 1 ⌊b⌋₊) -
        2 / Real.sqrt (Real.pi * ε) *
          ∫ u in (0 : ℝ)..Real.log b,
            Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
              (1 - Real.cos (t * u)) := by
  rw [gaussianPrimeFiniteForwardEnergyDiscrepancy_eq_partial_sub_continuous]
  rw [← intervalIntegral.integral_of_le hb]
  rw [gaussianPrimeAbelKernel_intervalIntegral_eq_log ε t hb]

theorem gaussianPrimeFiniteForwardEnergyDiscrepancy_eq_abel
    (ε t : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    gaussianPrimeFiniteForwardEnergyDiscrepancy ε t b =
      2 / Real.sqrt (Real.pi * ε) *
        (gaussianPrimeAbelKernel ε t b * (Chebyshev.psi b - b) +
          (∫ x in Set.Ioc (1 : ℝ) b,
            x * deriv (gaussianPrimeAbelKernel ε t) x) -
          ∫ x in Set.Ioc (1 : ℝ) b,
            deriv (gaussianPrimeAbelKernel ε t) x * Chebyshev.psi x) := by
  unfold gaussianPrimeFiniteForwardEnergyDiscrepancy
  rw [gaussianPrimeFiniteForwardDiscrepancy_eq ε t hb]

/-- Final finite PNT-error form with every analytic kernel explicit. -/
theorem gaussianPrimeFiniteForwardEnergyDiscrepancy_eq_explicitChebyshevErrorIntegral
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) {b : ℝ} (hb : 1 ≤ b) :
    gaussianPrimeFiniteForwardEnergyDiscrepancy ε t b =
      2 / Real.sqrt (Real.pi * ε) *
        (gaussianPrimeAbelKernel ε t b * (Chebyshev.psi b - b) +
          ∫ x in Set.Ioc (1 : ℝ) b,
            gaussianPrimeAbelKernelDerivative ε t x *
              (x - Chebyshev.psi x)) := by
  unfold gaussianPrimeFiniteForwardEnergyDiscrepancy
  rw [gaussianPrimeFiniteForwardDiscrepancy_eq_explicitChebyshevErrorIntegral
    hε t hb]

end

end RiemannGaussian
