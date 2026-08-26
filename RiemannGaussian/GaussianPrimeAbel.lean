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
transport formulations.  The final section passes natural cutoffs to
infinity: Gaussian decay kills the Chebyshev boundary using Mathlib's
explicit linear bound for `psi`, and the resulting improper error integrals
converge to the full forward discrepancy.
-/

namespace RiemannGaussian

noncomputable section

open Filter MeasureTheory Topology
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

/-! ## Passage to the infinite forward discrepancy -/

/-- The natural finite prime-energy blocks exhaust the complete atomic
von-Mangoldt energy. -/
theorem tendsto_gaussianPrimePartialOscillationEnergy_Ioc
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        gaussianPrimePartialOscillationEnergy ε t (Finset.Ioc 1 n))
      atTop (𝓝 (gaussianPrimeOscillationEnergy ε t)) := by
  have hsum (n : ℕ) (hn : 1 ≤ n) :
      (∑ k ∈ Finset.Ioc 1 n,
        gaussianPrimeOscillationSummand ε t k) =
      ∑ k ∈ Finset.range (n + 1),
        gaussianPrimeOscillationSummand ε t k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Ioc, Finset.mem_range] at hk ⊢
      omega
    · intro k hkrange hknot
      simp only [Finset.mem_range] at hkrange
      simp only [Finset.mem_Ioc, not_and_or, not_lt] at hknot
      have hk : k = 0 ∨ k = 1 := by omega
      rcases hk with rfl | rfl <;>
        simp [gaussianPrimeOscillationSummand_eq]
  have htendsto : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n,
        gaussianPrimeOscillationSummand ε t k)
      atTop (𝓝 (∑' k : ℕ,
        gaussianPrimeOscillationSummand ε t k)) :=
    (summable_gaussianPrimeOscillationSummand hε t).hasSum.tendsto_sum_nat
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hraw := htendsto.comp hshift
  unfold gaussianPrimePartialOscillationEnergy
    gaussianPrimeOscillationEnergy
  apply Tendsto.const_mul
  apply hraw.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (hsum n hn).symm

/-- The positive-log continuous comparison is exhausted by logarithmic
intervals whose multiplicative endpoints tend to infinity. -/
theorem tendsto_gaussianForwardContinuousPrimeOscillationEnergy_logInterval
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        2 / Real.sqrt (Real.pi * ε) *
          ∫ u in (0 : ℝ)..Real.log (n : ℝ),
            Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
              (1 - Real.cos (t * u)))
      atTop
      (𝓝 (gaussianForwardContinuousPrimeOscillationEnergy ε t)) := by
  let f : ℝ → ℝ := fun u =>
    Real.exp (u / 2 - u ^ 2 / (4 * ε)) *
      (1 - Real.cos (t * u))
  have hf : IntegrableOn f (Set.Ioi 0) :=
    (gaussianContinuousPrimeOscillationIntegrable hε t).integrableOn
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hint := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hf hlog
  unfold gaussianForwardContinuousPrimeOscillationEnergy
  exact hint.const_mul _

/-- The finite Abel discrepancies converge to the full one-sided PNT
discrepancy. -/
theorem tendsto_gaussianPrimeFiniteForwardEnergyDiscrepancy
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        gaussianPrimeFiniteForwardEnergyDiscrepancy ε t (n : ℝ))
      atTop (𝓝 (gaussianForwardPrimeEnergyDiscrepancy ε t)) := by
  have hprime := tendsto_gaussianPrimePartialOscillationEnergy_Ioc hε t
  have hcontinuous :=
    tendsto_gaussianForwardContinuousPrimeOscillationEnergy_logInterval hε t
  have hsub := hprime.sub hcontinuous
  unfold gaussianForwardPrimeEnergyDiscrepancy
  apply hsub.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [gaussianPrimeFiniteForwardEnergyDiscrepancy_eq_logInterval ε t]
  · simp
  · exact_mod_cast hn

/-- Logarithmic form of the Abel kernel at an exponential argument. -/
lemma gaussianPrimeAbelKernel_exp (ε t T : ℝ) :
    gaussianPrimeAbelKernel ε t (Real.exp T) =
      Real.exp (-T / 2 - T ^ 2 / (4 * ε)) *
        (1 - Real.cos (t * T)) := by
  unfold gaussianPrimeAbelKernel
  rw [Real.log_exp, ← Real.exp_half]
  rw [div_eq_mul_inv, one_mul, ← Real.exp_neg]
  rw [← Real.exp_add]
  congr 2
  ring

/-- Gaussian decay beats the linear Chebyshev bound, so the Abel boundary
term vanishes along exponential endpoints. -/
theorem tendsto_gaussianPrimeAbelBoundary_exp
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Tendsto
      (fun T : ℝ =>
        gaussianPrimeAbelKernel ε t (Real.exp T) *
          (Chebyshev.psi (Real.exp T) - Real.exp T))
      atTop (𝓝 0) := by
  let A : ℝ := Real.log 4 + 5
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have herror (T : ℝ) :
      |Chebyshev.psi (Real.exp T) - Real.exp T| ≤
        A * Real.exp T := by
    calc
      |Chebyshev.psi (Real.exp T) - Real.exp T| ≤
          |Chebyshev.psi (Real.exp T)| + |Real.exp T| := abs_sub _ _
      _ = Chebyshev.psi (Real.exp T) + Real.exp T := by
        rw [abs_of_nonneg (Chebyshev.psi_nonneg _),
          abs_of_pos (Real.exp_pos _)]
      _ ≤ (Real.log 4 + 4) * Real.exp T + Real.exp T := by
        gcongr
        exact Chebyshev.psi_le_const_mul_self (Real.exp_pos T).le
      _ = A * Real.exp T := by
        dsimp only [A]
        ring
  have hosc (T : ℝ) :
      0 ≤ 1 - Real.cos (t * T) ∧
        1 - Real.cos (t * T) ≤ 2 := by
    constructor
    · exact sub_nonneg.mpr (Real.cos_le_one _)
    · linarith [Real.neg_one_le_cos (t * T)]
  have hbound : ∀ T : ℝ,
      ‖gaussianPrimeAbelKernel ε t (Real.exp T) *
          (Chebyshev.psi (Real.exp T) - Real.exp T)‖ ≤
        (2 * A) * Real.exp (-T ^ 2 / (4 * ε) + T / 2) := by
    intro T
    rw [gaussianPrimeAbelKernel_exp]
    simp only [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg (hosc T).1]
    calc
      Real.exp (-T / 2 - T ^ 2 / (4 * ε)) *
            (1 - Real.cos (t * T)) *
          |Chebyshev.psi (Real.exp T) - Real.exp T| ≤
        Real.exp (-T / 2 - T ^ 2 / (4 * ε)) * 2 *
          (A * Real.exp T) := by
            gcongr
            · exact (hosc T).2
            · exact herror T
      _ = (2 * A) * Real.exp (-T ^ 2 / (4 * ε) + T / 2) := by
        calc
          _ = (2 * A) *
              (Real.exp (-T / 2 - T ^ 2 / (4 * ε)) * Real.exp T) := by ring
          _ = _ := by
            rw [← Real.exp_add]
            congr 2
            ring
  have hdecay : Tendsto
      (fun T : ℝ => (2 * A) *
        Real.exp (-T ^ 2 / (4 * ε) + T / 2))
      atTop (𝓝 0) := by
    have h := tendsto_exp_neg_quadratic_add_linear_atTop
      (ε := 1 / (4 * ε)) (by positivity) 0 (1 / 2) 0
    have h' : Tendsto
        (fun T : ℝ => (2 * A) *
          Real.exp (-(1 / (4 * ε)) * (T - 0) ^ 2 + (1 / 2) * T + 0))
        atTop (𝓝 0) := by
      simpa using h.const_mul (2 * A)
    apply h'.congr'
    filter_upwards with T
    congr 2
    field_simp [hε.ne']
    ring
  exact squeeze_zero_norm' (Filter.Eventually.of_forall hbound) hdecay

/-- The same Abel boundary term vanishes at natural cutoffs. -/
theorem tendsto_gaussianPrimeAbelBoundary_nat
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        gaussianPrimeAbelKernel ε t (n : ℝ) *
          (Chebyshev.psi (n : ℝ) - (n : ℝ)))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (tendsto_gaussianPrimeAbelBoundary_exp hε t).comp hlog
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  simp only [Function.comp_apply, Real.exp_log hnpos]

/-- Unconditional infinite-cutoff Abel formula: the normalized explicit
Chebyshev-error integrals converge to the full forward prime discrepancy.
This is stated as an improper-integral limit; absolute integrability of the
signed error kernel is not needed for the identity. -/
theorem tendsto_gaussianPrimeExplicitChebyshevErrorIntegral
    {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Tendsto
      (fun n : ℕ =>
        2 / Real.sqrt (Real.pi * ε) *
          ∫ x in Set.Ioc (1 : ℝ) (n : ℝ),
            gaussianPrimeAbelKernelDerivative ε t x *
              (x - Chebyshev.psi x))
      atTop (𝓝 (gaussianForwardPrimeEnergyDiscrepancy ε t)) := by
  have hfinite :=
    tendsto_gaussianPrimeFiniteForwardEnergyDiscrepancy hε t
  have hboundary :=
    (tendsto_gaussianPrimeAbelBoundary_nat hε t).const_mul
      (2 / Real.sqrt (Real.pi * ε))
  have hsub := hfinite.sub hboundary
  have heq :
      (fun n : ℕ =>
        gaussianPrimeFiniteForwardEnergyDiscrepancy ε t (n : ℝ) -
          2 / Real.sqrt (Real.pi * ε) *
            (gaussianPrimeAbelKernel ε t (n : ℝ) *
              (Chebyshev.psi (n : ℝ) - (n : ℝ)))) =ᶠ[atTop]
      (fun n : ℕ =>
        2 / Real.sqrt (Real.pi * ε) *
          ∫ x in Set.Ioc (1 : ℝ) (n : ℝ),
            gaussianPrimeAbelKernelDerivative ε t x *
              (x - Chebyshev.psi x)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [gaussianPrimeFiniteForwardEnergyDiscrepancy_eq_explicitChebyshevErrorIntegral
      hε t hnreal]
    ring
  have hresult := hsub.congr' heq
  simpa using hresult

end

end RiemannGaussian
