import RiemannGaussian.RiemannXiSuzukiPositiveCriticalStripEtaFiniteApproximation

/-!
# Finite paired-eta arithmetic fluxes on the detector circles

This module pulls the locally uniform finite paired-eta approximation back to
the compact zero-free circles selected by the diagonal heat-flux construction.
Uniform nonvanishing of the limiting eta core supplies an eventual positive
denominator margin for every finite eta polynomial on each circle.

The finite logarithmic quotients therefore converge uniformly after insertion
of the genuine Gaussian heat weight, and their radial integrands are genuinely
interval integrable. Lean passes the finite truncation limit through every
circle integral and every finite spectral window.

Finally, one growing truncation index is selected at each existing diagonal
window. The resulting single sequence uses only finite paired-eta Dirichlet
polynomials at every stage and converges to `2 * pi` times the complete
boundary-heat detector. This is an approximation theorem, not the missing
arithmetic estimate forcing that detector to vanish.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- The explicit finite derivative polynomial is continuous on the whole
complex plane. -/
theorem continuous_pairedEtaCoreDerivativePartialSum (N : ℕ) :
    Continuous (pairedEtaCoreDerivativePartialSum N) := by
  have hdiff : Differentiable ℂ (pairedEtaCoreDerivativePartialSum N) := by
    unfold pairedEtaCoreDerivativePartialSum
    apply Differentiable.fun_sum
    intro n _
    unfold pairedEtaCoreDerivativeSummand
    have hodd : ((((2 * n + 1 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show 2 * n + 1 ≠ 0 by omega)
    have heven : ((((2 * n + 2 : ℕ) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast (show 2 * n + 2 ≠ 0 by omega)
    exact
      ((Differentiable.const_cpow (Differentiable.neg differentiable_id)
          (Or.inl hodd)).const_mul
        (-Complex.log ((((2 * n + 1 : ℕ) : ℝ) : ℂ)))).add
        ((Differentiable.const_cpow (Differentiable.neg differentiable_id)
            (Or.inl heven)).const_mul
          (Complex.log ((((2 * n + 2 : ℕ) : ℝ) : ℂ))))
  exact hdiff.continuous
/-- The limiting paired-eta logarithmic quotient is continuous on its exact
positive-half-plane zero-free domain. -/
theorem continuousOn_pairedEtaArithmeticQuotient :
    ContinuousOn
      (fun s => pairedEtaArithmeticDerivativeValue s / pairedEtaCore s)
      pairedEtaArithmeticQuotientDomain := by
  have hsubset :
      pairedEtaArithmeticQuotientDomain ⊆ {s : ℂ | 0 < s.re} :=
    fun _ hs => hs.1
  have hEcontinuous : ContinuousOn pairedEtaCore
      pairedEtaArithmeticQuotientDomain :=
    (analyticOnNhd_pairedEtaCore.mono hsubset).continuousOn
  have hDcontinuous : ContinuousOn pairedEtaArithmeticDerivativeValue
      pairedEtaArithmeticQuotientDomain := by
    intro s hs
    have hanalytic := (analyticOnNhd_pairedEtaCore s hs.1).deriv
    have hpositive : ∀ᶠ w in nhds s, 0 < w.re :=
      (Complex.isOpen_re_gt 0).mem_nhds hs.1
    have heq : pairedEtaArithmeticDerivativeValue =ᶠ[nhds s]
        deriv pairedEtaCore := by
      filter_upwards [hpositive] with w hw
      exact
        (hasDerivAt_pairedEtaCore_arithmeticDerivativeValue hw).deriv.symm
    exact
      (hanalytic.continuousAt.congr_of_eventuallyEq heq).continuousWithinAt
  exact hDcontinuous.div hEcontinuous (fun s hs => hs.2)

/-- Pulling the finite quotient approximation back to a zero-free circle gives
local uniform convergence on the compact angular interval. -/
theorem tendstoLocallyUniformlyOn_pairedEtaArithmeticQuotientPartialSum_circle
    (rho : ℂ) (r : ℝ)
    (hgeometry : ∀ theta : ℝ,
      circleMap rho r theta ∈ pairedEtaArithmeticQuotientDomain) :
    TendstoLocallyUniformlyOn
      (fun N theta =>
        pairedEtaArithmeticQuotientPartialSum N (circleMap rho r theta))
      (fun theta =>
        pairedEtaArithmeticDerivativeValue (circleMap rho r theta) /
          pairedEtaCore (circleMap rho r theta))
      atTop (Set.Icc 0 (2 * Real.pi)) := by
  have hcomp :=
    tendstoLocallyUniformlyOn_pairedEtaArithmeticQuotientPartialSum.comp
      (fun theta : ℝ => circleMap rho r theta)
      (fun theta _ => hgeometry theta)
      (show ContinuousOn (fun theta : ℝ => circleMap rho r theta)
          (Set.Icc 0 (2 * Real.pi)) from
        (by fun_prop : Continuous
          (fun theta : ℝ => circleMap rho r theta)).continuousOn)
  change TendstoLocallyUniformlyOn
    (fun N => pairedEtaArithmeticQuotientPartialSum N ∘
      fun theta : ℝ => circleMap rho r theta)
    ((fun s => pairedEtaArithmeticDerivativeValue s / pairedEtaCore s) ∘
      fun theta : ℝ => circleMap rho r theta)
    atTop (Set.Icc 0 (2 * Real.pi))
  exact hcomp

/-- On a compact circle where the limiting eta core never vanishes, every
sufficiently long finite eta polynomial is uniformly nonzero. -/
theorem eventually_forall_pairedEtaCorePartialSum_circle_ne_zero
    (rho : ℂ) (r : ℝ)
    (hgeometry : ∀ theta : ℝ,
      circleMap rho r theta ∈ pairedEtaArithmeticQuotientDomain) :
    ∀ᶠ N : ℕ in atTop, ∀ theta ∈ Set.Icc 0 (2 * Real.pi),
      pairedEtaCorePartialSum N (circleMap rho r theta) ≠ 0 := by
  let circle : ℝ → ℂ := fun theta => circleMap rho r theta
  have hcircleContinuous : Continuous circle := by
    dsimp [circle]
    fun_prop
  have hmaps : MapsTo circle (Set.Icc 0 (2 * Real.pi))
      {s : ℂ | 0 < s.re} := by
    intro theta _
    exact (hgeometry theta).1
  have hEcircle :=
    tendstoLocallyUniformlyOn_pairedEtaCorePartialSum.comp circle hmaps
      hcircleContinuous.continuousOn
  have hEuniform : TendstoUniformlyOn
      (fun N => pairedEtaCorePartialSum N ∘ circle)
      (pairedEtaCore ∘ circle) atTop (Set.Icc 0 (2 * Real.pi)) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      isCompact_Icc).mp hEcircle
  have hEcontinuous : ContinuousOn (fun theta => ‖pairedEtaCore (circle theta)‖)
      (Set.Icc 0 (2 * Real.pi)) := by
    have hcore : ContinuousOn pairedEtaCore
        {s : ℂ | 0 < s.re} := analyticOnNhd_pairedEtaCore.continuousOn
    exact (hcore.comp hcircleContinuous.continuousOn hmaps).norm
  obtain ⟨c, hc, hcLower⟩ := isCompact_Icc.exists_forall_le'
    hEcontinuous (fun theta _ => norm_pos_iff.mpr (hgeometry theta).2)
  have hcHalf : 0 < c / 2 := by positivity
  have hclose :=
    (Metric.tendstoUniformlyOn_iff.mp hEuniform) (c / 2) hcHalf
  filter_upwards [hclose] with N hN
  intro theta htheta hzero
  have hdist := hN theta htheta
  have hzero' : pairedEtaCorePartialSum N (circle theta) = 0 := by
    simpa [circle] using hzero
  have hdist' : ‖pairedEtaCore (circle theta)‖ < c / 2 := by
    calc
      ‖pairedEtaCore (circle theta)‖ =
          dist (pairedEtaCore (circle theta)) 0 := by
            rw [dist_zero_right]
      _ = dist (pairedEtaCore (circle theta))
          (pairedEtaCorePartialSum N (circle theta)) := by rw [hzero']
      _ < c / 2 := by simpa only [Function.comp_apply] using hdist
  have hlower := hcLower theta htheta
  linarith

/-- The real radial detector integrand obtained by replacing the convergent
eta logarithmic quotient with its finite Dirichlet-polynomial quotient. -/
def pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
    (x tau : ℝ) (rho : NontrivialZetaZero) (r : ℝ)
    (N : ℕ) (theta : ℝ) : ℝ :=
  (circleMap 0 r theta *
    (suzukiChebyshevLaplaceBoundaryHeatKernel x tau
        (circleMap rho.1 r theta - 1 / 2) *
      pairedEtaArithmeticQuotientPartialSum N
        (circleMap rho.1 r theta))).re

/-- The interval integral of one finite paired-eta arithmetic radial
integrand. -/
def pairedEtaBoundaryHeatFiniteArithmeticRadialFlux
    (x tau : ℝ) (rho : NontrivialZetaZero) (r : ℝ) (N : ℕ) : ℝ :=
  ∫ theta : ℝ in 0..2 * Real.pi,
    pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
      x tau rho r N theta

/-- On a zero-free circle, the heat-weighted finite arithmetic integrands
converge uniformly to the literal paired-eta radial integrand. -/
theorem tendstoUniformlyOn_pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
    (x tau : ℝ) (rho : NontrivialZetaZero) (r : ℝ)
    (hgeometry : ∀ theta : ℝ,
      circleMap rho.1 r theta ∈ pairedEtaArithmeticQuotientDomain) :
    TendstoUniformlyOn
      (fun N theta =>
        pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
          x tau rho r N theta)
      (fun theta =>
        (circleMap 0 r theta *
          pairedEtaBoundaryHeatWeightedArithmeticQuotient x tau
            (circleMap rho.1 r theta)).re)
      atTop (Set.Icc 0 (2 * Real.pi)) := by
  let circle : ℝ → ℂ := fun theta => circleMap rho.1 r theta
  let weight : ℝ → ℂ := fun theta =>
    circleMap 0 r theta *
      suzukiChebyshevLaplaceBoundaryHeatKernel x tau
        (circle theta - 1 / 2)
  have hcircleContinuous : Continuous circle := by
    dsimp [circle]
    fun_prop
  have hweightContinuous : Continuous weight := by
    dsimp [weight]
    fun_prop
  have hmaps : MapsTo circle (Set.Icc 0 (2 * Real.pi))
      pairedEtaArithmeticQuotientDomain :=
    fun theta _ => hgeometry theta
  have hQ :=
    tendstoLocallyUniformlyOn_pairedEtaArithmeticQuotientPartialSum_circle
      rho.1 r hgeometry
  have hQcontinuous : ContinuousOn
      (fun theta =>
        pairedEtaArithmeticDerivativeValue (circle theta) /
          pairedEtaCore (circle theta))
      (Set.Icc 0 (2 * Real.pi)) :=
    continuousOn_pairedEtaArithmeticQuotient.comp
      hcircleContinuous.continuousOn hmaps
  have hweightUniform : TendstoUniformlyOn
      (fun _ : ℕ => weight) weight atTop (Set.Icc 0 (2 * Real.pi)) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro epsilon hepsilon
    exact Eventually.of_forall fun _ theta _ => by
      simpa using hepsilon
  have hproduct :=
    hweightUniform.tendstoLocallyUniformlyOn.mul₀ hQ
      hweightContinuous.continuousOn hQcontinuous
  have hre :=
    Complex.uniformContinuous_re.comp_tendstoLocallyUniformlyOn hproduct
  apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
    isCompact_Icc).mp
  have hfinite : TendstoLocallyUniformlyOn
      (fun N theta =>
        pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
          x tau rho r N theta)
      (Complex.re ∘
        (weight * fun theta =>
          pairedEtaArithmeticDerivativeValue (circleMap rho.1 r theta) /
            pairedEtaCore (circleMap rho.1 r theta)))
      atTop (Set.Icc 0 (2 * Real.pi)) := by
    apply hre.congr
    intro N theta _
    unfold pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
    simp only [Function.comp_apply, Pi.mul_apply]
    dsimp [weight, circle]
    simp only [mul_assoc]
  apply hfinite.congr_right
  intro theta _
  unfold pairedEtaBoundaryHeatWeightedArithmeticQuotient
  simp only [Function.comp_apply, Pi.mul_apply]
  dsimp [weight, circle]
  simp only [mul_assoc]

/-- Every sufficiently long finite arithmetic integrand is genuinely `L¹` on
a zero-free detector circle. -/
theorem eventually_intervalIntegrable_pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
    (x tau : ℝ) (rho : NontrivialZetaZero) (r : ℝ)
    (hgeometry : ∀ theta : ℝ,
      circleMap rho.1 r theta ∈ pairedEtaArithmeticQuotientDomain) :
    ∀ᶠ N : ℕ in atTop,
      IntervalIntegrable
        (pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
          x tau rho r N) volume 0 (2 * Real.pi) := by
  have hnonzero :=
    eventually_forall_pairedEtaCorePartialSum_circle_ne_zero
      rho.1 r hgeometry
  filter_upwards [hnonzero] with N hN
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  let circle : ℝ → ℂ := fun theta => circleMap rho.1 r theta
  let weight : ℝ → ℂ := fun theta =>
    circleMap 0 r theta *
      suzukiChebyshevLaplaceBoundaryHeatKernel x tau
        (circle theta - 1 / 2)
  have hcircleContinuous : Continuous circle := by
    dsimp [circle]
    fun_prop
  have hweightContinuous : Continuous weight := by
    dsimp [weight]
    fun_prop
  have hEcontinuous : Continuous
      (fun theta => pairedEtaCorePartialSum N (circle theta)) :=
    (differentiable_pairedEtaCorePartialSum N).continuous.comp
      hcircleContinuous
  have hDcontinuous : Continuous
      (fun theta => pairedEtaCoreDerivativePartialSum N (circle theta)) :=
    (continuous_pairedEtaCoreDerivativePartialSum N).comp
      hcircleContinuous
  have hquotientContinuous : ContinuousOn
      (fun theta =>
        pairedEtaCoreDerivativePartialSum N (circle theta) /
          pairedEtaCorePartialSum N (circle theta))
      (Set.Icc 0 (2 * Real.pi)) :=
    hDcontinuous.continuousOn.div hEcontinuous.continuousOn (by
      intro theta htheta
      exact hN theta htheta)
  have hproduct :=
    hweightContinuous.continuousOn.mul hquotientContinuous
  have hre := Complex.continuous_re.comp_continuousOn hproduct
  apply hre.congr
  intro theta _
  unfold pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
    pairedEtaArithmeticQuotientPartialSum
  simp only [Function.comp_apply]
  dsimp [weight, circle]
  simp only [mul_assoc]

/-- The limiting literal arithmetic radial integrand is genuinely `L¹` on a
circle contained in the zero-free quotient domain. -/
theorem intervalIntegrable_pairedEtaBoundaryHeatArithmeticRadialIntegrand
    (x tau : ℝ) (rho : NontrivialZetaZero) (r : ℝ)
    (hgeometry : ∀ theta : ℝ,
      circleMap rho.1 r theta ∈ pairedEtaArithmeticQuotientDomain) :
    IntervalIntegrable
      (fun theta =>
        (circleMap 0 r theta *
          pairedEtaBoundaryHeatWeightedArithmeticQuotient x tau
            (circleMap rho.1 r theta)).re)
      volume 0 (2 * Real.pi) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  let circle : ℝ → ℂ := fun theta => circleMap rho.1 r theta
  let weight : ℝ → ℂ := fun theta =>
    circleMap 0 r theta *
      suzukiChebyshevLaplaceBoundaryHeatKernel x tau
        (circle theta - 1 / 2)
  have hcircleContinuous : Continuous circle := by
    dsimp [circle]
    fun_prop
  have hweightContinuous : Continuous weight := by
    dsimp [weight]
    fun_prop
  have hmaps : MapsTo circle (Set.Icc 0 (2 * Real.pi))
      pairedEtaArithmeticQuotientDomain :=
    fun theta _ => hgeometry theta
  have hquotientContinuous : ContinuousOn
      (fun theta =>
        pairedEtaArithmeticDerivativeValue (circle theta) /
          pairedEtaCore (circle theta))
      (Set.Icc 0 (2 * Real.pi)) :=
    continuousOn_pairedEtaArithmeticQuotient.comp
      hcircleContinuous.continuousOn hmaps
  have hproduct :=
    hweightContinuous.continuousOn.mul hquotientContinuous
  have hre := Complex.continuous_re.comp_continuousOn hproduct
  apply hre.congr
  intro theta _
  unfold pairedEtaBoundaryHeatWeightedArithmeticQuotient
  simp only [Function.comp_apply]
  dsimp [weight, circle]
  simp only [mul_assoc]

/-- On a fixed zero-free circle, the finite arithmetic radial fluxes converge
to the literal convergent paired-eta radial flux. -/
theorem tendsto_pairedEtaBoundaryHeatFiniteArithmeticRadialFlux
    (x tau : ℝ) (rho : NontrivialZetaZero) (r : ℝ)
    (hgeometry : ∀ theta : ℝ,
      circleMap rho.1 r theta ∈ pairedEtaArithmeticQuotientDomain) :
    Tendsto
      (pairedEtaBoundaryHeatFiniteArithmeticRadialFlux x tau rho r)
      atTop
      (nhds (pairedEtaBoundaryHeatArithmeticRadialFlux x tau rho r)) := by
  have huniform :=
    tendstoUniformlyOn_pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
      x tau rho r hgeometry
  have hfiniteIntegrable :=
    eventually_intervalIntegrable_pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
      x tau rho r hgeometry
  have hlimitIntegrable :=
    intervalIntegrable_pairedEtaBoundaryHeatArithmeticRadialIntegrand
      x tau rho r hgeometry
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let delta : ℝ := epsilon / (2 * Real.pi + 1)
  have hdenominator : 0 < 2 * Real.pi + 1 := by positivity
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hclose :=
    (Metric.tendstoUniformlyOn_iff.mp huniform) delta hdelta
  filter_upwards [hclose, hfiniteIntegrable] with N hN hNIntegrable
  change dist
    (∫ theta : ℝ in 0..2 * Real.pi,
      pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
        x tau rho r N theta)
    (∫ theta : ℝ in 0..2 * Real.pi,
      (circleMap 0 r theta *
        pairedEtaBoundaryHeatWeightedArithmeticQuotient x tau
          (circleMap rho.1 r theta)).re) < epsilon
  rw [dist_eq_norm,
    ← intervalIntegral.integral_sub hNIntegrable hlimitIntegrable]
  have hbound :
      ‖∫ theta : ℝ in 0..2 * Real.pi,
        pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
            x tau rho r N theta -
          (circleMap 0 r theta *
            pairedEtaBoundaryHeatWeightedArithmeticQuotient x tau
              (circleMap rho.1 r theta)).re‖ ≤
        delta * |2 * Real.pi - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro theta htheta
    rw [← dist_eq_norm, dist_comm]
    exact (hN theta (by
      rw [← uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
      exact uIoc_subset_uIcc htheta)).le
  apply hbound.trans_lt
  rw [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  dsimp [delta]
  calc
    epsilon / (2 * Real.pi + 1) * (2 * Real.pi) <
        epsilon / (2 * Real.pi + 1) * (2 * Real.pi + 1) := by
      exact mul_lt_mul_of_pos_left (by linarith) (div_pos hepsilon hdenominator)
    _ = epsilon := by field_simp

/-- The sum of the finite arithmetic radial fluxes over one genuine selected
spectral window. -/
def pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
    (x tau T r : ℝ) (N : ℕ) : ℝ :=
  ∑ rho ∈ spectralUpperZetaZeroWindow T,
    pairedEtaBoundaryHeatFiniteArithmeticRadialFlux
      x tau rho r N

/-- At fixed valid radius and finite spectral window, increasing the arithmetic
truncation recovers the exact normalized paired-eta flux window. -/
theorem tendsto_pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
    (x tau T r : ℝ)
    (hgeometry : ∀ rho ∈ spectralUpperZetaZeroWindow T, ∀ theta : ℝ,
      circleMap rho.1 r theta ∈ pairedEtaArithmeticQuotientDomain) :
    Tendsto
      (pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
        x tau T r)
      atTop
      (nhds (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
        x tau T r)) := by
  have hsum := tendsto_finsetSum (spectralUpperZetaZeroWindow T)
    (fun rho hrho =>
      tendsto_pairedEtaBoundaryHeatFiniteArithmeticRadialFlux
        x tau rho r (hgeometry rho hrho))
  change Tendsto
    (fun N => ∑ rho ∈ spectralUpperZetaZeroWindow T,
      pairedEtaBoundaryHeatFiniteArithmeticRadialFlux
        x tau rho r N)
    atTop
    (nhds (∑ rho ∈ spectralUpperZetaZeroWindow T,
      pairedEtaBoundaryHeatArithmeticRadialFlux x tau rho r)) at hsum
  have htarget :
      (∑ rho ∈ spectralUpperZetaZeroWindow T,
        pairedEtaBoundaryHeatArithmeticRadialFlux x tau rho r) =
      pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
        x tau T r := by
    unfold pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
    apply Finset.sum_congr rfl
    intro rho _
    exact
      (pairedEtaBoundaryHeatNormalizedNumeratorRadialFlux_eq_arithmetic
        x tau rho r).symm
  change Tendsto
    (fun N => ∑ rho ∈ spectralUpperZetaZeroWindow T,
      pairedEtaBoundaryHeatFiniteArithmeticRadialFlux
        x tau rho r N)
    atTop
    (nhds (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
      x tau T r))
  rw [← htarget]
  exact hsum

/-- At every detector stage there is a truncation index beyond the stage number
whose finite window is within the diagonal tolerance, is integrable, and has
no finite eta denominator zero on any selected circle. -/
theorem exists_pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex
    (x tau : ℝ) (n : ℕ) :
    ∃ N : ℕ,
      n ≤ N ∧
      dist
          (pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
            x tau (n : ℝ)
              (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n) N)
          (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
            x tau (n : ℝ)
              (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)) <
        pairedEtaBoundaryHeatFluxDiagonalTolerance n ∧
      (∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ),
        IntervalIntegrable
          (pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
            x tau rho
              (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n) N)
          volume 0 (2 * Real.pi)) ∧
      ∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ),
        ∀ theta ∈ Set.Icc 0 (2 * Real.pi),
          pairedEtaCorePartialSum N
            (circleMap rho.1
              (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n) theta) ≠ 0 := by
  let r := pairedEtaBoundaryHeatFluxDiagonalRadius x tau n
  have hrSpec := pairedEtaBoundaryHeatFluxDiagonalRadius_spec x tau n
  have hgeometry : ∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ),
      ∀ theta : ℝ,
      circleMap rho.1 r theta ∈ pairedEtaArithmeticQuotientDomain := by
    intro rho hrho theta
    exact hrSpec.2.2.2.2 rho hrho theta
  have hlimit :=
    tendsto_pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
      x tau (n : ℝ) r hgeometry
  have hclose : ∀ᶠ N : ℕ in atTop,
      dist
          (pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
            x tau (n : ℝ) r N)
          (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
            x tau (n : ℝ) r) <
        pairedEtaBoundaryHeatFluxDiagonalTolerance n :=
    (Metric.tendsto_nhds.mp hlimit) _
      (pairedEtaBoundaryHeatFluxDiagonalTolerance_pos n)
  have hintegrable : ∀ᶠ N : ℕ in atTop,
      ∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ),
        IntervalIntegrable
          (pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
            x tau rho r N) volume 0 (2 * Real.pi) := by
    rw [Finset.eventually_all]
    intro rho hrho
    exact
      eventually_intervalIntegrable_pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
        x tau rho r (hgeometry rho hrho)
  have hnonzero : ∀ᶠ N : ℕ in atTop,
      ∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ),
        ∀ theta ∈ Set.Icc 0 (2 * Real.pi),
          pairedEtaCorePartialSum N (circleMap rho.1 r theta) ≠ 0 := by
    rw [Finset.eventually_all]
    intro rho hrho
    exact
      eventually_forall_pairedEtaCorePartialSum_circle_ne_zero
        rho.1 r (hgeometry rho hrho)
  obtain ⟨N, hNge, hNclose, hNintegrable, hNnonzero⟩ :=
    ((eventually_ge_atTop n).and
      (hclose.and (hintegrable.and hnonzero))).exists
  exact ⟨N, hNge, hNclose, hNintegrable, hNnonzero⟩

/-- A classically selected growing finite eta truncation index at each detector
stage. -/
noncomputable def pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex
    (x tau : ℝ) (n : ℕ) : ℕ :=
  Classical.choose
    (exists_pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex x tau n)

/-- The selected arithmetic truncation grows past its stage, approximates the
literal window within tolerance, is simultaneously `L¹`, and is denominator-
nonvanishing on every selected compact circle. -/
theorem pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex_spec
    (x tau : ℝ) (n : ℕ) :
    n ≤ pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex x tau n ∧
    dist
        (pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
          x tau (n : ℝ)
            (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)
            (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex
              x tau n))
        (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
          x tau (n : ℝ)
            (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)) <
      pairedEtaBoundaryHeatFluxDiagonalTolerance n ∧
    (∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ),
      IntervalIntegrable
        (pairedEtaBoundaryHeatFiniteArithmeticRadialIntegrand
          x tau rho (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)
            (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex
              x tau n)) volume 0 (2 * Real.pi)) ∧
    ∀ rho ∈ spectralUpperZetaZeroWindow (n : ℝ),
      ∀ theta ∈ Set.Icc 0 (2 * Real.pi),
        pairedEtaCorePartialSum
          (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex x tau n)
          (circleMap rho.1
            (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n) theta) ≠ 0 := by
  exact Classical.choose_spec
    (exists_pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex x tau n)

/-- The selected finite arithmetic truncation indices tend to infinity. -/
theorem tendsto_pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex_atTop
    (x tau : ℝ) :
    Tendsto
      (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex x tau)
      atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro m
  filter_upwards [eventually_ge_atTop m] with n hn
  exact hn.trans
    (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex_spec
      x tau n).1

/-- The distance from the selected finite arithmetic flux window to the
literal paired-eta diagonal flux tends to zero. -/
theorem tendsto_pairedEtaBoundaryHeatFiniteArithmeticDiagonalError_zero
    (x tau : ℝ) :
    Tendsto
      (fun n : ℕ =>
        dist
          (pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxWindow
            x tau (n : ℝ)
              (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n))
          (pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
            x tau (n : ℝ)
              (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)
              (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex
                x tau n)))
      atTop (nhds 0) := by
  apply squeeze_zero'
    (g := pairedEtaBoundaryHeatFluxDiagonalTolerance)
  · exact Eventually.of_forall fun _ => dist_nonneg
  · exact Eventually.of_forall fun n =>
      (by
        simpa only [dist_comm] using
        (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex_spec
          x tau n).2.1.le)
  · exact tendsto_pairedEtaBoundaryHeatFluxDiagonalTolerance_zero

/-- A single sequence of genuine finite paired-eta Dirichlet-polynomial radial
flux windows converges to `2 * pi` times the complete fixed-time boundary-heat
detector. -/
theorem tendsto_pairedEtaBoundaryHeatFiniteArithmeticRadialFluxDiagonal
    (x : ℝ) {tau : ℝ} (htau : 0 < tau) :
    Tendsto
      (fun n : ℕ =>
        pairedEtaBoundaryHeatFiniteArithmeticRadialFluxWindow
          x tau (n : ℝ)
            (pairedEtaBoundaryHeatFluxDiagonalRadius x tau n)
            (pairedEtaBoundaryHeatFiniteArithmeticDiagonalIndex
              x tau n))
      atTop
      (nhds (2 * Real.pi *
        riemannXiUpperHyperbolicBoundaryHeatTotal x tau)) := by
  exact
    (tendsto_pairedEtaBoundaryHeatNormalizedNumeratorRadialFluxDiagonal
      x htau).congr_dist
        (tendsto_pairedEtaBoundaryHeatFiniteArithmeticDiagonalError_zero
          x tau)

end
end RiemannGaussian
