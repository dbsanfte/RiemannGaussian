import RiemannGaussian.FiniteHardyMultipointConclusion
import RiemannGaussian.GaussianXiDivisorContour
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Locally uniform passage from finite homotopies to an entire limit

This file begins the analytic bridge from the completed finite Hardy theory
to the spectral xi function.  It proves that locally uniform convergence of
holomorphic functions also gives locally uniform convergence of the
homotopies

`f + i * eta * f'`.

Consequently, a convergent sequence of zeros of finite polynomial
homotopies cannot become a spurious point: its limit is a zero of the
limiting analytic homotopy.  This is a one-way closure theorem.  It does not
assert the existence of suitable real-polynomial approximants or the
converse persistence of a prescribed limiting zero.
-/

open Filter Polynomial Set
open scoped Topology

namespace RiemannGaussian

noncomputable section

/-- The analytic counterpart of the finite polynomial homotopy
`A + i * eta * A'`. -/
def analyticEValue (f : ℂ → ℂ) (eta : ℝ) (z : ℂ) : ℂ :=
  f z + Complex.I * (eta : ℂ) * deriv f z

/-- On a real polynomial, `analyticEValue` is exactly evaluation of the
finite homotopy polynomial. -/
@[simp] theorem analyticEValue_realPolynomial
    (A : ℝ[X]) (eta : ℝ) (z : ℂ) :
    analyticEValue (fun w : ℂ ↦ (A.map Complex.ofRealHom).eval w) eta z =
      (finiteEPolynomial A eta).eval z := by
  rw [analyticEValue, Polynomial.deriv, finiteEPolynomial_eval]
  simp [Polynomial.eval_map]

/-- Locally uniform convergence of holomorphic functions transports through
the operation `f ↦ f + i * eta * f'`. -/
theorem analyticEValue_tendstoLocallyUniformlyOn
    {ι : Type*} {φ : Filter ι} {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
    {U : Set ℂ} (hF : TendstoLocallyUniformlyOn F f φ U)
    (hhol : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hU : IsOpen U)
    (eta : ℝ) :
    TendstoLocallyUniformlyOn
      (fun n ↦ analyticEValue (F n) eta) (analyticEValue f eta) φ U := by
  have hderiv := hF.deriv hhol hU
  have hscaled :=
    (uniformContinuous_const_smul (Complex.I * (eta : ℂ))).comp_tendstoLocallyUniformlyOn
      hderiv
  refine ((hF.add hscaled).congr
    (G := fun n ↦ analyticEValue (F n) eta) ?_).congr_right ?_
  · intro n z _
    simp [analyticEValue, Function.comp_def, smul_eq_mul]
  · intro z _
    simp [analyticEValue, Function.comp_def, smul_eq_mul]

/-- The limiting analytic homotopy is holomorphic on the same open set. -/
theorem analyticEValue_differentiableOn
    {f : ℂ → ℂ} {U : Set ℂ} (hf : DifferentiableOn ℂ f U)
    (hU : IsOpen U) (eta : ℝ) :
    DifferentiableOn ℂ (analyticEValue f eta) U := by
  unfold analyticEValue
  intro z hz
  exact (hf z hz).add
    (((hf.deriv hU) z hz).const_mul (Complex.I * (eta : ℂ)))

/-- A convergent sequence of zeros of analytic homotopies remains a zero in
the locally uniform holomorphic limit. -/
theorem analyticEValue_eq_zero_of_locallyUniform_root_limit
    {ι : Type*} {φ : Filter ι} [φ.NeBot]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {U : Set ℂ}
    (hF : TendstoLocallyUniformlyOn F f φ U)
    (hhol : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hU : IsOpen U)
    (eta : ℝ) {z : ι → ℂ} {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hz : Tendsto z φ (nhdsWithin z₀ U))
    (hroot : ∀ᶠ n in φ, analyticEValue (F n) eta (z n) = 0) :
    analyticEValue f eta z₀ = 0 := by
  have hfdiff : DifferentiableOn ℂ f U := hF.differentiableOn hhol hU
  have hEdiff : DifferentiableOn ℂ (analyticEValue f eta) U :=
    analyticEValue_differentiableOn hfdiff hU eta
  have hlimit :
      Tendsto (fun n ↦ analyticEValue (F n) eta (z n)) φ
        (nhds (analyticEValue f eta z₀)) :=
    (analyticEValue_tendstoLocallyUniformlyOn hF hhol hU eta).tendsto_comp
      (hEdiff z₀ hz₀).continuousWithinAt hz₀ hz
  have hzero :
      Tendsto (fun n ↦ analyticEValue (F n) eta (z n)) φ (nhds 0) :=
    tendsto_nhds_of_eventually_eq hroot
  exact tendsto_nhds_unique hlimit hzero

/-- Specialization to real polynomial approximants on the whole plane. -/
theorem finiteEPolynomial_root_limit
    {ι : Type*} {φ : Filter ι} [φ.NeBot] (A : ι → ℝ[X])
    {f : ℂ → ℂ} (eta : ℝ)
    (hA : TendstoLocallyUniformlyOn
      (fun n z ↦ ((A n).map Complex.ofRealHom).eval z) f φ Set.univ)
    {z : ι → ℂ} {z₀ : ℂ} (hz : Tendsto z φ (nhds z₀))
    (hroot : ∀ᶠ n in φ, (finiteEPolynomial (A n) eta).eval (z n) = 0) :
    analyticEValue f eta z₀ = 0 := by
  apply analyticEValue_eq_zero_of_locallyUniform_root_limit hA
    (Eventually.of_forall fun n ↦ ((A n).map Complex.ofRealHom).differentiableOn)
    isOpen_univ eta (mem_univ z₀)
  · simpa only [nhdsWithin_univ] using hz
  · filter_upwards [hroot] with n hn
    simpa using hn

/-- The preceding closure theorem specialized to the spectral xi function.
It isolates the precise approximation hypothesis still required by the
finite-to-xi program. -/
theorem riemannXiSpectral_analyticEValue_eq_zero_of_finite_root_limit
    {ι : Type*} {φ : Filter ι} [φ.NeBot] (A : ι → ℝ[X]) (eta : ℝ)
    (hA : TendstoLocallyUniformlyOn
      (fun n z ↦ ((A n).map Complex.ofRealHom).eval z)
      riemannXiSpectral φ Set.univ)
    {z : ι → ℂ} {z₀ : ℂ} (hz : Tendsto z φ (nhds z₀))
    (hroot : ∀ᶠ n in φ, (finiteEPolynomial (A n) eta).eval (z n) = 0) :
    analyticEValue riemannXiSpectral eta z₀ = 0 :=
  finiteEPolynomial_root_limit A eta hA hz hroot

end

end RiemannGaussian
