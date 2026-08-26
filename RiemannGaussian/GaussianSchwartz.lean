import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Asymptotics.SuperpolynomialDecay
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian
import RiemannGaussian.GaussianHeat

/-!
# Gaussian functions in Schwartz space

This file constructs the standard real Gaussian as an actual Mathlib
`SchwartzMap`.  Translations and positive rescalings will then give the
symmetric Gaussian family used by the closed-cone argument.
-/

open Filter Set
open Asymptotics Polynomial
open scoped SchwartzMap Topology

namespace RiemannGaussian

noncomputable section

/-- The standard Gaussian with variance one, in the normalization convenient
for Hermite-polynomial derivative formulas. -/
def standardGaussian (x : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 / 2))

lemma standardGaussian_superpolynomialDecay :
    SuperpolynomialDecay (cocompact ℝ) id standardGaussian := by
  rw [superpolynomialDecay_iff_norm_tendsto_zero]
  intro n
  have h := tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (a := (1 / 2 : ℝ)) (by norm_num) (n : ℝ)
  have h' : Tendsto (fun x : ℝ => |x| ^ (n : ℝ) * standardGaussian x)
      (cocompact ℝ) (𝓝 0) := by
    refine h.congr' (Eventually.of_forall fun x => ?_)
    unfold standardGaussian
    congr 2
    ring
  simpa [standardGaussian, Real.norm_eq_abs, abs_mul, abs_pow, Real.rpow_natCast,
    abs_of_pos] using h'

lemma iter_deriv_standardGaussian (n : ℕ) (x : ℝ) :
    deriv^[n] standardGaussian x =
      (-1 : ℝ) ^ n * aeval x (hermite n) * standardGaussian x := by
  change deriv^[n] (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) x =
    (-1 : ℝ) ^ n * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))
  exact Polynomial.deriv_gaussian_eq_hermite_mul_gaussian n x

/-- The standard Gaussian, bundled as a real Schwartz function. -/
def standardGaussianSchwartz : 𝓢(ℝ, ℝ) where
  toFun := standardGaussian
  smooth' := by
    unfold standardGaussian
    fun_prop
  decay' k n := by
    let p : ℝ[X] := X ^ k * C ((-1 : ℝ) ^ n) *
      (hermite n).map (Int.castRingHom ℝ)
    have hp_decay : SuperpolynomialDecay (cocompact ℝ) id
        (fun x : ℝ => p.eval x * standardGaussian x) := by
      simpa only [Function.comp_apply, id_eq] using
        standardGaussian_superpolynomialDecay.polynomial_mul p
    have hp_tendsto : Tendsto
        (fun x : ℝ => ‖p.eval x * standardGaussian x‖)
        (cocompact ℝ) (𝓝 0) := by
      exact tendsto_zero_iff_norm_tendsto_zero.mp (by simpa using hp_decay 0)
    have hp_cont : Continuous (fun x : ℝ => ‖p.eval x * standardGaussian x‖) := by
      unfold standardGaussian
      fun_prop
    have hp_bounded : Bornology.IsBounded (range fun x : ℝ =>
        ‖p.eval x * standardGaussian x‖) :=
      hp_cont.isBounded_range_iff_isBigO.mpr (hp_tendsto.isBigO_one ℝ)
    rw [isBounded_iff_forall_norm_le] at hp_bounded
    obtain ⟨C, hC⟩ := hp_bounded
    refine ⟨C, fun x => ?_⟩
    have hx := hC ‖p.eval x * standardGaussian x‖ ⟨x, rfl⟩
    rw [norm_norm] at hx
    convert hx using 1
    simp only [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      iteratedDeriv_eq_iterate, iter_deriv_standardGaussian]
    simp [p, eval_mul, eval_pow, eval_X, eval_map, aeval_def, abs_mul,
      standardGaussian, abs_of_pos]
    ring

/-- Real-valued Schwartz test functions on the real line. -/
abbrev RealSchwartz := 𝓢(ℝ, ℝ)

/-- A positive width together with a real translation parameter. -/
abbrev PositiveGaussianIndex := Set.Ioi (0 : ℝ) × ℝ

/-- The centered Gaussian `exp (-ε x²)` as a Schwartz map. -/
def centeredGaussianSchwartz (ε : Set.Ioi (0 : ℝ)) : RealSchwartz := by
  let c : ℝ := Real.sqrt (2 * ε.1)
  have hc : c ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.2 (mul_pos two_pos ε.2))
  exact SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 c hc)) standardGaussianSchwartz

@[simp]
theorem centeredGaussianSchwartz_apply (ε : Set.Ioi (0 : ℝ)) (x : ℝ) :
    centeredGaussianSchwartz ε x = Real.exp (-ε.1 * x ^ 2) := by
  change standardGaussian (Real.sqrt (2 * ε.1) * x) =
    Real.exp (-ε.1 * x ^ 2)
  unfold standardGaussian
  have hsqrt : Real.sqrt (2 * ε.1) ^ 2 = 2 * ε.1 := by
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) ε.2.le)]
  congr 1
  rw [mul_pow, hsqrt]
  ring

/-- A translated positive-width Gaussian as a Schwartz map. -/
def translatedGaussianSchwartz (p : PositiveGaussianIndex) : RealSchwartz :=
  (centeredGaussianSchwartz p.1).compSubConstCLM ℝ p.2

@[simp]
theorem translatedGaussianSchwartz_apply (p : PositiveGaussianIndex) (r : ℝ) :
    translatedGaussianSchwartz p r = translatedGaussian p.1.1 p.2 r := by
  simp [translatedGaussianSchwartz, translatedGaussian]

/-- The concrete even pair of translated Gaussians, bundled in Schwartz
space. -/
def symmetricGaussianSchwartz (p : PositiveGaussianIndex) : RealSchwartz :=
  translatedGaussianSchwartz p +
    translatedGaussianSchwartz (p.1, -p.2)

@[simp]
theorem symmetricGaussianSchwartz_apply (p : PositiveGaussianIndex) (r : ℝ) :
    symmetricGaussianSchwartz p r = symmetricGaussian p.1.1 p.2 r := by
  simp only [symmetricGaussianSchwartz, add_apply,
    translatedGaussianSchwartz_apply, symmetricGaussian, translatedGaussian]
  congr 2
  congr 1
  ring

end

end RiemannGaussian
