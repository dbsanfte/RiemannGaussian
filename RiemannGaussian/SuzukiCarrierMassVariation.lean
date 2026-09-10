/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierNormalizedMass

/-!
# Global horizontal variation of the true smoothed source

The entire xi pair gives a globally valid source identity in spectral
coordinates. Both fields and their derivatives are smooth through common
zeros and genuine carrier poles. The full complex source is retained.
-/

open Complex Filter Set Topology
open scoped ContDiff
namespace RiemannGaussian
noncomputable section

/-- The actual real mass on a horizontal spectral line. -/
def suzukiXiHorizontalMass (r y x : ℝ) : ℝ :=
  suzukiXiNormalizedMass r ((x : ℂ) + (y : ℂ) * I)

/-- The actual complex carrier on the same oriented spectral line. -/
def suzukiXiHorizontalCarrier (r y x : ℝ) : ℂ :=
  suzukiXiSmoothCarrier r ((x : ℂ) + (y : ℂ) * I)

/-- The mass and all its real derivatives exist on every full horizontal line. -/
theorem contDiff_suzukiXiHorizontalMass {r : ℝ} (hr : 0 < r) (y : ℝ) :
    ContDiff ℝ ∞ (suzukiXiHorizontalMass r y) :=
  (contDiff_suzukiXiNormalizedMass hr).comp (Complex.ofRealCLM.contDiff.add contDiff_const)

/-- The complex carrier and its derivatives are also globally smooth on each line. -/
theorem contDiff_suzukiXiHorizontalCarrier {r : ℝ} (hr : 0 < r) (y : ℝ) :
    ContDiff ℝ ∞ (suzukiXiHorizontalCarrier r y) :=
  (contDiff_suzukiXiSmoothCarrier hr).comp (Complex.ofRealCLM.contDiff.add contDiff_const)

private lemma horizontal_derivative {f : ℂ → ℂ} {f' : ℂ} {x y : ℝ}
    (hf : HasDerivAt f f' ((x : ℂ) + (y : ℂ) * I)) :
    HasDerivAt (fun u : ℝ => f ((u : ℂ) + (y : ℂ) * I)) f' x := by
  have hline := (hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I)
  simpa only [Function.comp_def, mul_one, id_eq] using (hf.comp (x : ℂ) hline).comp_ofReal

private lemma coupled_variation {f g d : ℝ → ℂ} {f' g' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t)
    (hd : DifferentiableAt ℝ d t) (hz : d t ≠ 0) :
    (f t * starRingEnd ℂ (f t) / d t) *
        deriv (fun u => I * f u * starRingEnd ℂ (g u) / d u) t -
      (I * f t * starRingEnd ℂ (g t) / d t) *
        deriv (fun u => f u * starRingEnd ℂ (f u) / d u) t =
      -I * f t ^ 2 * starRingEnd ℂ (f' * g t - f t * g') / d t ^ 2 := by
  have hm := ((hf.fun_mul hf.star).div hd.hasDerivAt hz).deriv
  have hS := (((hf.const_mul I).fun_mul hg.star).div hd.hasDerivAt hz).deriv
  simp only [star_def] at hm hS
  change deriv (fun u => f u * starRingEnd ℂ (f u) / d u) t = _ at hm
  change deriv (fun u => I * f u * starRingEnd ℂ (g u) / d u) t = _ at hS
  rw [hm, hS]
  simp only [map_mul, map_sub]
  field_simp
  ring

private lemma carrier_formula (r : ℝ) (z : ℂ) :
    suzukiXiSmoothCarrier r z = I * riemannXiSpectral z *
      starRingEnd ℂ (suzukiXiEValue z) /
        ((normSq (suzukiXiEValue z) + r ^ 2 * normSq (riemannXiSpectral z) : ℝ) : ℂ) := by
  rw [suzukiXiSmoothCarrier, complexSmoothQuotient, complexSmoothQuotient_denominator]
  simp only [map_mul, normSq_I, one_mul]

/-- The exact source is a coupled horizontal variation everywhere,
including genuine poles and common zeros. The factor i records the
orientation of the spectral Cauchy--Green source. -/
theorem suzukiXiSmoothCarrierSource_eq_horizontal_mass_variation {r : ℝ} (hr : 0 < r) (y x : ℝ) :
    suzukiXiSmoothCarrierSource r ((x : ℂ) + (y : ℂ) * I) =
      2 * I * (r : ℂ) ^ 2 *
        ((suzukiXiHorizontalMass r y x : ℂ) * deriv (suzukiXiHorizontalCarrier r y) x -
          suzukiXiHorizontalCarrier r y x * ((deriv (suzukiXiHorizontalMass r y) x : ℝ) : ℂ)) := by
  by_cases hA : riemannXiSpectral ((x : ℂ) + (y : ℂ) * I) = 0
  · have hm : suzukiXiHorizontalMass r y x = 0 := suzukiXiNormalizedMass_eq_zero r hA
    have hS : suzukiXiHorizontalCarrier r y x = 0 := suzukiXiSmoothCarrier_eq_zero_of_xi_zero r hA
    simp [suzukiXiSmoothCarrierSource, hA, hm, hS]
  let d := fun u : ℝ => normSq (suzukiXiEValue ((u : ℂ) + (y : ℂ) * I)) +
    r ^ 2 * normSq (riemannXiSpectral ((u : ℂ) + (y : ℂ) * I))
  have hf := horizontal_derivative (analyticAt_riemannXiSpectral ((x : ℂ) + (y : ℂ) * I)).differentiableAt.hasDerivAt
  have hg := horizontal_derivative (analyticAt_suzukiXiEValue ((x : ℂ) + (y : ℂ) * I)).differentiableAt.hasDerivAt
  have hd : DifferentiableAt ℝ d x := by
    dsimp only [d]
    simpa only [normSq_eq_norm_sq] using
      (hg.differentiableAt.norm_sq (𝕜 := ℂ)).fun_add
        ((hf.differentiableAt.norm_sq (𝕜 := ℂ)).const_mul (r ^ 2))
  have hp := complexSmoothQuotient_denominator_pos hr
    (b := suzukiXiEValue ((x : ℂ) + (y : ℂ) * I)) (Or.inl hA)
  have hz : (d x : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have h := coupled_variation hf hg hd.hasDerivAt.ofReal_comp.differentiableAt hz
  have hmf : (fun u : ℝ => riemannXiSpectral ((u : ℂ) + (y : ℂ) * I) *
      starRingEnd ℂ (riemannXiSpectral ((u : ℂ) + (y : ℂ) * I)) / (d u : ℂ)) =
      fun u => (suzukiXiHorizontalMass r y u : ℂ) := by
    funext u
    rw [mul_conj]
    change (normSq (riemannXiSpectral ((u : ℂ) + (y : ℂ) * I)) : ℂ) / (d u : ℂ) =
      ((normSq (riemannXiSpectral ((u : ℂ) + (y : ℂ) * I)) / d u : ℝ) : ℂ)
    rw [ofReal_div]
  have hSf : (fun u : ℝ => I * riemannXiSpectral ((u : ℂ) + (y : ℂ) * I) *
      starRingEnd ℂ (suzukiXiEValue ((u : ℂ) + (y : ℂ) * I)) / (d u : ℂ)) =
      suzukiXiHorizontalCarrier r y := by
    funext u
    exact (carrier_formula r _).symm
  have hm := ((contDiff_suzukiXiHorizontalMass hr y).differentiable (by simp) x).hasDerivAt
  rw [hmf, hSf, hm.ofReal_comp.deriv, congrFun hmf x, congrFun hSf x] at h
  rw [h]
  unfold suzukiXiSmoothCarrierSource
  dsimp only [d]
  ring_nf
  simp only [I_sq]
  ring

end
end RiemannGaussian
