/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SuzukiCarrierSafeHalfPlane

/-!
# Vanishing outer horizontal sides for the actual mixed carrier

For every pair of genuine zeta nodes, the upper horizontal integral of
`C(z) / ((z-conj alpha_rho)*(z-alpha_sigma))` across `[-T,T]+iT` is
bounded by `8/T` for `T >= 1`. Its integrability is proved using the
unconditional carrier nonvanishing and analytic estimates in the safe
half-plane. Thus this full outer side vanishes, retaining every mixed
entry and multiplicity convention of the boundary Gram.

No claim about the remaining vertical sides or strip poles is made here.
-/

open Complex Filter MeasureTheory Set Topology
open scoped Topology

namespace RiemannGaussian

noncomputable section

private lemma safe_horizontal_distance {T : ℝ} (hT : 1 ≤ T) (x : ℝ) {a : ℂ}
    (ha : a.im ≤ 1 / 2) : T / 2 ≤ ‖(x : ℂ) + I * (T : ℂ) - a‖ := by
  calc
    T / 2 ≤ T - a.im := by linarith
    _ = ((x : ℂ) + I * (T : ℂ) - a).im := by simp
    _ ≤ ‖(x : ℂ) + I * (T : ℂ) - a‖ := Complex.im_le_norm _

private lemma node_im_le_half (rho : NontrivialZetaZero) :
    (zetaSpectralCoordinate rho.1).im ≤ 1 / 2 :=
  (le_abs_self _).trans (NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho).le

private lemma conjugate_node_im_le_half (rho : NontrivialZetaZero) :
    (starRingEnd ℂ (zetaSpectralCoordinate rho.1)).im ≤ 1 / 2 := by
  rw [conj_im]
  exact (neg_le_abs _).trans (NontrivialZetaZero.abs_spectralCoordinate_im_lt_half rho).le

/-- The exact upper horizontal mixed channel, with the same node order
and conjugation as the actual boundary Gram. -/
def suzukiXiCarrierUpperHorizontal (rho sigma : NontrivialZetaZero) (T : ℝ) : ℂ :=
  ∫ x : ℝ in -T..T, suzukiXiZeroCarrier ((x : ℂ) + I * (T : ℂ)) /
    ((((x : ℂ) + I * (T : ℂ)) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
      (((x : ℂ) + I * (T : ℂ)) - zetaSpectralCoordinate sigma.1))

/-- Every actual mixed channel has a uniform inverse-square bound on the
whole horizontal line above the zero strip. -/
theorem norm_suzukiXiCarrier_upper_horizontal_integrand_le
    (rho sigma : NontrivialZetaZero) {T : ℝ} (hT : 1 ≤ T) (x : ℝ) :
    ‖suzukiXiZeroCarrier ((x : ℂ) + I * (T : ℂ)) /
      ((((x : ℂ) + I * (T : ℂ)) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
        (((x : ℂ) + I * (T : ℂ)) - zetaSpectralCoordinate sigma.1))‖ ≤ 4 / T ^ 2 := by
  have hC := norm_suzukiXiZeroCarrier_le_one_of_half_le_im
    (z := (x : ℂ) + I * (T : ℂ))
      (by simpa using (show (1 / 2 : ℝ) ≤ T by linarith))
  have hrho := safe_horizontal_distance hT x (conjugate_node_im_le_half rho)
  have hsigma := safe_horizontal_distance hT x (node_im_le_half sigma)
  rw [norm_div, norm_mul]
  calc
    ‖suzukiXiZeroCarrier ((x : ℂ) + I * (T : ℂ))‖ /
        (‖(x : ℂ) + I * (T : ℂ) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)‖ *
          ‖(x : ℂ) + I * (T : ℂ) - zetaSpectralCoordinate sigma.1‖)
      ≤ 1 / ((T / 2) * (T / 2)) := by gcongr
    _ = 4 / T ^ 2 := by ring

/-- The upper mixed horizontal integral is a genuine integral of a
continuous function; no totalized singular integral is used. -/
theorem intervalIntegrable_suzukiXiCarrier_upper_horizontal
    (rho sigma : NontrivialZetaZero) {T : ℝ} (hT : 1 ≤ T) :
    IntervalIntegrable (fun x : ℝ => suzukiXiZeroCarrier ((x : ℂ) + I * (T : ℂ)) /
      ((((x : ℂ) + I * (T : ℂ)) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
        (((x : ℂ) + I * (T : ℂ)) - zetaSpectralCoordinate sigma.1))) volume (-T) T := by
  have hp : Continuous (fun x : ℝ => (x : ℂ) + I * (T : ℂ)) := by fun_prop
  have hC : Continuous (fun x : ℝ => suzukiXiZeroCarrier ((x : ℂ) + I * (T : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (analyticAt_suzukiXiZeroCarrier_of_half_le_im
      (by simpa using (show (1 / 2 : ℝ) ≤ T by linarith))).continuousAt.comp
        hp.continuousAt
  apply (hC.div ((hp.sub continuous_const).mul (hp.sub continuous_const)) ?_).intervalIntegrable
  intro x
  apply mul_ne_zero
  · exact norm_pos_iff.mp ((by linarith : 0 < T / 2).trans_le
      (safe_horizontal_distance hT x (conjugate_node_im_le_half rho)))
  · exact norm_pos_iff.mp ((by linarith : 0 < T / 2).trans_le
      (safe_horizontal_distance hT x (node_im_le_half sigma)))

/-- Uniform quantitative decay of the actual outer horizontal side,
simultaneously applicable to every genuine mixed pair. -/
theorem norm_suzukiXiCarrierUpperHorizontal_le
    (rho sigma : NontrivialZetaZero) {T : ℝ} (hT : 1 ≤ T) :
    ‖suzukiXiCarrierUpperHorizontal rho sigma T‖ ≤ 8 / T := by
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := T) (fun x _ =>
      norm_suzukiXiCarrier_upper_horizontal_integrand_le rho sigma hT x)
  change ‖suzukiXiCarrierUpperHorizontal rho sigma T‖ ≤ _ at hnorm
  have hTpos : 0 < T := by linarith
  calc
    ‖suzukiXiCarrierUpperHorizontal rho sigma T‖ ≤ (4 / T ^ 2) * |T - -T| := hnorm
    _ = 8 / T := by rw [abs_of_nonneg (by linarith)]; field_simp; ring

/-- The complete outer upper side tends to zero, with all mixed node
information retained in the original integral. -/
theorem tendsto_suzukiXiCarrierUpperHorizontal (rho sigma : NontrivialZetaZero) :
    Tendsto (suzukiXiCarrierUpperHorizontal rho sigma) atTop (𝓝 0) := by
  have hdecay : Tendsto (fun T : ℝ => 8 / T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hdecay
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  exact norm_suzukiXiCarrierUpperHorizontal_le rho sigma hT

/-- The lower horizontal reflected channel, parametrized from left to
right. A positively oriented rectangle traverses this side in the
opposite direction from its upper side. -/
def suzukiXiCarrierLowerHorizontal (rho sigma : NontrivialZetaZero) (T : ℝ) : ℂ :=
  ∫ x : ℝ in -T..T, suzukiXiSharpCarrier ((x : ℂ) - I * (T : ℂ)) /
    ((((x : ℂ) - I * (T : ℂ)) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
      (((x : ℂ) - I * (T : ℂ)) - zetaSpectralCoordinate sigma.1))

private lemma lower_horizontal_eq_conj_upper (rho sigma : NontrivialZetaZero) (T x : ℝ) :
    suzukiXiSharpCarrier ((x : ℂ) - I * (T : ℂ)) /
      ((((x : ℂ) - I * (T : ℂ)) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
        (((x : ℂ) - I * (T : ℂ)) - zetaSpectralCoordinate sigma.1)) =
      starRingEnd ℂ (suzukiXiZeroCarrier ((x : ℂ) + I * (T : ℂ)) /
        ((((x : ℂ) + I * (T : ℂ)) - starRingEnd ℂ (zetaSpectralCoordinate sigma.1)) *
          (((x : ℂ) + I * (T : ℂ)) - zetaSpectralCoordinate rho.1))) := by
  simp only [suzukiXiSharpCarrier, map_div₀, map_mul, map_sub, map_add, conj_ofReal,
    conj_I, starRingEnd_self_apply, neg_mul, sub_neg_eq_add, ← sub_eq_add_neg]
  congr 1
  ring

/-- Exact reflection of the two outer sides exchanges the mixed node
indices; no off-diagonal phase is discarded. -/
theorem suzukiXiCarrierLowerHorizontal_eq_conj_upper
    (rho sigma : NontrivialZetaZero) (T : ℝ) :
    suzukiXiCarrierLowerHorizontal rho sigma T =
      starRingEnd ℂ (suzukiXiCarrierUpperHorizontal sigma rho T) := by
  unfold suzukiXiCarrierLowerHorizontal suzukiXiCarrierUpperHorizontal
  rw [← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr
  intro x _
  exact lower_horizontal_eq_conj_upper rho sigma T x

/-- The reflected lower outer integral is genuinely integrable, including
every mixed pair and without a zero simplicity assumption. -/
theorem intervalIntegrable_suzukiXiCarrier_lower_horizontal
    (rho sigma : NontrivialZetaZero) {T : ℝ} (hT : 1 ≤ T) :
    IntervalIntegrable (fun x : ℝ => suzukiXiSharpCarrier ((x : ℂ) - I * (T : ℂ)) /
      ((((x : ℂ) - I * (T : ℂ)) - starRingEnd ℂ (zetaSpectralCoordinate rho.1)) *
        (((x : ℂ) - I * (T : ℂ)) - zetaSpectralCoordinate sigma.1))) volume (-T) T := by
  have hu := intervalIntegrable_suzukiXiCarrier_upper_horizontal sigma rho hT
  simp_rw [lower_horizontal_eq_conj_upper]
  exact ⟨(Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hu.1,
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hu.2⟩

/-- The reflected outer side has the same uniform `8/T` bound. -/
theorem norm_suzukiXiCarrierLowerHorizontal_le
    (rho sigma : NontrivialZetaZero) {T : ℝ} (hT : 1 ≤ T) :
    ‖suzukiXiCarrierLowerHorizontal rho sigma T‖ ≤ 8 / T := by
  rw [suzukiXiCarrierLowerHorizontal_eq_conj_upper, norm_conj]
  exact norm_suzukiXiCarrierUpperHorizontal_le sigma rho hT

/-- The reflected outer side tends to zero with its exact mixed-index
reflection retained. -/
theorem tendsto_suzukiXiCarrierLowerHorizontal (rho sigma : NontrivialZetaZero) :
    Tendsto (suzukiXiCarrierLowerHorizontal rho sigma) atTop (𝓝 0) := by
  change Tendsto (fun T => suzukiXiCarrierLowerHorizontal rho sigma T) atTop (𝓝 0)
  simpa only [suzukiXiCarrierLowerHorizontal_eq_conj_upper, Function.comp_def, map_zero] using
    Complex.continuous_conj.continuousAt.tendsto.comp
      (tendsto_suzukiXiCarrierUpperHorizontal sigma rho)

end

end RiemannGaussian
