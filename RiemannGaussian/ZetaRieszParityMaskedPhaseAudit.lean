/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszParityInsertionTail
import RiemannGaussian.ZetaRieszEulerPrimeHeadDensity

/-!
# A quantitative obstruction to inferring masked phases from complete moments

This is an explicit analytic-mode counterexample, not actual zeta zeros,
prime data, or a counterexample to the literal FullParityPacket estimate.
Both individual modes are farther than the requested exposed radius.
A correlated total-order integral over the actual largest-share interval
has a closer resonant endpoint. Thus separate complete-moment limits do
not, on their own, justify the remaining coupled mask transfer.
-/

namespace RiemannGaussian.ZetaRieszParityMaskedPhaseAudit
noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/-- The upper radius of the current restricted test. -/
def radius : ℝ := 10001/20000
/-- Common real part of the model modes, strictly below the radius. -/
def axis : ℝ := 20001/40000
/-- First analytic test mode; it is not asserted to be a zeta zero. -/
def leftMode : ℂ := (axis : ℂ)+Complex.I/10
/-- Second test mode, chosen to resonate at the lower share endpoint. -/
def rightMode : ℂ := (axis : ℂ)-43*Complex.I/370
/-- The correlated denominator selected by a fixed logarithmic share. -/
def pole (q : ℝ) : ℂ := (q : ℂ)*leftMode+(1-(q : ℂ))*rightMode
/-- Nonzero derivative of the affine correlated denominator. -/
def slope : ℂ := (8/37 : ℂ)*Complex.I

theorem pole_affine (q : ℝ) : pole q = (axis : ℂ)+slope*((q : ℂ)-43/80) := by
  unfold pole leftMode rightMode slope
  ring

theorem pole_ne_zero (q : ℝ) : pole q ≠ 0 := by
  intro h
  have hh := congrArg Complex.re h
  rw [pole_affine] at hh
  norm_num [slope, axis] at hh

theorem mode_geometry :
    axis < radius ∧ radius < ‖leftMode‖ ∧ radius < ‖rightMode‖ ∧
      pole (43/80) = (axis : ℂ) ∧ pole (9/16) = (axis : ℂ)+Complex.I/185 ∧
      radius < ‖pole (9/16)‖ := by
  have hleft : (radius : ℝ)^2 < ‖leftMode‖^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [radius, axis, leftMode, Complex.normSq_apply]
  have hright : (radius : ℝ)^2 < ‖rightMode‖^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    norm_num [radius, axis, rightMode, Complex.normSq_apply]
  have hlo : pole (43/80) = (axis : ℂ) := by rw [pole_affine]; norm_num
  have hhi : pole (9/16) = (axis : ℂ)+Complex.I/185 := by rw [pole_affine]; norm_num [slope]; ring
  have hhigh : (radius : ℝ)^2 < ‖pole (9/16)‖^2 := by
    rw [hhi, ← Complex.normSq_eq_norm_sq]
    norm_num [radius, axis, Complex.normSq_apply]
  have hu : (0 : ℝ) < radius := by norm_num [radius]
  exact ⟨by norm_num [axis, radius], by nlinarith [norm_nonneg leftMode],
    by nlinarith [norm_nonneg rightMode], hlo, hhi, by nlinarith [norm_nonneg (pole (9/16))]⟩

/-- Each complete leg is geometrically negligible. Adding it to minus
one therefore preserves the simple-zero one-leg phase limit. -/
theorem complete_modes_tendsto :
    Tendsto (fun k : ℕ => ((radius : ℂ)/leftMode)^k) atTop (𝓝 0) ∧
    Tendsto (fun k : ℕ => ((radius : ℂ)/rightMode)^k) atTop (𝓝 0) := by
  have hu : (0 : ℝ) < radius := by norm_num [radius]
  constructor
  · apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hu.le]
    exact (div_lt_one (hu.trans mode_geometry.2.1)).mpr mode_geometry.2.1
  · apply tendsto_pow_atTop_nhds_zero_of_norm_lt_one
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hu.le]
    exact (div_lt_one (hu.trans mode_geometry.2.2.1)).mpr mode_geometry.2.2.1

/-- The counterexample meets the strengthened *uniform* lower-order
requirement, including the newly paid `N/200` cutoff. It is not caused
by order-zero atoms or by choosing orders outside that range. -/
theorem eventually_uniform_complete_modes {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, N ≤ 200*k →
      ‖((radius : ℂ)/leftMode)^k‖ < ε ∧
      ‖((radius : ℂ)/rightMode)^k‖ < ε := by
  have hl := (tendsto_order.1 complete_modes_tendsto.1.norm).2 ε (by simpa using hε)
  have hr := (tendsto_order.1 complete_modes_tendsto.2.norm).2 ε (by simpa using hε)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hl.and hr)
  filter_upwards [eventually_ge_atTop (200*K)] with N hN
  intro k hk
  exact hK k (by omega)

/-- A correlated total-order integral, retaining the hard share interval. -/
def band (N : ℕ) : ℂ :=
  ∫ q : ℝ in (43/80)..(9/16), ((radius : ℂ)/pole q)^(N+2)

theorem band_eq (N : ℕ) : band N =
    (radius : ℂ)/(slope*(N+1))*
      (((radius : ℂ)/(axis : ℂ))^(N+1)-((radius : ℂ)/pole (9/16))^(N+1)) := by
  have hu : (radius : ℂ) ≠ 0 := by norm_num [radius]
  have hs : slope ≠ 0 := by simp [slope]
  have hN : (N+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  have hp (q : ℝ) : HasDerivAt pole slope q := by
    have hh := (((hasDerivAt_id q).ofReal_comp.sub_const (43/80 : ℂ)).const_mul slope).const_add (axis : ℂ)
    simp only [id_eq, Complex.ofReal_one, mul_one] at hh
    simpa only [← pole_affine] using hh
  have hd (q : ℝ) : HasDerivAt
      (fun x : ℝ => -(radius : ℂ)/(slope*(N+1))*((radius : ℂ)/pole x)^(N+1))
      (((radius : ℂ)/pole q)^(N+2)) q := by
    have hh := (((hasDerivAt_const q (radius : ℂ)).div (hp q) (pole_ne_zero q)).pow (N+1)).const_mul
      (-(radius : ℂ)/(slope*(N+1)))
    apply hh.congr_deriv
    push_cast
    simp only [Pi.div_apply]
    rw [div_pow, div_pow, pow_succ, pow_succ]
    field_simp
    ring
  have hc : Continuous (fun q : ℝ => ((radius : ℂ)/pole q)^(N+2)) := by
    apply Continuous.pow
    apply Continuous.div continuous_const
    · exact continuous_iff_continuousAt.mpr (fun q => (hp q).continuousAt)
    · exact pole_ne_zero
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun q _ => hd q)
    (hc.intervalIntegrable (43/80) (9/16))
  rw [mode_geometry.2.2.2.1] at hf
  change band N = _ at hf
  rw [hf]
  ring

/-- Normalization exposing the exact nonzero endpoint asymptotic. -/
def damping (N : ℕ) : ℝ := (N+1 : ℝ)*(axis/radius)^(N+1)

theorem scaled_band_eq (N : ℕ) : (damping N : ℂ)*band N =
    (radius : ℂ)/slope*(1-((axis : ℂ)/pole (9/16))^(N+1)) := by
  have hu : (radius : ℂ) ≠ 0 := by norm_num [radius]
  have ha : (axis : ℂ) ≠ 0 := by norm_num [axis]
  have hs : slope ≠ 0 := by simp [slope]
  have hN : (N+1 : ℂ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero N)
  have hlo : ((axis : ℂ)/radius)^(N+1)*((radius : ℂ)/axis)^(N+1) = 1 := by
    rw [← mul_pow]
    field_simp
    simp
  have hhi : ((axis : ℂ)/radius)^(N+1)*((radius : ℂ)/pole (9/16))^(N+1) =
      ((axis : ℂ)/pole (9/16))^(N+1) := by
    rw [← mul_pow]
    congr 1
    field_simp
  rw [band_eq]
  simp only [damping, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_div]
  calc
    _ = (radius : ℂ)/slope*
        (((axis : ℂ)/radius)^(N+1)*((radius : ℂ)/axis)^(N+1)-
         ((axis : ℂ)/radius)^(N+1)*((radius : ℂ)/pole (9/16))^(N+1)) := by
      field_simp
    _ = _ := by rw [hlo, hhi]

theorem damping_tendsto : Tendsto damping atTop (𝓝 0) := by
  have hpos : (0 : ℝ) < axis/radius := by norm_num [axis, radius]
  have hlt : axis/radius < 1 := by norm_num [axis, radius]
  have hh := (ZetaRieszEulerPrimeHeadDensity.tendsto_successor_pow_mul_geometric 1 hpos hlt).mul_const (axis/radius)
  simp only [pow_one, zero_mul] at hh
  apply hh.congr'
  filter_upwards [] with N
  dsimp [damping]
  rw [pow_succ]
  ring

theorem scaled_band_tendsto :
    Tendsto (fun N => (damping N : ℂ)*band N) atTop (𝓝 ((radius : ℂ)/slope)) := by
  have ha : (0 : ℝ) < axis := by norm_num [axis]
  have hbound : axis < ‖pole (9/16)‖ := mode_geometry.1.trans mode_geometry.2.2.2.2.2
  have hnorm : ‖(axis : ℂ)/pole (9/16)‖ < 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le]
    exact (div_lt_one (ha.trans hbound)).mpr hbound
  have hh := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm).comp (tendsto_add_atTop_nat 1)
  have ht := ((tendsto_const_nhds (x := (1 : ℂ))).sub hh).const_mul ((radius : ℂ)/slope)
  simp only [sub_zero, mul_one] at ht
  simpa only [scaled_band_eq, Function.comp_def] using ht

/-- Complete-mode decay does not imply any fixed eventual bound after
this hard share projection. This is a model obstruction to the inference,
not a theorem that the literal arithmetic packet is unbounded. -/
theorem not_eventually_band_bounded (B : ℝ) :
    ¬∀ᶠ N : ℕ in atTop, ‖band N‖ ≤ B := by
  intro hb
  have hn (N : ℕ) : 0 ≤ damping N := by dsimp [damping]; norm_num [axis, radius]; positivity
  have he : ∀ᶠ N : ℕ in atTop, ‖(damping N : ℂ)*band N‖ ≤ damping N*B := by
    filter_upwards [hb] with N hN
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hn N)]
    exact mul_le_mul_of_nonneg_left hN (hn N)
  have hz := squeeze_zero_norm' he (by simpa using damping_tendsto.mul_const B)
  have hzero := tendsto_nhds_unique scaled_band_tendsto hz
  have hu : (radius : ℂ) ≠ 0 := by norm_num [radius]
  have hs : slope ≠ 0 := by simp [slope]
  exact (div_ne_zero hu hs) hzero

/-- An arbitrarily small fixed continuum residual would not rescue
this general transfer rule. The residual must either vanish exactly or
be accompanied by a joint masked arithmetic estimate. This statement
still concerns the analytic model, not actual zeta zeros or the packet. -/
theorem scaled_defect_not_eventually_bounded {c : ℂ} (hc : c ≠ 0) (B : ℝ) :
    ¬∀ᶠ N : ℕ in atTop, ‖c*band N‖ ≤ B := by
  intro hb
  apply not_eventually_band_bounded (B/‖c‖)
  filter_upwards [hb] with N hN
  rw [norm_mul] at hN
  exact (le_div_iff₀ (norm_pos_iff.mpr hc)).mpr (by simpa only [mul_comm] using hN)

/-! ## The actual radial saddle of the same analytic modes

The old `band` is already a complete Gamma-moment response, rather than a
fixed-total-log slice. Inserting its denominator into a second radial
integral would count that integration twice. For the literal radial kernel
the mode density instead contributes `exp ((1/2-pole q)*T)`.

These theorems check the joint exponent and spectral geometry. They are
not an identification or asymptotic theorem for the masked all-count
arithmetic packet, or even for its numerical continuum model.
-/

/-- Exponential rate at `T=t*N`, including the source normalization,
the factorial saddle, and the real part of the correlated mode. -/
def radialExponent (t q : ℝ) : ℝ :=
  1+Real.log (radius*t)-(pole q).re*t

theorem radial_saddle_in_core :
    (39/20 : ℝ) < axis⁻¹ ∧ axis⁻¹ < 203/100 := by
  norm_num [axis]

theorem radial_saddle_exponent :
    radialExponent axis⁻¹ (43/80) = Real.log (radius/axis) := by
  rw [radialExponent, mode_geometry.2.2.2.1]
  have ha : axis ≠ 0 := by norm_num [axis]
  simp only [Complex.ofReal_re, mul_inv_cancel₀ ha, div_eq_mul_inv]
  ring

/-- A strictly positive exponential rate, certified without decimal
evaluation. In particular the radial window contains the dangerous saddle. -/
theorem radial_growth_bounds :
    (1/21000 : ℝ) < Real.log (radius/axis) ∧
      Real.log (radius/axis) < 1/20000 := by
  have hp : 0 < radius/axis := by norm_num [radius, axis]
  have hl := Real.one_sub_inv_le_log_of_pos hp
  have hu := Real.log_le_sub_one_of_pos hp
  norm_num [radius, axis] at hl hu ⊢
  constructor <;> linarith

/-- The requested uniformly negative joint real exponent is impossible
for these modes on the original radial/share rectangle. This is a
pointwise rate obstruction, not a bound on an oscillatory integral. -/
theorem no_uniform_negative_radial_exponent {c : ℝ} (hc : 0 < c) :
    ¬∀ t ∈ Icc (39/20 : ℝ) (203/100),
      ∀ q ∈ Icc (43/80 : ℝ) (9/16), radialExponent t q ≤ -c := by
  intro h
  have hs := h axis⁻¹ ⟨radial_saddle_in_core.1.le, radial_saddle_in_core.2.le⟩
    (43/80) ⟨le_rfl, by norm_num⟩
  rw [radial_saddle_exponent] at hs
  linarith [radial_growth_bounds.1]

/-- Both optimal Gamma window-tail rates strictly exceed the resonant
growth rate. This checks the constants only; it does not assume or assert
a Gamma-tail estimate for the literal carrier. -/
theorem radial_window_rate_margin :
    Real.log (radius/axis) < axis*(39/20)-1-Real.log (axis*(39/20)) ∧
    Real.log (radius/axis) < axis*(203/100)-1-Real.log (axis*(203/100)) := by
  have hlog {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
      Real.log x ≤ x/c+c-2 := by
    have h := add_le_add (Real.log_le_sub_one_of_pos (div_pos hx hc))
      (Real.log_le_sub_one_of_pos hc)
    rw [Real.log_div hx.ne' hc.ne'] at h
    linarith
  have hl := hlog (x := axis*(39/20)) (c := 79/80)
    (by norm_num [axis]) (by norm_num)
  have hh := hlog (x := axis*(203/100)) (c := 403/400)
    (by norm_num [axis]) (by norm_num)
  have hg := radial_growth_bounds.2
  norm_num [axis] at hl hh hg ⊢
  constructor <;> linarith

/-- Assigning at least one cofactor share to the largest prime's mode
moves its total modal share strictly past the resonant endpoint. -/
theorem left_owner_extra_mode_separated {q x : ℝ}
    (hq : 43/80 ≤ q) (hx : 3/250 ≤ x) :
    (43/80+3/250 : ℝ) ≤ q+x ∧ (12/4625 : ℝ) ≤ (pole (q+x)).im := by
  rw [pole_affine]
  norm_num [slope, Complex.mul_im, Complex.mul_re]
  constructor <;> linarith

/-- If the largest prime has the right mode, all left-mode cofactor
shares together lie strictly below the resonant modal share. -/
theorem right_owner_mode_separated {q x : ℝ}
    (hq : 43/80 ≤ q) (hx : x ≤ 1-q) :
    x ≤ (37/80 : ℝ) ∧ (pole x).im ≤ -(3/185 : ℝ) := by
  rw [pole_affine]
  norm_num [slope, Complex.mul_im, Complex.mul_re]
  constructor <;> linarith

end
end RiemannGaussian.ZetaRieszParityMaskedPhaseAudit
