/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszNegativeModeSupport
import RiemannGaussian.ZetaRieszShiftedZeroModes
import RiemannGaussian.ZetaMoebiusMassBound
import Mathlib.Topology.Algebra.Order.Floor

/-!
# The infinite-divisor support passage needs more than coefficient summability

Finite canonical windows retain every actual multiplicity and vanish on
strict-core tests. The complete xi count factor has a different normal
growth problem. Reflection exposes the factorial Gamma growth. Taking a
fixed number of d-primitives cannot turn that response into a bounded
Laplace transform along the cone-normal direction.
-/

namespace RiemannGaussian.ZetaRieszInfiniteModeAudit
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped BigOperators Classical

/-- Explicit repeated copies, rather than replacing analytic multiplicity by one. -/
def zeroCopies (W : Finset NontrivialZetaZero) :
    Finset (Sigma (fun _ : NontrivialZetaZero => ℕ)) :=
  W.sigma (fun rho => Finset.range (analyticZetaZeroMultiplicity rho))

theorem zeroCopies_card (W : Finset NontrivialZetaZero) :
    (zeroCopies W).card = ∑ rho ∈ W, analyticZetaZeroMultiplicity rho := by
  simp [zeroCopies, Finset.card_sigma]

/-- Every finite genuine divisor, with all multiplicities, misses every
strict-core test. No simplicity, exposure or rightmost hypothesis enters. -/
theorem finite_zero_core_support (W : Finset NontrivialZetaZero) (r : ℕ) (y : ℝ)
    {f : ZetaRieszNegativeModeSupport.Test}
    (hf : tsupport (Function.uncurry f) ⊆ {x : ℝ×ℝ | x.2 < x.1}) :
    ZetaRieszNegativeModeSupport.inversePrimitive r (zeroCopies W)
      (fun i => i.1.1-ZetaRieszShiftedCenter.center y) f = 0 :=
  ZetaRieszNegativeModeSupport.inversePrimitive_support _ _ _ hf

/-- Convergence on the restricted test space is automatic. This does not
identify a global inverse or justify exchanging the complete count transform. -/
theorem canonical_windows_core_limit (r : ℕ) (y : ℝ)
    {f : ZetaRieszNegativeModeSupport.Test}
    (hf : tsupport (Function.uncurry f) ⊆ {x : ℝ×ℝ | x.2 < x.1}) :
    Tendsto (fun n => ZetaRieszNegativeModeSupport.inversePrimitive r
      (zeroCopies (riemannXiCanonicalZeroWindow n))
      (fun i => i.1.1-ZetaRieszShiftedCenter.center y) f) atTop (𝓝 0) := by
  simpa only [finite_zero_core_support _ _ _ hf] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

/-- The normalized count factor associated with the full xi logarithmic derivative. -/
def xiFactor (s z : ℂ) : ℂ := riemannXi s/riemannXi (s+z)

theorem xiFactor_zero {s : ℂ} (hs : riemannXi s ≠ 0) : xiFactor s 0 = 1 := by
  simp [xiFactor, hs]

/-- The count factor solves the exact exponential/count ODE of the genuine
global xi term, rather than a separate-leg phase approximation. -/
theorem hasDerivAt_xiFactor (s z : ℂ) (hz : riemannXi (s+z) ≠ 0) :
    HasDerivAt (xiFactor s) (-logDeriv riemannXi (s+z)*xiFactor s z) z := by
  have h := (differentiable_riemannXi (s+z)).hasDerivAt.comp z
    ((hasDerivAt_id z).const_add s)
  have hh : HasDerivAt (fun t => riemannXi (s+t)) (deriv riemannXi (s+z)) z := by
    simpa only [Function.comp_def, mul_one] using h
  have he := (hasDerivAt_const z (riemannXi s)).div hh hz
  have hd : (0 * riemannXi (s+z) - riemannXi s * deriv riemannXi (s+z)) /
      riemannXi (s+z)^2 = -logDeriv riemannXi (s+z)*xiFactor s z := by
    simp only [zero_mul, zero_sub, logDeriv_apply, xiFactor]
    field_simp
  exact hd ▸ he

/-- The exact global-divisor ODE, including its constant boundary channel.
The sum uses actual analytic multiplicities and the inverse-square
summable Cauchy difference. It is not a bare infinite product assertion. -/
theorem hasDerivAt_xiFactor_global (s z : ℂ)
    (hs : riemannXi s ≠ 0) (hz : riemannXi (s+z) ≠ 0) :
    HasDerivAt (xiFactor s)
      (-(logDeriv riemannXi s +
        ∑' rho : NontrivialZetaZero, zetaLogDerivDifferenceSummand (s+z) s rho) *
        xiFactor s z) z := by
  rw [tsum_zetaLogDerivDifference hz hs, add_sub_cancel]
  exact hasDerivAt_xiFactor s z hz

/-- Complete xi count response, retaining the same empty-cofactor subtraction. -/
def xiResponse (s z : ℂ) : ℂ := (1-xiFactor s z)/z^2

/-- A factorial lower bound at genuine positive even arguments. The xi
normalization of this repository is s(1-s) Gamma_R(s) zeta(s). -/
theorem xi_even_lower (n : ℕ) :
    (n.factorial : ℝ)/Real.pi^(n+1) ≤ ‖riemannXi (2*((n : ℂ)+1))‖ := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hs : 1 < (2*((n : ℂ)+1)).re := by simp; linarith
  have hz : 1 ≤ ‖riemannZeta (2*((n : ℂ)+1))‖ := by
    have h := (one_le_moebiusDirichletMass (by linarith : 1 < 2*((n : ℝ)+1))).trans
      (moebiusDirichletMass_le_norm_zeta (by linarith : 1 < 2*((n : ℝ)+1)))
    simpa using h
  have hg : Complex.Gammaℝ (2*((n : ℂ)+1)) =
      ((Real.pi : ℂ)^(n+1))⁻¹ * (n.factorial : ℂ) := by
    rw [Complex.Gammaℝ_def]
    have he : -(2*((n : ℂ)+1))/2 = -((n+1 : ℕ) : ℂ) := by push_cast; ring
    have he' : 2*((n : ℂ)+1)/2 = (n : ℂ)+1 := by ring
    rw [he, he', Complex.cpow_neg, Complex.cpow_natCast, Complex.Gamma_nat_eq_factorial]
  rw [riemannXi_eq_mul_Gammaℝ_riemannZeta_of_one_lt_re hs, hg]
  have hnorm0 : ‖2*((n : ℂ)+1)‖ = 2*((n : ℝ)+1) := by
    rw [show 2*((n : ℂ)+1) = ((2*((n : ℝ)+1) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hnorm1 : ‖1-2*((n : ℂ)+1)‖ = 2*(n : ℝ)+1 := by
    rw [show 1-2*((n : ℂ)+1) = ((-(2*(n : ℝ)+1) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, norm_neg, Real.norm_of_nonneg (by positivity)]
  simp only [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_natCast, hnorm0, hnorm1]
  have ha : 0 ≤ (Real.pi^(n+1))⁻¹*(n.factorial : ℝ) := by positivity
  have hp : 1 ≤ 2*((n : ℝ)+1)*(2*n+1) := by nlinarith
  calc
    _ = (Real.pi^(n+1))⁻¹*(n.factorial : ℝ) := by ring
    _ ≤ (2*((n : ℝ)+1)*(2*n+1))*((Real.pi^(n+1))⁻¹*(n.factorial : ℝ))*
        ‖riemannZeta (2*((n : ℂ)+1))‖ := by
      calc
        _ = 1*((Real.pi^(n+1))⁻¹*(n.factorial : ℝ))*1 := by ring
        _ ≤ _ := by gcongr
    _ = _ := by ring

private theorem geometric_over_polynomial (r : ℕ) :
    Tendsto (fun n : ℕ => (2 : ℝ)^n/((n : ℝ)+1)^r) atTop atTop := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt r (by norm_num : (1 : ℝ) < 2)).comp
    (tendsto_add_atTop_nat 1)
  have he : Tendsto (fun n : ℕ => ((n : ℝ)+1)^r/(2 : ℝ)^n) atTop (𝓝 0) := by
    convert h.mul_const 2 using 1
    · ext n
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    · simp
  have hep : ∀ᶠ n : ℕ in atTop, 0 < ((n : ℝ)+1)^r/(2 : ℝ)^n :=
    Eventually.of_forall (fun n => by positivity)
  have hh := tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨he, hep⟩)
  simpa only [Function.comp_def, inv_div] using hh

/-- No fixed polynomial division pays the genuine Gamma growth of xi. -/
theorem xi_even_div_polynomial_tendsto (r : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    Tendsto (fun n : ℕ => ‖riemannXi (2*((n : ℂ)+1))‖/(v+2*(n : ℝ)+1)^r)
      atTop atTop := by
  have hg := (geometric_over_polynomial r).atTop_div_const
    (by positivity : 0 < Real.pi*(v+2)^r)
  apply tendsto_atTop_mono' _ _ hg
  filter_upwards [FloorSemiring.eventually_mul_pow_lt_factorial_sub (1 : ℝ)
    (2*Real.pi) 0] with n hn
  simp only [Nat.sub_zero, one_mul] at hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have ht : 0 < v+2*(n : ℝ)+1 := by positivity
  have hfac : (2 : ℝ)^n/Real.pi ≤ (n.factorial : ℝ)/Real.pi^(n+1) := by
    rw [div_le_div_iff₀ Real.pi_pos (pow_pos Real.pi_pos _), pow_succ]
    have h := hn.le
    rw [mul_pow] at h
    nlinarith [mul_le_mul_of_nonneg_right h Real.pi_pos.le]
  calc
    _ = (2 : ℝ)^n/Real.pi/((v+2)*((n : ℝ)+1))^r := by rw [mul_pow]; ring
    _ ≤ (2 : ℝ)^n/Real.pi/(v+2*(n : ℝ)+1)^r := by gcongr; nlinarith
    _ ≤ ‖riemannXi (2*((n : ℂ)+1))‖/(v+2*(n : ℝ)+1)^r := by
      gcongr
      exact hfac.trans (xi_even_lower n)

private theorem xi_real_ne_zero {v : ℝ} (hv : 1 < v) : riemannXi (v : ℂ) ≠ 0 := by
  intro h
  have hz := (riemannXi_eq_zero_iff_isNontrivialZetaZero (v : ℂ)).mp h
  have hr := NontrivialZetaZero.re_lt_one ⟨(v : ℂ), hz⟩
  simp only [Complex.ofReal_re] at hr
  linarith

/-- Along a fixed tangential coordinate v>1, every fixed primitive of the
actual xi count response is unbounded in the positive normal direction.
This is actual xi Gamma growth, not a synthetic zero configuration. -/
theorem xi_response_normal_growth (r : ℕ) {v : ℝ} (hv : 1 < v) :
    Tendsto (fun n : ℕ =>
      ‖xiResponse ((v : ℂ)-((v+2*(n : ℝ)+1 : ℝ) : ℂ))
        ((v+2*(n : ℝ)+1 : ℝ) : ℂ) /
        ((v+2*(n : ℝ)+1 : ℝ) : ℂ)^r‖) atTop atTop := by
  have hv0 : 0 ≤ v := by linarith
  have hb : 0 < ‖riemannXi (v : ℂ)‖ := norm_pos_iff.mpr (xi_real_ne_zero hv)
  have hg := (xi_even_div_polynomial_tendsto (r+2) hv0).atTop_div_const hb
  have hg' := tendsto_atTop_add_const_right atTop (-1 : ℝ) hg
  apply tendsto_atTop_mono' _ _ hg'
  filter_upwards [] with n
  let t : ℝ := v+2*(n : ℝ)+1
  have ht : 1 ≤ t := by dsimp [t]; linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]
  have ht0 : 0 < t := by linarith
  have hp : 1 ≤ t^(r+2) := one_le_pow₀ ht
  have he : riemannXi ((v : ℂ)-(t : ℂ)) = riemannXi (2*((n : ℂ)+1)) := by
    rw [show (v : ℂ)-(t : ℂ) = 1-2*((n : ℂ)+1) by dsimp [t]; push_cast; ring,
      riemannXi_one_sub]
  change ‖riemannXi (2*((n : ℂ)+1))‖/t^(r+2)/‖riemannXi (v : ℂ)‖ + (-1) ≤
    ‖xiResponse ((v : ℂ)-(t : ℂ)) (t : ℂ)/(t : ℂ)^r‖
  rw [xiResponse, xiFactor, sub_add_cancel, he]
  simp only [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht0.le]
  have hnorm := norm_sub_norm_le (riemannXi (2*((n : ℂ)+1))/riemannXi (v : ℂ)) 1
  rw [norm_one, norm_div, norm_sub_rev] at hnorm
  have hh := div_le_div_of_nonneg_right hnorm (by positivity : 0 ≤ t^(r+2))
  have hi : 1/t^(r+2) ≤ 1 := (div_le_one (by positivity)).mpr hp
  have hid : (‖riemannXi (2*((n : ℂ)+1))‖/‖riemannXi (v : ℂ)‖-1)/t^(r+2) =
      ‖riemannXi (2*((n : ℂ)+1))‖/t^(r+2)/‖riemannXi (v : ℂ)‖ - 1/t^(r+2) := by ring
  rw [hid] at hh
  have heq : ‖1-riemannXi (2*((n : ℂ)+1))/riemannXi (v : ℂ)‖/t^2/t^r =
      ‖1-riemannXi (2*((n : ℂ)+1))/riemannXi (v : ℂ)‖/t^(r+2) := by
    rw [div_div, pow_add, mul_comm (t^2) (t^r)]
  rw [heq]
  linarith

/-- The ordinary cone and its transform in tangential/normal coordinates.
The original Laplace variables are w=v-z and z. -/
def supportCone : Set (ℝ×ℝ) := {x | 0 ≤ x.1 ∧ x.1 ≤ x.2}

/-- The ordinary cone transform, with a complex tangential and real normal parameter. -/
def coneLaplace (F : ℝ×ℝ → ℂ) (v : ℂ) (z : ℝ) : ℂ :=
  ∫ x in supportCone, Complex.exp (-v*x.1-(z : ℂ)*(x.2-x.1))*F x

/-- A single integrable majorant for an ordinary cone-supported primitive
forces a uniform bound in the whole positive normal direction. -/
theorem coneLaplace_norm_le {F : ℝ×ℝ → ℂ} {v : ℂ} {b z : ℝ} (hz : b ≤ z)
    (hF : IntegrableOn (fun x : ℝ×ℝ =>
      Real.exp (-v.re*x.1-b*(x.2-x.1))*‖F x‖) supportCone) :
    ‖coneLaplace F v z‖ ≤
      ∫ x in supportCone, Real.exp (-v.re*x.1-b*(x.2-x.1))*‖F x‖ := by
  apply norm_integral_le_of_norm_le hF
  filter_upwards [ae_restrict_mem (by
    exact (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_fst continuous_snd) |>.measurableSet)] with x hx
  have hnon : b*(x.2-x.1) ≤ z*(x.2-x.1) :=
    mul_le_mul_of_nonneg_right hz (sub_nonneg.mpr hx.2)
  simp only [norm_mul, Complex.norm_exp, sub_re, mul_re, ofReal_re, ofReal_im,
    neg_re, neg_im, zero_mul, mul_zero, sub_zero]
  gcongr

/-- No fixed d-primitive of the full xi response is an ordinary inverse
with the uniform exponentially weighted cone majorant proposed for the
finite-window dominated passage. This is not a no-go for every possible
generalized inverse or for the original arithmetic packet. -/
theorem no_dominated_cone_primitive (r : ℕ) (b : ℝ) {v : ℝ} (hv : 1 < v) :
    ¬ ∃ F : ℝ×ℝ → ℂ,
      IntegrableOn (fun x : ℝ×ℝ => Real.exp (-v*x.1-b*(x.2-x.1))*‖F x‖) supportCone ∧
      ∀ᶠ n : ℕ in atTop,
        coneLaplace F v (v+2*(n : ℝ)+1) =
          xiResponse ((v : ℂ)-((v+2*(n : ℝ)+1 : ℝ) : ℂ))
            ((v+2*(n : ℝ)+1 : ℝ) : ℂ) /
            ((v+2*(n : ℝ)+1 : ℝ) : ℂ)^r := by
  rintro ⟨F, hF, heq⟩
  let M := ∫ x in supportCone, Real.exp (-v*x.1-b*(x.2-x.1))*‖F x‖
  have hg := (xi_response_normal_growth r hv).eventually_gt_atTop M
  obtain ⟨n, hn, hgn, hbn⟩ := (heq.and (hg.and (eventually_ge_atTop (Nat.ceil b)))).exists
  have hnb : b ≤ (n : ℝ) := (Nat.le_ceil b).trans (by exact_mod_cast hbn)
  have hb := coneLaplace_norm_le (F := F) (v := v) (b := b)
    (z := v+2*(n : ℝ)+1) (by linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n]) hF
  rw [hn] at hb
  exact (not_lt_of_ge hb) hgn

/-- The actual center shift changes only the tangential exponential
weight; it does not repair the normal-direction domination obstruction. -/
theorem no_dominated_shifted_cone_primitive (r : ℕ) (y b : ℝ)
    {v : ℝ} (hv : 1 < v) :
    ¬ ∃ F : ℝ×ℝ → ℂ,
      IntegrableOn (fun x : ℝ×ℝ =>
        Real.exp (-(v-3/2)*x.1-b*(x.2-x.1))*‖F x‖) supportCone ∧
      ∀ᶠ n : ℕ in atTop,
        coneLaplace F ((v : ℂ)-ZetaRieszShiftedCenter.center y) (v+2*(n : ℝ)+1) =
          xiResponse (ZetaRieszShiftedCenter.center y+
            ((v : ℂ)-ZetaRieszShiftedCenter.center y-((v+2*(n : ℝ)+1 : ℝ) : ℂ)))
            ((v+2*(n : ℝ)+1 : ℝ) : ℂ) / ((v+2*(n : ℝ)+1 : ℝ) : ℂ)^r := by
  rintro ⟨F, hF, heq⟩
  let M := ∫ x in supportCone, Real.exp (-(v-3/2)*x.1-b*(x.2-x.1))*‖F x‖
  have hg := (xi_response_normal_growth r hv).eventually_gt_atTop M
  obtain ⟨n, hn, hgn, hbn⟩ := (heq.and (hg.and (eventually_ge_atTop (Nat.ceil b)))).exists
  have hnb : b ≤ (n : ℝ) := (Nat.le_ceil b).trans (by exact_mod_cast hbn)
  have hvre : ((v : ℂ)-ZetaRieszShiftedCenter.center y).re = v-3/2 := by
    simp [ZetaRieszShiftedCenter.center]
  have hb := coneLaplace_norm_le (F := F)
    (v := (v : ℂ)-ZetaRieszShiftedCenter.center y) (b := b)
    (z := v+2*(n : ℝ)+1) (by linarith [show 0 ≤ (n : ℝ) from Nat.cast_nonneg n])
    (by simpa only [hvre] using hF)
  rw [hn, hvre] at hb
  have hs : ZetaRieszShiftedCenter.center y+
      ((v : ℂ)-ZetaRieszShiftedCenter.center y-((v+2*(n : ℝ)+1 : ℝ) : ℂ)) =
      (v : ℂ)-((v+2*(n : ℝ)+1 : ℝ) : ℂ) := by ring
  rw [hs] at hb
  exact (not_lt_of_ge hb) hgn

end
end RiemannGaussian.ZetaRieszInfiniteModeAudit
