import RiemannGaussian.EtaZetaDyadicRectangle
import Mathlib.Analysis.Complex.Liouville

/-!
# Quantitative horizontal control from the literal eta bound

Cauchy's estimate on a fixed-radius disc turns the pole-removed strip bound
into an explicit derivative estimate. A real horizontal mean-value bound
then compares actual zeta values to an actual zero without assuming a
derivative or growth hypothesis.
-/

open Complex Filter MeasureTheory Metric Set Topology
open scoped Classical ComplexConjugate ENNReal Interval Topology

namespace RiemannGaussian

noncomputable section

/-- Cauchy's estimate gives a uniform derivative bound on the narrower
strip, with all ordinate dependence explicit. -/
theorem norm_deriv_riemannZeta₁_le_etaStrip {s : ℂ}
    (hslo : 3 / 4 ≤ s.re) (hshi : s.re ≤ 5 / 4) :
    ‖deriv riemannZeta₁ s‖ ≤ 32 * (|s.im| + 21) ^ 2 := by
  have hbound (z : ℂ) (hz : z ∈ sphere s (1 / 4 : ℝ)) :
      ‖riemannZeta₁ z‖ ≤ 8 * (|s.im| + 21) ^ 2 := by
    have hdist : ‖z - s‖ = 1 / 4 := by simpa only [mem_sphere, dist_eq_norm] using hz
    have hre : |z.re - s.re| ≤ 1 / 4 := by
      simpa only [Complex.sub_re, hdist] using Complex.abs_re_le_norm (z - s)
    have him : |z.im - s.im| ≤ 1 / 4 := by
      simpa only [Complex.sub_im, hdist] using Complex.abs_im_le_norm (z - s)
    have hzlo : 1 / 2 ≤ z.re := by linarith [(abs_le.mp hre).1]
    have hzhi : z.re ≤ 3 / 2 := by linarith [(abs_le.mp hre).2]
    have himabs : |z.im| + 20 ≤ |s.im| + 21 := by
      have h := abs_add_le (z.im - s.im) s.im
      rw [sub_add_cancel] at h
      linarith
    exact (norm_riemannZeta₁_le_etaStrip hzlo hzhi).trans (by gcongr)
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 4) differentiable_riemannZeta₁.diffContOnCl hbound
  convert h using 1
  ring

/-- The pole-removed zeta function is quantitatively Lipschitz on every
horizontal segment in the narrower strip. -/
theorem norm_riemannZeta₁_sub_le_etaStrip_horizontal {u v : ℝ} (y : ℝ)
    (hu : u ∈ Icc (3 / 4 : ℝ) (5 / 4)) (hv : v ∈ Icc (3 / 4 : ℝ) (5 / 4)) :
    ‖riemannZeta₁ ((v : ℂ) + I * y) - riemannZeta₁ ((u : ℂ) + I * y)‖ ≤
      32 * (|y| + 21) ^ 2 * |v - u| := by
  have hderiv (x : ℝ) (_hx : x ∈ Icc (3 / 4 : ℝ) (5 / 4)) :
      HasDerivWithinAt (fun t : ℝ ↦ riemannZeta₁ ((t : ℂ) + I * y))
        (deriv riemannZeta₁ ((x : ℂ) + I * y)) (Icc (3 / 4 : ℝ) (5 / 4)) x := by
    have hc : HasDerivAt (fun z : ℂ ↦ riemannZeta₁ (z + I * y))
        (deriv riemannZeta₁ ((x : ℂ) + I * y)) (x : ℂ) := by
      simpa only [mul_one, Function.comp_def, id_eq] using
        (differentiable_riemannZeta₁ ((x : ℂ) + I * y)).hasDerivAt.comp (x : ℂ)
          ((hasDerivAt_id (x : ℂ)).add_const (I * y))
    exact hc.comp_ofReal.hasDerivWithinAt
  have hbound (x : ℝ) (hx : x ∈ Icc (3 / 4 : ℝ) (5 / 4)) :
      ‖deriv riemannZeta₁ ((x : ℂ) + I * y)‖ ≤ 32 * (|y| + 21) ^ 2 := by
    have hlo : 3 / 4 ≤ (((x : ℂ) + I * y)).re := by simpa using hx.1
    have hhi : (((x : ℂ) + I * y)).re ≤ 5 / 4 := by simpa using hx.2
    simpa using norm_deriv_riemannZeta₁_le_etaStrip hlo hhi
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound (convex_Icc _ _) hu hv

/-- At every actual zeta zero the entire pole-removed function also
vanishes; the point one is excluded by the original zero carrier. -/
theorem riemannZeta₁_nontrivialZetaZero (rho : NontrivialZetaZero) : riemannZeta₁ rho.1 = 0 := by
  have h := riemannZeta_eq_inv_sub_mul rho.2.2.2
  rw [rho.2.1] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (inv_ne_zero (sub_ne_zero.mpr rho.2.2.2))

/-- A zero near the right edge forces an explicit small value at its
equally displaced point to the right of one, at the original ordinate. -/
theorem norm_riemannZeta₁_reflected_across_one_le (rho : NontrivialZetaZero)
    (hrho : 3 / 4 ≤ rho.1.re) :
    ‖riemannZeta₁ (((2 - rho.1.re : ℝ) : ℂ) + I * rho.1.im)‖ ≤
      64 * (|rho.1.im| + 21) ^ 2 * (1 - rho.1.re) := by
  have hre := NontrivialZetaZero.re_lt_one rho
  have hu : rho.1.re ∈ Icc (3 / 4 : ℝ) (5 / 4) := ⟨hrho, by linarith⟩
  have hv : 2 - rho.1.re ∈ Icc (3 / 4 : ℝ) (5 / 4) := ⟨by linarith, by linarith⟩
  have h := norm_riemannZeta₁_sub_le_etaStrip_horizontal rho.1.im hu hv
  have he : ((rho.1.re : ℝ) : ℂ) + I * rho.1.im = rho.1 := by
    simpa only [mul_comm I] using Complex.re_add_im rho.1
  rw [he, riemannZeta₁_nontrivialZetaZero, sub_zero,
    abs_of_nonneg (by linarith : 0 ≤ 2 - rho.1.re - rho.1.re)] at h
  exact h.trans_eq (by ring)

end

end RiemannGaussian
