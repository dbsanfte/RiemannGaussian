/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Complex.Schwarz

/-!
# Derivative control from a signed half-plane bound

An analytic function whose imaginary part is nonpositive on a disk has
derivative norm at most twice its central negative imaginary part divided
by the radius. The bound retains that actual signed mass, including the
zero-mass case. It is obtained by a Cayley transform and Schwarz's lemma.
-/

open Complex Filter Metric Set
namespace RiemannGaussian
noncomputable section

private lemma norm_deriv_le_of_im_nonpos_strict_center {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (him : ∀ z ∈ ball c R, (f z).im ≤ 0) (hc : (f c).im < 0) :
    ‖deriv f c‖ ≤ 2 * (-(f c).im) / R := by
  let g : ℂ → ℂ := fun z => (f z - f c) / (f z - starRingEnd ℂ (f c))
  have hden (z : ℂ) (hz : z ∈ ball c R) : f z - starRingEnd ℂ (f c) ≠ 0 := by
    intro he
    have h := congrArg Complex.im (sub_eq_zero.mp he)
    simp only [conj_im] at h
    linarith [him z hz]
  have hcenter : c ∈ ball c R := mem_ball_self hR
  have hg0 : g c = 0 := by simp only [g, sub_self, zero_div]
  have hg : DifferentiableOn ℂ g (ball c R) := by
    intro z hz
    exact ((hf z hz).sub_const (f c)).div
      ((hf z hz).sub_const (starRingEnd ℂ (f c))) (hden z hz)
  have hmaps : MapsTo g (ball c R) (closedBall (g c) 1) := by
    intro z hz
    rw [mem_closedBall, hg0, dist_zero_right]
    change ‖(f z - f c) / (f z - starRingEnd ℂ (f c))‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hden z hz))]
    have hs : ‖f z - f c‖ ^ 2 ≤ ‖f z - starRingEnd ℂ (f c)‖ ^ 2 := by
      simp only [Complex.sq_norm, normSq_apply, sub_re, sub_im, conj_re, conj_im]
      nlinarith [mul_nonneg_of_nonpos_of_nonpos (him z hz) hc.le]
    nlinarith [norm_nonneg (f z - f c), norm_nonneg (f z - starRingEnd ℂ (f c))]
  have hschwarz := Complex.norm_deriv_le_div_of_mapsTo_ball hg hmaps hR
  have hfc : DifferentiableAt ℂ f c := hf.differentiableAt (isOpen_ball.mem_nhds hcenter)
  have hd : deriv g c = deriv f c / (f c - starRingEnd ℂ (f c)) := by
    have h := ((hfc.hasDerivAt.sub_const (f c)).div
      (hfc.hasDerivAt.sub_const (starRingEnd ℂ (f c))) (hden c hcenter)).deriv
    change deriv g c = _ at h
    rw [h]
    simp only [sub_self, zero_mul, sub_zero]
    field_simp
  have hnorm : ‖f c - starRingEnd ℂ (f c)‖ = 2 * (-(f c).im) := by
    have he : f c - starRingEnd ℂ (f c) = ((2 * (f c).im : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp
      · simp
        ring
    rw [he, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith)]
    ring
  rw [hd, norm_div, hnorm] at hschwarz
  have hbound := (div_le_iff₀ (by linarith : 0 < 2 * (-(f c).im))).mp hschwarz
  exact hbound.trans_eq (by ring)

/-- The sharp central disk derivative bound for an analytic function in
the closed lower half-plane. Its actual negative imaginary part controls
the derivative; a vanishing central mass forces a vanishing derivative. -/
theorem norm_deriv_le_of_im_nonpos_on_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (him : ∀ z ∈ ball c R, (f z).im ≤ 0) :
    ‖deriv f c‖ ≤ 2 * (-(f c).im) / R := by
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  let e : ℝ := epsilon * R / 2
  have he : 0 < e := by dsimp [e]; positivity
  let g : ℂ → ℂ := fun z => f z - I * (e : ℂ)
  have hg : DifferentiableOn ℂ g (ball c R) := hf.sub_const _
  have hgim (z : ℂ) (hz : z ∈ ball c R) : (g z).im ≤ 0 := by
    dsimp only [g]
    simp only [sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add]
    linarith [him z hz]
  have hgc : (g c).im < 0 := by
    dsimp only [g]
    simp only [sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add]
    linarith [him c (mem_ball_self hR)]
  have hb := norm_deriv_le_of_im_nonpos_strict_center hR hg hgim hgc
  have hfc := hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hR))
  have hd : deriv g c = deriv f c := (hfc.hasDerivAt.sub_const (I * (e : ℂ))).deriv
  rw [hd] at hb
  calc
    ‖deriv f c‖ ≤ 2 * (-(g c).im) / R := hb
    _ = 2 * (-(f c).im) / R + epsilon := by
      simp only [g, sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add]
      dsimp only [e]
      field_simp
      ring

end
end RiemannGaussian
