/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaGlobalSignedBudget
import RiemannGaussian.TrigammaHalfPlane
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Signed horizontal variation of the actual zeta completion

The reciprocal at zero cancels exactly with one digamma recurrence.
The remaining shifted trigamma has positive real part and uniformly
bounded complex norm. Thus the regular completion increases horizontally
and its differences have no logarithmic height cost. The full complex
correction is kept before either conclusion is used.
-/

namespace RiemannGaussian
noncomputable section
open Complex Set
open scoped Topology

/-- One actual Gamma recurrence absorbs the reciprocal at zero into
the regular completion. This identity retains its full complex phase. -/
theorem zetaGlobalRegularCorrection_eq_shifted {s : ℂ} (hs : 0 < s.re) :
    zetaGlobalRegularCorrection s =
      Complex.digamma (s / 2 + 1) / 2 - Complex.log Real.pi / 2 := by
  have hrec := Complex.digamma_apply_add_one (s / 2) (fun n => by
    apply ne_of_apply_ne Complex.re
    simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) n])
  rw [hrec, zetaGlobalRegularCorrection]
  field_simp
  ring

/-- The complete regular correction has the shifted trigamma derivative
on the positive half-plane, with the exact chain-rule factor. -/
theorem hasDerivAt_zetaGlobalRegularCorrection {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt zetaGlobalRegularCorrection
      (deriv Complex.digamma (s / 2 + 1) / 4) s := by
  have hz : 0 < (s / 2 + 1).re := by simp; linarith
  have hd := (((hasDerivAt_digamma_euler hz).comp s
    (((hasDerivAt_id s).div_const 2).add_const 1)).div_const 2).sub_const
      (Complex.log Real.pi / 2)
  rw [← deriv_digamma_eq_tsum hz] at hd
  have hd' : HasDerivAt
      (fun w : ℂ => Complex.digamma (w / 2 + 1) / 2 - Complex.log Real.pi / 2)
      (deriv Complex.digamma (s / 2 + 1) / 4) s := by
    convert! hd using 1
    ring
  apply hd'.congr_of_eventuallyEq
  filter_upwards [(Complex.isOpen_re_gt 0).mem_nhds hs] with w hw
  exact zetaGlobalRegularCorrection_eq_shifted hw

/-- The literal completion has strictly positive real horizontal
derivative throughout the positive half-plane. -/
theorem re_deriv_zetaGlobalRegularCorrection_pos {s : ℂ} (hs : 0 < s.re) :
    0 < (deriv zetaGlobalRegularCorrection s).re := by
  rw [(hasDerivAt_zetaGlobalRegularCorrection hs).deriv, Complex.div_ofNat_re]
  exact div_pos (trigamma_re_pos (by simp; linarith)) (by norm_num)

/-- A height-independent complex derivative bound for the actual
regular correction. The midpoint remainder is bounded after its leading
complex reciprocal has been retained. -/
theorem norm_deriv_zetaGlobalRegularCorrection_le {s : ℂ} (hs : 0 < s.re) :
    ‖deriv zetaGlobalRegularCorrection s‖ ≤ 1 := by
  let z := s / 2 + 1
  have hz1 : 1 < z.re := by dsimp [z]; simp; linarith
  have hz : 1 / 2 < z.re := by linarith
  have hm : (1 / 2 : ℝ) ≤ ‖z - 1 / 2‖ := by
    have h := Complex.re_le_norm (z - 1 / 2)
    simp only [sub_re, div_ofNat_re, one_re] at h
    linarith
  have hN : 1 ≤ normSq z := by
    rw [normSq_apply]
    nlinarith [sq_nonneg z.im, sq_nonneg (z.re - 1)]
  have hden : 2 ≤ 4 * normSq z * (z.re - 1 / 2) := by
    nlinarith [mul_nonneg (show 0 ≤ normSq z - 1 by linarith)
      (show 0 ≤ z.re - 1 by linarith)]
  have he := (norm_trigamma_sub_midpoint_le hz).trans
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden)
  have hi : ‖(z - 1 / 2)⁻¹‖ ≤ 2 := by
    rw [norm_inv, ← one_div]
    exact (one_div_le_one_div_of_le (by norm_num) hm).trans_eq (by norm_num)
  have hn := norm_add_le (deriv Complex.digamma z - (z - 1 / 2)⁻¹) (z - 1 / 2)⁻¹
  rw [sub_add_cancel] at hn
  have hb : ‖deriv Complex.digamma z‖ ≤ 4 := by linarith
  rw [(hasDerivAt_zetaGlobalRegularCorrection hs).deriv, norm_div]
  norm_num only [Complex.norm_ofNat]
  exact (div_le_div_of_nonneg_right hb (by norm_num)).trans_eq (by norm_num)

/-- Differences of the complete complex correction are uniformly
Lipschitz on the positive half-plane. No height moment is needed to sum
horizontal differences against absolutely summable coefficients. -/
theorem norm_zetaGlobalRegularCorrection_sub_le {s w : ℂ}
    (hs : 0 < s.re) (hw : 0 < w.re) :
    ‖zetaGlobalRegularCorrection w - zetaGlobalRegularCorrection s‖ ≤ ‖w - s‖ := by
  simpa using (convex_halfSpace_re_gt 0).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hasDerivAt_zetaGlobalRegularCorrection hz).differentiableAt)
    (fun z hz => norm_deriv_zetaGlobalRegularCorrection_le hz) hs hw

private theorem horizontal_derivative (y : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    HasDerivAt (fun u : ℝ => (zetaGlobalRegularCorrection ((u : ℂ) + I * y)).re)
      (deriv zetaGlobalRegularCorrection ((σ : ℂ) + I * y)).re σ := by
  have hh := hasDerivAt_zetaGlobalRegularCorrection (s := (σ : ℂ) + I * y)
    (by simpa using hσ)
  have hd := hh.comp (σ : ℂ) ((hasDerivAt_id (σ : ℂ)).add_const (I * y))
  rw [hh.deriv]
  simpa only [mul_one, Function.comp_apply, id_eq] using hd.real_of_complex

/-- At every fixed ordinate, the real regular completion is strictly
increasing with the abscissa on the whole positive half-plane. -/
theorem strictMonoOn_re_zetaGlobalRegularCorrection (y : ℝ) :
    StrictMonoOn (fun σ : ℝ => (zetaGlobalRegularCorrection ((σ : ℂ) + I * y)).re)
      (Ioi 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro σ hσ
    exact (horizontal_derivative y hσ).continuousAt.continuousWithinAt
  · intro σ hσ
    rw [interior_Ioi] at hσ
    rw [(horizontal_derivative y hσ).deriv]
    exact re_deriv_zetaGlobalRegularCorrection_pos (by simpa using hσ)

/-- In the subtraction from a smaller to a larger safe abscissa, the
entire regular completion has a favorable sign, at every ordinate. -/
theorem re_zetaGlobalRegularCorrection_sub_nonpos {σ τ : ℝ}
    (hσ : 0 < σ) (hστ : σ ≤ τ) (y : ℝ) :
    (zetaGlobalRegularCorrection ((σ : ℂ) + I * y) -
      zetaGlobalRegularCorrection ((τ : ℂ) + I * y)).re ≤ 0 := by
  rw [Complex.sub_re]
  exact sub_nonpos.mpr ((strictMonoOn_re_zetaGlobalRegularCorrection y).monotoneOn
    hσ (hσ.trans_le hστ) hστ)

end
end RiemannGaussian
