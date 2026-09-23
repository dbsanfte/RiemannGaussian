/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Quantitative isolation from a contracting complex Newton map

A nonzero approximate slope and a uniform derivative error give a proved
contraction on a closed disc. The center residual pays the self-map
condition. The result asserts an actual unique zero and a nonzero derivative,
so it can be used for numerical zero isolation without assuming a zero list.
-/

namespace RiemannGaussian.AnalyticNewtonIsolation
noncomputable section
open Complex Metric Set

/-- A second-derivative bound gives a linear bound for derivative variation. -/
theorem derivative_variation {f : ℂ → ℂ} {c z : ℂ} {r E : ℝ}
    (hr : 0 ≤ r) (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hE : ∀ w ∈ closedBall c r, ‖deriv (deriv f) w‖ ≤ E)
    (hz : z ∈ closedBall c r) :
    ‖deriv f z - deriv f c‖ ≤ E * ‖z - c‖ := by
  exact (convex_closedBall c r).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hf.deriv w hw).differentiableAt) hE
    (mem_closedBall_self hr) hz

/-- The same bound controls the complete error of the affine approximation.
The deliberately coarse constant avoids any unproved Taylor remainder. -/
theorem affine_error {f : ℂ → ℂ} {c z : ℂ} {r E : ℝ}
    (hr : 0 ≤ r) (hE0 : 0 ≤ E) (hf : AnalyticOnNhd ℂ f (closedBall c r))
    (hE : ∀ w ∈ closedBall c r, ‖deriv (deriv f) w‖ ≤ E)
    (hz : z ∈ closedBall c r) :
    ‖f z - f c - deriv f c * (z - c)‖ ≤ E * r * ‖z - c‖ := by
  let g : ℂ → ℂ := fun w => f w - f c - deriv f c * (w - c)
  have hg (w : ℂ) (hw : w ∈ closedBall c r) :
      HasDerivAt g (deriv f w - deriv f c) w := by
    apply HasDerivAt.sub
    · exact (hf w hw).differentiableAt.hasDerivAt.sub_const (f c)
    · simpa only [mul_one, id_eq] using
        (((hasDerivAt_id w).sub_const c).const_mul (deriv f c))
  have hb (w : ℂ) (hw : w ∈ closedBall c r) :
      ‖deriv f w - deriv f c‖ ≤ E * r :=
    (derivative_variation hr hf hE hw).trans
      (mul_le_mul_of_nonneg_left (mem_closedBall_iff_norm.mp hw) hE0)
  have hh := (convex_closedBall c r).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w hw => (hg w hw).hasDerivWithinAt) hb (mem_closedBall_self hr) hz
  simpa [g] using hh

/-- Two genuine function values and a second-derivative bound enclose the
actual derivative at the center; no numerical derivative is assumed. -/
theorem derivative_from_two_values {f : ℂ → ℂ} {c a : ℂ} {h E : ℝ}
    (hh : 0 < h) (hE0 : 0 ≤ E)
    (hf : AnalyticOnNhd ℂ f (closedBall c h))
    (hE : ∀ w ∈ closedBall c h, ‖deriv (deriv f) w‖ ≤ E) :
    ‖deriv f c - a‖ ≤
      (‖f (c + (h : ℂ)) - a * (h : ℂ)‖ + ‖f c‖) / h + E * h := by
  have hnorm : ‖(h : ℂ)‖ = h := by simp [abs_of_pos hh]
  have hz : c + (h : ℂ) ∈ closedBall c h := by
    simpa only [mem_closedBall_iff_norm, add_sub_cancel_left, hnorm] using le_refl h
  have herr := affine_error hh.le hE0 hf hE hz
  simp only [add_sub_cancel_left, hnorm] at herr
  have he : (deriv f c - a) * (h : ℂ) =
      (f (c + (h : ℂ)) - a * (h : ℂ)) - f c -
        (f (c + (h : ℂ)) - f c - deriv f c * (h : ℂ)) := by ring
  have hb : ‖deriv f c - a‖ * h ≤
      ‖f (c + (h : ℂ)) - a * (h : ℂ)‖ + ‖f c‖ + E * h * h := by
    calc
      _ = ‖(deriv f c - a) * (h : ℂ)‖ := by rw [norm_mul, hnorm]
      _ = ‖(f (c + (h : ℂ)) - a * (h : ℂ)) - f c -
          (f (c + (h : ℂ)) - f c - deriv f c * (h : ℂ))‖ := congrArg norm he
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) herr)
  have hcancel := div_mul_cancel₀
    (‖f (c + (h : ℂ)) - a * (h : ℂ)‖ + ‖f c‖) hh.ne'
  nlinarith

/-- A genuine Banach contraction certificate supplies one unique simple zero
in the entire closed disc. No root-existence assumption is present. -/
theorem exists_unique_zero {f : ℂ → ℂ} {c a : ℂ} {r : ℝ} {q : NNReal}
    (hr : 0 ≤ r) (ha : a ≠ 0) (hq : q < 1)
    (hf : ∀ z ∈ closedBall c r, DifferentiableAt ℂ f z)
    (hd : ∀ z ∈ closedBall c r, ‖deriv f z - a‖ ≤ (q : ℝ) * ‖a‖)
    (hc : ‖f c‖ ≤ (1 - (q : ℝ)) * r * ‖a‖) :
    ∃ z ∈ closedBall c r, f z = 0 ∧ deriv f z ≠ 0 ∧
      ∀ w ∈ closedBall c r, f w = 0 → w = z := by
  let g : ℂ → ℂ := fun z => z - f z / a
  have han : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hg (z : ℂ) (hz : z ∈ closedBall c r) :
      HasDerivAt g (1 - deriv f z / a) z :=
    (hasDerivAt_id z).sub ((hf z hz).hasDerivAt.div_const a)
  have hg_bound (z : ℂ) (hz : z ∈ closedBall c r) :
      ‖1 - deriv f z / a‖ ≤ (q : ℝ) := by
    have he : 1 - deriv f z / a = -(deriv f z - a) / a := by field_simp; ring
    rw [he, norm_div, norm_neg]
    exact (div_le_iff₀ han).mpr (hd z hz)
  have hdist {z w : ℂ} (hz : z ∈ closedBall c r) (hw : w ∈ closedBall c r) :
      ‖g w - g z‖ ≤ (q : ℝ) * ‖w - z‖ :=
    (convex_closedBall c r).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun x hx => (hg x hx).hasDerivWithinAt) hg_bound hz hw
  have hcenter : ‖g c - c‖ ≤ (1 - (q : ℝ)) * r := by
    simpa only [g, sub_sub_cancel_left, norm_neg, norm_div] using
      (div_le_iff₀ han).mpr hc
  have hmaps : MapsTo g (closedBall c r) (closedBall c r) := by
    intro z hz
    apply mem_closedBall_iff_norm.mpr
    calc
      ‖g z - c‖ ≤ ‖g z - g c‖ + ‖g c - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (q : ℝ) * ‖z - c‖ + (1 - (q : ℝ)) * r :=
        add_le_add (hdist (mem_closedBall_self hr) hz) hcenter
      _ ≤ (q : ℝ) * r + (1 - (q : ℝ)) * r := by
        gcongr
        exact mem_closedBall_iff_norm.mp hz
      _ = r := by ring
  have hcontract : ContractingWith q (hmaps.restrict g (closedBall c r) (closedBall c r)) := by
    refine ⟨hq, LipschitzWith.of_dist_le_mul ?_⟩
    intro z w
    change dist (g z) (g w) ≤ (q : ℝ) * dist (z : ℂ) w
    simpa only [dist_eq_norm] using hdist w.2 z.2
  obtain ⟨z, hz, hfix, _, _⟩ := ContractingWith.exists_fixedPoint'
    isClosed_closedBall.isComplete hmaps hcontract (mem_closedBall_self hr)
    (edist_ne_top _ _)
  have hzero : f z = 0 := by
    have he : z - f z / a = z := hfix
    have he' : f z / a = 0 := by linear_combination -he
    exact (div_eq_zero_iff).mp he' |>.resolve_right ha
  have hsimple : deriv f z ≠ 0 := by
    intro he
    have hh := hd z hz
    rw [he, zero_sub, norm_neg] at hh
    have hq' : (q : ℝ) < 1 := hq
    nlinarith
  refine ⟨z, hz, hzero, hsimple, ?_⟩
  intro w hw hwzero
  have hh := hdist hz hw
  simp only [g, hzero, hwzero, zero_div, sub_zero] at hh
  have hq' : (q : ℝ) < 1 := hq
  have hn := norm_nonneg (w - z)
  have he : ‖w - z‖ = 0 := by nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp he)

end
end RiemannGaussian.AnalyticNewtonIsolation
