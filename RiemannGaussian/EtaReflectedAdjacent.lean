/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.EtaUniformTailBound
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Reflected adjacent eta multipliers at every positive cutoff

The neighboring ratio has modulus strictly below one throughout the open
right half-plane. Consequently its inverse denominator is nonzero even
before the safe tail range. Reflection couples the two ratios by an exact
positive real product. The mixed inverse retains this relation rather than
replacing the two channels by separate absolute bounds.
-/

namespace RiemannGaussian
noncomputable section
open Complex Set
open scoped Classical ComplexConjugate

/-- The logarithmic step is strictly positive at every positive argument. -/
theorem pairedEtaStepLog_pos {x : ℝ} (hx : 0 < x) : 0 < pairedEtaStepLog x := by
  apply Real.log_pos
  exact (lt_div_iff₀ hx).mpr (by linarith)

/-- The full ratio has its exact positive radial amplitude. -/
theorem norm_pairedEtaAdjacentRatio (s : ℂ) (x : ℝ) :
    ‖pairedEtaAdjacentRatio s x‖ = Real.exp (-s.re * pairedEtaStepLog x) := by
  rw [pairedEtaAdjacentRatio, Complex.norm_exp]
  simp

/-- In the open right half-plane, no adjacent ratio reaches the unit circle. -/
theorem norm_pairedEtaAdjacentRatio_lt_one {s : ℂ} (hs : 0 < s.re)
    {x : ℝ} (hx : 0 < x) : ‖pairedEtaAdjacentRatio s x‖ < 1 := by
  rw [norm_pairedEtaAdjacentRatio, Real.exp_lt_one_iff]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos hs) (pairedEtaStepLog_pos hx)

/-- The inverse denominator is nonzero without a cutoff-to-height restriction. -/
theorem one_add_pairedEtaAdjacentRatio_ne_zero {s : ℂ} (hs : 0 < s.re)
    {x : ℝ} (hx : 0 < x) : 1 + pairedEtaAdjacentRatio s x ≠ 0 := by
  intro h
  have he : pairedEtaAdjacentRatio s x = -1 := by linear_combination h
  have hn := norm_pairedEtaAdjacentRatio_lt_one hs hx
  simp only [he, norm_neg, norm_one, lt_self_iff_false] at hn

/-- Exact adjacent splitting holds on the whole open right half-plane. -/
theorem pairedEtaAdjacentInverse_mul_add_of_re_pos {s : ℂ} (hs : 0 < s.re)
    {x : ℝ} (hx : 0 < x) :
    pairedEtaAdjacentInverse s x *
        ((x : ℂ) ^ (-s) + ((x + 1 : ℝ) : ℂ) ^ (-s)) = (x : ℂ) ^ (-s) := by
  rw [cpow_add_one_eq_pairedEtaAdjacentRatio_mul s hx]
  unfold pairedEtaAdjacentInverse
  rw [show (x : ℂ) ^ (-s) + pairedEtaAdjacentRatio s x * (x : ℂ) ^ (-s) =
    (1 + pairedEtaAdjacentRatio s x) * (x : ℂ) ^ (-s) by ring,
    ← mul_assoc, inv_mul_cancel₀ (one_add_pairedEtaAdjacentRatio_ne_zero hs hx), one_mul]

/-- The signed boundary and variation identity extends through the entire
finite prefix, including large adjacent phase rotations. -/
theorem cpow_pair_eq_adjacent_boundary_add_defect_of_re_pos {s : ℂ} (hs : 0 < s.re)
    {x : ℝ} (hx : 0 < x) :
    (x : ℂ) ^ (-s) - ((x + 1 : ℝ) : ℂ) ^ (-s) =
      pairedEtaAdjacentBoundary s x - pairedEtaAdjacentBoundary s (x + 2) +
        pairedEtaAdjacentDefect s x := by
  have h1 := pairedEtaAdjacentInverse_mul_add_of_re_pos hs hx
  have h2 := pairedEtaAdjacentInverse_mul_add_of_re_pos hs
    (show 0 < x + 1 by linarith)
  rw [show x + 1 + 1 = x + 2 by ring] at h2
  unfold pairedEtaAdjacentBoundary pairedEtaAdjacentDefect
  linear_combination -h1 + h2

/-- The actual reflected mixed inverse, with both channel phases still
represented by their original adjacent eta ratios. -/
def pairedEtaReflectedAdjacentProduct (s : ℂ) (x : ℝ) : ℂ :=
  pairedEtaAdjacentInverse s x * conj (pairedEtaAdjacentInverse (1 - conj s) x)

/-- Reflection cancels the oscillation in the mixed ratio exactly. -/
theorem pairedEtaAdjacentRatio_mul_conj_reflected (s : ℂ) (x : ℝ) :
    pairedEtaAdjacentRatio s x * conj (pairedEtaAdjacentRatio (1 - conj s) x) =
      (Real.exp (-pairedEtaStepLog x) : ℂ) := by
  unfold pairedEtaAdjacentRatio
  rw [← Complex.exp_conj, ← Complex.exp_add, Complex.ofReal_exp]
  congr 1
  simp only [map_mul, map_neg, map_sub, map_one, conj_conj, conj_ofReal]
  push_cast
  ring

/-- The sum of the two oriented inverse channels is their positive radial
factor times the full mixed inverse. -/
theorem pairedEtaAdjacentInverse_reflected_sum {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    pairedEtaAdjacentInverse s x + conj (pairedEtaAdjacentInverse (1 - conj s) x) - 1 =
      (1 - (Real.exp (-pairedEtaStepLog x) : ℂ)) * pairedEtaReflectedAdjacentProduct s x := by
  have hp : 0 < (1 - conj s).re := by simp; linarith
  have h0 := one_add_pairedEtaAdjacentRatio_ne_zero hs hx
  have h1 := one_add_pairedEtaAdjacentRatio_ne_zero hp hx
  have h1' : 1 + conj (pairedEtaAdjacentRatio (1 - conj s) x) ≠ 0 := by
    simpa only [map_add, map_one] using (map_ne_zero (starRingEnd ℂ)).mpr h1
  rw [← pairedEtaAdjacentRatio_mul_conj_reflected s x]
  unfold pairedEtaReflectedAdjacentProduct pairedEtaAdjacentInverse
  simp only [map_inv₀, map_add, map_one]
  field_simp
  ring

private theorem sinh_mul_le {a t : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (ht : 0 ≤ t) :
    Real.sinh (a * t) ≤ a * Real.sinh t := by
  have hc : ConvexOn ℝ (Ici 0) Real.sinh := by
    apply MonotoneOn.convexOn_of_deriv (convex_Ici 0) Real.continuous_sinh.continuousOn
      Real.differentiable_sinh.differentiableOn
    rw [Real.deriv_sinh]
    exact Real.cosh_strictMonoOn.monotoneOn.mono interior_subset
  have h := hc.2 (show (0 : ℝ) ∈ Ici 0 by simp) ht
    (show 0 ≤ 1 - a by linarith) ha (show 1 - a + a = 1 by ring)
  simpa using h

/-- Complementary radial damping has contrast at most its horizontal
asymmetry times the total damping. This holds at every logarithmic step. -/
theorem eta_complementary_exp_contrast_le {σ t : ℝ} (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 0 ≤ t) :
    |Real.exp (-(1 - σ) * t) - Real.exp (-σ * t)| ≤
      |2 * σ - 1| * (1 - Real.exp (-t)) := by
  have hk : |2 * σ - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hh : |Real.sinh ((2 * σ - 1) * (t / 2))| ≤
      |2 * σ - 1| * Real.sinh (t / 2) := by
    rw [Real.abs_sinh, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t / 2)]
    exact sinh_mul_le (abs_nonneg _) hk (by positivity)
  have hex : 2 * Real.exp (-t / 2) * Real.sinh ((2 * σ - 1) * (t / 2)) =
      Real.exp (-(1 - σ) * t) - Real.exp (-σ * t) := by
    rw [Real.sinh_eq]
    rw [show 2 * Real.exp (-t / 2) *
        ((Real.exp ((2 * σ - 1) * (t / 2)) - Real.exp (-((2 * σ - 1) * (t / 2)))) / 2) =
      Real.exp (-t / 2) * Real.exp ((2 * σ - 1) * (t / 2)) -
        Real.exp (-t / 2) * Real.exp (-((2 * σ - 1) * (t / 2))) by ring,
      ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  have hbase : 2 * Real.exp (-t / 2) * Real.sinh (t / 2) = 1 - Real.exp (-t) := by
    rw [Real.sinh_eq]
    rw [show 2 * Real.exp (-t / 2) * ((Real.exp (t / 2) - Real.exp (-(t / 2))) / 2) =
      Real.exp (-t / 2) * Real.exp (t / 2) - Real.exp (-t / 2) * Real.exp (-(t / 2)) by ring,
      ← Real.exp_add, ← Real.exp_add]
    rw [show -t / 2 + t / 2 = 0 by ring, show -t / 2 + -(t / 2) = -t by ring, Real.exp_zero]
  calc
    _ = (2 * Real.exp (-t / 2)) * |Real.sinh ((2 * σ - 1) * (t / 2))| := by
      rw [← hex, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.exp (-t / 2))]
    _ ≤ (2 * Real.exp (-t / 2)) * (|2 * σ - 1| * Real.sinh (t / 2)) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by rw [← hbase]; ring

private theorem inverse_re_sector {z : ℂ} {a : ℝ}
    (h : a * normSq z ≤ z.re ^ 2) : a * normSq z⁻¹ ≤ z⁻¹.re ^ 2 := by
  by_cases hz : z = 0
  · simp [hz]
  have hn := normSq_pos.mpr hz
  rw [normSq_inv, inv_re, div_pow]
  calc
    _ = (a * normSq z) / normSq z ^ 2 := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_right h (sq_nonneg _)

private theorem shared_phase_sector {r u c d a : ℝ} {z : ℂ}
    (hr : 0 ≤ r) (hr1 : r < 1) (hu : 0 ≤ u) (hu1 : u < 1)
    (hc : -1 ≤ c) (hcd : c ^ 2 + d ^ 2 = 1)
    (hzr : z.re = 1 + r * u + (r + u) * c) (hzi : z.im = (u - r) * d)
    (ha : (u - r) ^ 2 ≤ (1 - a) * (1 - r * u) ^ 2) :
    0 < z.re ∧ a * normSq z ≤ z.re ^ 2 := by
  have hru : r * u < 1 := (mul_le_mul_of_nonneg_left hu1.le hr).trans_lt (by simpa using hr1)
  have hA : 0 < 1 - r * u := sub_pos.mpr hru
  have hreal : 0 < z.re := by
    rw [hzr]
    have hh := mul_nonneg (show 0 ≤ r + u by positivity) (show 0 ≤ c + 1 by linarith)
    nlinarith [mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hu1)]
  refine ⟨hreal, ?_⟩
  have he : (1 - r * u) ^ 2 * z.im ^ 2 +
      ((u - r) * ((1 + r * u) * c + (r + u))) ^ 2 = (u - r) ^ 2 * normSq z := by
    rw [normSq_apply, hzr, hzi]
    linear_combination ((u - r) ^ 2 * ((1 + r * u) ^ 2 - (r + u) ^ 2)) * hcd
  have hmul := mul_le_mul_of_nonneg_right ha (normSq_nonneg z)
  have hsmall : (1 - r * u) ^ 2 * z.im ^ 2 ≤
      (1 - r * u) ^ 2 * ((1 - a) * normSq z) := by
    nlinarith only [he, hmul, sq_nonneg ((u - r) * ((1 + r * u) * c + (r + u)))]
  have hi := (mul_le_mul_iff_right₀ (sq_pos_of_pos hA)).mp hsmall
  rw [normSq_apply] at hi ⊢
  nlinarith only [hi]

private theorem adjacent_ratio_parts (s : ℂ) (x : ℝ) :
    (pairedEtaAdjacentRatio s x).re = Real.exp (-s.re * pairedEtaStepLog x) *
        Real.cos (s.im * pairedEtaStepLog x) ∧
      (pairedEtaAdjacentRatio s x).im = -Real.exp (-s.re * pairedEtaStepLog x) *
        Real.sin (s.im * pairedEtaStepLog x) := by
  simp [pairedEtaAdjacentRatio, Complex.exp_re, Complex.exp_im]

private theorem reflected_denominator_sector {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    let D := (1 + pairedEtaAdjacentRatio s x) *
      (1 + conj (pairedEtaAdjacentRatio (1 - conj s) x))
    0 < D.re ∧ 4 * s.re * (1 - s.re) * normSq D ≤ D.re ^ 2 := by
  let δ := pairedEtaStepLog x
  let r := Real.exp (-s.re * δ)
  let u := Real.exp (-(1 - s.re) * δ)
  have hδ : 0 < δ := pairedEtaStepLog_pos hx
  have hr : 0 < r := Real.exp_pos _
  have hu : 0 < u := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hu1 : u < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hru : r * u = Real.exp (-δ) := by
    dsimp [r, u]
    rw [← Real.exp_add]
    congr 1
    ring
  have he := pairedEtaAdjacentRatio_mul_conj_reflected s x
  have hp := adjacent_ratio_parts s x
  have hq := adjacent_ratio_parts (1 - conj s) x
  simp only [sub_re, one_re, conj_re, sub_im, one_im, conj_im, zero_sub, neg_neg] at hq
  have hproduct : (1 + pairedEtaAdjacentRatio s x) *
      (1 + conj (pairedEtaAdjacentRatio (1 - conj s) x)) =
      1 + pairedEtaAdjacentRatio s x + conj (pairedEtaAdjacentRatio (1 - conj s) x) +
        (Real.exp (-δ) : ℂ) := by
    rw [← he]
    ring
  have hcontrast := eta_complementary_exp_contrast_le hs.le hs1.le hδ.le
  change |u - r| ≤ |2 * s.re - 1| * (1 - Real.exp (-δ)) at hcontrast
  have hsq := sq_le_sq₀ (abs_nonneg (u - r))
    (show 0 ≤ |2 * s.re - 1| * (1 - Real.exp (-δ)) from
      mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))))
  have hcontrast2 := hsq.mpr hcontrast
  rw [sq_abs, mul_pow, sq_abs, ← hru] at hcontrast2
  apply shared_phase_sector (d := Real.sin (s.im * δ)) hr.le hr1 hu.le hu1
    (Real.neg_one_le_cos (s.im * δ))
    (by nlinarith [Real.sin_sq_add_cos_sq (s.im * δ)])
  · rw [hproduct]
    simp only [add_re, one_re, conj_re, ofReal_re, hp.1, hq.1]
    change 1 + r * Real.cos (s.im * δ) + u * Real.cos (s.im * δ) + Real.exp (-δ) = _
    rw [← hru]
    ring
  · rw [hproduct]
    simp only [add_im, one_im, conj_im, ofReal_im, hp.2, hq.2]
    change 0 + -r * Real.sin (s.im * δ) - -u * Real.sin (s.im * δ) + 0 = _
    ring
  · nlinarith only [hcontrast2]

/-- The reflected mixed adjacent inverse has positive real part even
where the individual phase steps approach an odd multiple of pi. -/
theorem re_pairedEtaReflectedAdjacentProduct_pos {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    0 < (pairedEtaReflectedAdjacentProduct s x).re := by
  have h := (reflected_denominator_sector hs hs1 hx).1
  unfold pairedEtaReflectedAdjacentProduct pairedEtaAdjacentInverse
  rw [map_inv₀, map_add, map_one, ← mul_inv, inv_re]
  apply div_pos h
  exact normSq_pos.mpr (fun hz => by rw [hz, zero_re] at h; exact lt_irrefl _ h)

/-- At every cutoff and ordinate the reflected mixed eta inverse lies
in a sector determined only by the horizontal coordinate. -/
theorem pairedEtaReflectedAdjacentProduct_sector {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    4 * s.re * (1 - s.re) * normSq (pairedEtaReflectedAdjacentProduct s x) ≤
      (pairedEtaReflectedAdjacentProduct s x).re ^ 2 := by
  have h := inverse_re_sector (reflected_denominator_sector hs hs1 hx).2
  simpa only [pairedEtaReflectedAdjacentProduct, pairedEtaAdjacentInverse,
    map_inv₀, map_add, map_one, mul_inv] using h

/-- The complete magnitude is bounded by the retained positive real
channel, with a constant independent of height and physical cutoff. -/
theorem pairedEtaReflectedAdjacentProduct_norm_le_re {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    2 * Real.sqrt (s.re * (1 - s.re)) * ‖pairedEtaReflectedAdjacentProduct s x‖ ≤
      (pairedEtaReflectedAdjacentProduct s x).re := by
  have hp : 0 ≤ s.re * (1 - s.re) := mul_nonneg hs.le (sub_nonneg.mpr hs1.le)
  apply (sq_le_sq₀ (by positivity) (re_pairedEtaReflectedAdjacentProduct_pos hs hs1 hx).le).mp
  calc
    _ = 4 * s.re * (1 - s.re) * normSq (pairedEtaReflectedAdjacentProduct s x) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hp, Complex.sq_norm]
      ring
    _ ≤ _ := pairedEtaReflectedAdjacentProduct_sector hs hs1 hx

/-- The signed odd channel is controlled by the horizontal asymmetry.
It vanishes on the critical line, without any height restriction. -/
theorem pairedEtaReflectedAdjacentProduct_im_sq_le {s : ℂ} (hs : 0 < s.re)
    (hs1 : s.re < 1) {x : ℝ} (hx : 0 < x) :
    4 * s.re * (1 - s.re) * (pairedEtaReflectedAdjacentProduct s x).im ^ 2 ≤
      (2 * s.re - 1) ^ 2 * (pairedEtaReflectedAdjacentProduct s x).re ^ 2 := by
  have h := pairedEtaReflectedAdjacentProduct_sector hs hs1 hx
  rw [normSq_apply] at h
  nlinarith only [h]

end
end RiemannGaussian
