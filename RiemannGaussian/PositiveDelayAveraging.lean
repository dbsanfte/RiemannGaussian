/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.AnalyticDoublePoleMoments
import Mathlib.MeasureTheory.Group.Integral

/-!
# Positive delay averages that cancel prescribed nonreal modes

For `p = delta + i*gamma`, a delay `h = pi/abs(gamma)` and positive weight
`w = exp(delta*h)` give the convex average `(f(t)+w*f(t-h))/(1+w)`.
Its Laplace multiplier vanishes at `p` and its conjugate. Finite iteration
therefore removes any prescribed finite nonreal spectrum, while retaining
the original time signal and transporting pointwise lower bounds exactly.

The construction does not select numerical coefficients. It is available
for every finite list of complex nodes; nonrealness is required only for
the cancellation conclusion. Constants are preserved by normalization.
-/

namespace RiemannGaussian
noncomputable section
open Complex Filter MeasureTheory Set
open scoped Topology

/-- A half-period delay of the prescribed imaginary frequency. -/
def nonrealModeDelay (p : ℂ) : ℝ := Real.pi / |p.im|

/-- The positive tilt that compensates the real exponential growth over
one half-period delay. -/
def nonrealModeDelayWeight (p : ℂ) : ℝ := Real.exp (p.re * nonrealModeDelay p)

/-- Every delay is nonnegative; at a real node the totalized value is zero. -/
theorem nonrealModeDelay_nonneg (p : ℂ) : 0 ≤ nonrealModeDelay p := by
  unfold nonrealModeDelay
  positivity

/-- Every prescribed nonreal mode has a strictly positive half-period. -/
theorem nonrealModeDelay_pos {p : ℂ} (hp : p.im ≠ 0) : 0 < nonrealModeDelay p :=
  div_pos Real.pi_pos (abs_pos.mpr hp)

/-- The tilt weight is strictly positive at every node. -/
theorem nonrealModeDelayWeight_pos (p : ℂ) : 0 < nonrealModeDelayWeight p := Real.exp_pos _

/-- The exact normalized Laplace multiplier of one positive delay average. -/
def nonrealModeDelayMultiplier (p z : ℂ) : ℂ :=
  (1 + (nonrealModeDelayWeight p : ℂ) * Complex.exp (-z * (nonrealModeDelay p : ℂ))) /
    (1 + (nonrealModeDelayWeight p : ℂ))

/-- One convex average of the current value and an earlier value. -/
def nonrealModeDelayAverage (p : ℂ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (f t + nonrealModeDelayWeight p * f (t - nonrealModeDelay p)) /
    (1 + nonrealModeDelayWeight p)

/-- Normalized positive delay averaging over an arbitrary finite node list. -/
def positiveDelayAverage : List ℂ → (ℝ → ℝ) → ℝ → ℝ
  | [], f, t => f t
  | p :: L, f, t => nonrealModeDelayAverage p (positiveDelayAverage L f) t

/-- The full complex multiplier, retaining every coupled delay factor. -/
def positiveDelayMultiplier : List ℂ → ℂ → ℂ
  | [], _ => 1
  | p :: L, z => nonrealModeDelayMultiplier p z * positiveDelayMultiplier L z

/-- The maximum backward displacement of a finite positive delay average. -/
def positiveDelaySpan (L : List ℂ) : ℝ := (L.map nonrealModeDelay).sum

/-- The complete averaging span is nonnegative. -/
theorem positiveDelaySpan_nonneg (L : List ℂ) : 0 ≤ positiveDelaySpan L := by
  induction L with
  | nil => simp [positiveDelaySpan]
  | cons p L ih => simpa [positiveDelaySpan] using add_nonneg (nonrealModeDelay_nonneg p) ih

private theorem weight_mul_exp_at_node {p : ℂ} (hp : p.im ≠ 0) :
    (nonrealModeDelayWeight p : ℂ) * Complex.exp (-p * (nonrealModeDelay p : ℂ)) = -1 := by
  rw [nonrealModeDelayWeight, Complex.ofReal_exp, ← Complex.exp_add]
  have he : ((p.re * nonrealModeDelay p : ℝ) : ℂ) - p * (nonrealModeDelay p : ℂ) =
      -((p.im * nonrealModeDelay p : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [show ((p.re * nonrealModeDelay p : ℝ) : ℂ) + -p * (nonrealModeDelay p : ℂ) =
    ((p.re * nonrealModeDelay p : ℝ) : ℂ) - p * (nonrealModeDelay p : ℂ) by ring, he]
  rcases lt_or_gt_of_ne hp with him | him
  · have hh : p.im * nonrealModeDelay p = -Real.pi := by
      rw [nonrealModeDelay, abs_of_neg him]
      field_simp
    rw [hh]
    simp
  · have hh : p.im * nonrealModeDelay p = Real.pi := by
      rw [nonrealModeDelay, abs_of_pos him]
      field_simp
    rw [hh]
    simpa only [neg_mul] using Complex.exp_neg_pi_mul_I

/-- The exact nonreal mode is cancelled by a positive two-delay average. -/
theorem nonrealModeDelayMultiplier_self {p : ℂ} (hp : p.im ≠ 0) :
    nonrealModeDelayMultiplier p p = 0 := by
  rw [nonrealModeDelayMultiplier, weight_mul_exp_at_node hp]
  simp

/-- Every one-delay multiplier is entire. -/
theorem analyticAt_nonrealModeDelayMultiplier (p z : ℂ) :
    AnalyticAt ℂ (nonrealModeDelayMultiplier p) z := by
  unfold nonrealModeDelayMultiplier
  fun_prop

/-- Every finite complete multiplier is entire. -/
theorem analyticAt_positiveDelayMultiplier (L : List ℂ) (z : ℂ) :
    AnalyticAt ℂ (positiveDelayMultiplier L) z := by
  induction L with
  | nil => exact analyticAt_const
  | cons p L ih => exact (analyticAt_nonrealModeDelayMultiplier p z).mul ih

/-- A finite average cancels every nonreal node in its list. -/
theorem positiveDelayMultiplier_eq_zero_of_mem {L : List ℂ} {p : ℂ}
    (hpL : p ∈ L) (hp : p.im ≠ 0) : positiveDelayMultiplier L p = 0 := by
  induction L with
  | nil => simp at hpL
  | cons q L ih =>
    rcases List.mem_cons.mp hpL with h | h
    · subst q
      simp [positiveDelayMultiplier, nonrealModeDelayMultiplier_self hp]
    · simp [positiveDelayMultiplier, ih h]

/-- Normalization preserves the constant mode exactly. -/
theorem positiveDelayMultiplier_zero (L : List ℂ) : positiveDelayMultiplier L 0 = 1 := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    have hp : (1 + (nonrealModeDelayWeight p : ℂ)) ≠ 0 := by
      exact_mod_cast (show 0 < 1 + nonrealModeDelayWeight p by
        linarith [nonrealModeDelayWeight_pos p]).ne'
    simp [positiveDelayMultiplier, nonrealModeDelayMultiplier, ih, hp]

/-- One convex delay average preserves a common lower bound at its two
input times. -/
theorem le_nonrealModeDelayAverage {p : ℂ} {f : ℝ → ℝ} {t B : ℝ}
    (ht : B ≤ f t) (hd : B ≤ f (t - nonrealModeDelay p)) :
    B ≤ nonrealModeDelayAverage p f t := by
  rw [nonrealModeDelayAverage, le_div_iff₀ (show 0 < 1 + nonrealModeDelayWeight p by
    linarith [nonrealModeDelayWeight_pos p])]
  nlinarith [mul_le_mul_of_nonneg_left hd (nonrealModeDelayWeight_pos p).le]

/-- A lower bound on the entire finite backward interval transports
unchanged through every positive delay average. -/
theorem le_positiveDelayAverage {L : List ℂ} {f : ℝ → ℝ} {t B : ℝ}
    (hf : ∀ u ∈ Icc (t - positiveDelaySpan L) t, B ≤ f u) :
    B ≤ positiveDelayAverage L f t := by
  induction L generalizing t with
  | nil => simpa [positiveDelayAverage, positiveDelaySpan] using hf t (by simp [positiveDelaySpan])
  | cons p L ih =>
    apply le_nonrealModeDelayAverage
    · apply ih
      intro u hu
      apply hf u
      simp only [positiveDelaySpan, List.map_cons, List.sum_cons] at *
      have hd := nonrealModeDelay_nonneg p
      exact ⟨by linarith [hu.1], hu.2⟩
    · apply ih
      intro u hu
      apply hf u
      simp only [positiveDelaySpan, List.map_cons, List.sum_cons] at *
      have hd := nonrealModeDelay_nonneg p
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- A finite positive delay average never exceeds all its actual inputs:
some original signal value within the backward span is at least the average. -/
theorem exists_positiveDelayAverage_le (L : List ℂ) (f : ℝ → ℝ) (t : ℝ) :
    ∃ u ∈ Icc (t - positiveDelaySpan L) t, positiveDelayAverage L f t ≤ f u := by
  induction L generalizing t with
  | nil => exact ⟨t, by simp [positiveDelaySpan], le_rfl⟩
  | cons p L ih =>
    have hd := nonrealModeDelay_nonneg p
    have hw := nonrealModeDelayWeight_pos p
    have hw1 : 0 < 1 + nonrealModeDelayWeight p := by linarith
    rcases le_total (positiveDelayAverage L f t)
      (positiveDelayAverage L f (t - nonrealModeDelay p)) with h | h
    · obtain ⟨u, hu, hh⟩ := ih (t - nonrealModeDelay p)
      refine ⟨u, ?_, le_trans ?_ hh⟩
      · simp only [positiveDelaySpan, List.map_cons, List.sum_cons] at *
        exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
      · change nonrealModeDelayAverage p (positiveDelayAverage L f) t ≤ _
        rw [nonrealModeDelayAverage, div_le_iff₀ hw1]
        nlinarith
    · obtain ⟨u, hu, hh⟩ := ih t
      refine ⟨u, ?_, le_trans ?_ hh⟩
      · simp only [positiveDelaySpan, List.map_cons, List.sum_cons] at *
        exact ⟨by linarith [hu.1], hu.2⟩
      · change nonrealModeDelayAverage p (positiveDelayAverage L f) t ≤ _
        rw [nonrealModeDelayAverage, div_le_iff₀ hw1]
        nlinarith [mul_le_mul_of_nonneg_left h hw.le]

/-- Nonnegative delays preserve causal support exactly. -/
theorem positiveDelayAverage_eq_zero_of_nonpositive (L : List ℂ) {f : ℝ → ℝ}
    (hf : ∀ t : ℝ, t ≤ 0 → f t = 0) {t : ℝ} (ht : t ≤ 0) :
    positiveDelayAverage L f t = 0 := by
  induction L generalizing t with
  | nil => exact hf t ht
  | cons p L ih =>
    change nonrealModeDelayAverage p (positiveDelayAverage L f) t = 0
    rw [nonrealModeDelayAverage, ih ht, ih (by linarith [nonrealModeDelay_nonneg p])]
    simp

private theorem translated_laplace_eq (f : ℝ → ℝ) (z : ℂ) (h t : ℝ) :
    (f (t - h) : ℂ) * Complex.exp (-z * (t : ℂ)) =
      Complex.exp (-z * (h : ℂ)) *
        ((f (t - h) : ℂ) * Complex.exp (-z * ((t - h : ℝ) : ℂ))) := by
  rw [mul_comm _ ((f (t - h) : ℂ) * _), mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem average_laplace_eq (p : ℂ) (f : ℝ → ℝ) (z : ℂ) (t : ℝ) :
    (nonrealModeDelayAverage p f t : ℂ) * Complex.exp (-z * (t : ℂ)) =
      ((f t : ℂ) * Complex.exp (-z * (t : ℂ)) +
        (nonrealModeDelayWeight p : ℂ) * Complex.exp (-z * (nonrealModeDelay p : ℂ)) *
          ((f (t - nonrealModeDelay p) : ℂ) *
            Complex.exp (-z * ((t - nonrealModeDelay p : ℝ) : ℂ)))) /
        (1 + (nonrealModeDelayWeight p : ℂ)) := by
  have ht := translated_laplace_eq f z (nonrealModeDelay p) t
  unfold nonrealModeDelayAverage
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_one]
  calc
    _ = ((f t : ℂ) * Complex.exp (-z * (t : ℂ)) +
        (nonrealModeDelayWeight p : ℂ) *
          ((f (t - nonrealModeDelay p) : ℂ) * Complex.exp (-z * (t : ℂ)))) /
        (1 + (nonrealModeDelayWeight p : ℂ)) := by ring
    _ = _ := by rw [ht]; ring

/-- Positive finite delay averaging preserves genuine Laplace
integrability on every line where the original signal is integrable. -/
theorem integrable_positiveDelayAverage_laplace (L : List ℂ) {f : ℝ → ℝ} {z : ℂ}
    (hf : Integrable (fun t : ℝ => (f t : ℂ) * Complex.exp (-z * (t : ℂ)))) :
    Integrable (fun t : ℝ => (positiveDelayAverage L f t : ℂ) *
      Complex.exp (-z * (t : ℂ))) := by
  induction L with
  | nil => exact hf
  | cons p L ih =>
    simp only [positiveDelayAverage, average_laplace_eq]
    exact (ih.add ((ih.comp_sub_right (nonrealModeDelay p)).const_mul
      ((nonrealModeDelayWeight p : ℂ) * Complex.exp (-z * (nonrealModeDelay p : ℂ))))).div_const _

/-- The full signed arithmetic transform is multiplied by the complete
positive-delay multiplier. No finite-time remainder is omitted. -/
theorem integral_positiveDelayAverage_laplace (L : List ℂ) {f : ℝ → ℝ} {z : ℂ}
    (hf : Integrable (fun t : ℝ => (f t : ℂ) * Complex.exp (-z * (t : ℂ)))) :
    (∫ t : ℝ, (positiveDelayAverage L f t : ℂ) * Complex.exp (-z * (t : ℂ))) =
      positiveDelayMultiplier L z * ∫ t : ℝ, (f t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
  induction L with
  | nil => simp [positiveDelayAverage, positiveDelayMultiplier]
  | cons p L ih =>
    have hi := integrable_positiveDelayAverage_laplace L hf
    simp only [positiveDelayAverage, average_laplace_eq]
    rw [integral_div, integral_add hi
      ((hi.comp_sub_right (nonrealModeDelay p)).const_mul
        ((nonrealModeDelayWeight p : ℂ) * Complex.exp (-z * (nonrealModeDelay p : ℂ)))),
      integral_const_mul, integral_sub_right_eq_self
        (fun t : ℝ => (positiveDelayAverage L f t : ℂ) * Complex.exp (-z * (t : ℂ)))
        (nonrealModeDelay p), ih]
    change _ = (nonrealModeDelayMultiplier p z * positiveDelayMultiplier L z) * _
    unfold nonrealModeDelayMultiplier
    ring

end
end RiemannGaussian
