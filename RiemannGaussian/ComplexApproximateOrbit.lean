/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Certified approximate unitary orbits

A whole trigonometric grid can be checked by one approximation to its base
rotation and a finite list of rational residuals. The error grows linearly
with the number of rotations because the exact rotation has norm one.
This retains the relation between neighboring phases rather than evaluating
every sine and cosine independently.
-/

namespace RiemannGaussian.ComplexApproximateOrbit
noncomputable section

/-- A bounded approximate orbit of a unit complex number has an explicit
linear accumulated error, with both base and recurrence errors retained. -/
theorem error_le {u r : ℂ} (hu : ‖u‖ = 1) {ε δ B : ℝ}
    (hε : 0 ≤ ε) (hr : ‖r - u‖ ≤ ε) (v : ℕ → ℂ) (hv0 : v 0 = 1)
    {N : ℕ} (hv : ∀ i < N, ‖v i‖ ≤ B)
    (hstep : ∀ i < N, ‖v (i + 1) - r * v i‖ ≤ δ) :
    ∀ n ≤ N, ‖v n - u ^ n‖ ≤ (n : ℝ) * (ε * B + δ) := by
  intro n
  induction n with
  | zero => intro _; simp [hv0]
  | succ n ih =>
    intro hn
    have hnN : n < N := by omega
    have hprev := ih (Nat.le_of_lt hnN)
    have hid : v (n + 1) - u ^ (n + 1) =
        u * (v n - u ^ n) + (r - u) * v n + (v (n + 1) - r * v n) := by
      rw [pow_succ]
      ring
    rw [hid]
    calc
      _ ≤ ‖u * (v n - u ^ n)‖ + ‖(r - u) * v n‖ +
          ‖v (n + 1) - r * v n‖ := (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (n : ℝ) * (ε * B + δ) + ε * B + δ := by
        rw [norm_mul, norm_mul, hu, one_mul]
        exact add_le_add (add_le_add hprev
          (mul_le_mul hr (hv n hnN) (norm_nonneg _) hε)) (hstep n hnN)
      _ = _ := by push_cast; ring

/-- A rectangular enclosure of real and imaginary parts encloses the
complex norm with the sum of the two radii. -/
theorem norm_le_of_components {z : ℂ} {a b : ℝ}
    (ha : |z.re| ≤ a) (hb : |z.im| ≤ b) : ‖z‖ ≤ a + b :=
  (Complex.norm_le_abs_re_add_abs_im z).trans (add_le_add ha hb)

/-- A finite grid with rationally checked recurrence residuals encloses
the exact sine and cosine at every sampled multiple of its base angle. -/
theorem trigonometric_grid_error (θ : ℝ) (r : ℂ) (v : ℕ → ℂ)
    {ε δ B : ℝ} (hε : 0 ≤ ε)
    (hr : ‖r - Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ ε)
    (hv0 : v 0 = 1) {N : ℕ} (hv : ∀ i < N, ‖v i‖ ≤ B)
    (hstep : ∀ i < N, ‖v (i + 1) - r * v i‖ ≤ δ)
    {n : ℕ} (hn : n ≤ N) :
    |(v n).re - Real.cos ((n : ℝ) * θ)| ≤ (n : ℝ) * (ε * B + δ) ∧
      |(v n).im - Real.sin ((n : ℝ) * θ)| ≤ (n : ℝ) * (ε * B + δ) := by
  have h := error_le (Complex.norm_exp_ofReal_mul_I θ) hε hr v hv0 hv hstep n hn
  have hpow : Complex.exp ((θ : ℂ) * Complex.I) ^ n =
      Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    push_cast
    congr 1
    ring
  rw [hpow] at h
  constructor
  · have hh := (Complex.abs_re_le_norm (v n -
        Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I))).trans h
    simpa [Complex.exp_re] using hh
  · have hh := (Complex.abs_im_le_norm (v n -
        Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I))).trans h
    simpa [Complex.exp_im] using hh

end
end RiemannGaussian.ComplexApproximateOrbit
