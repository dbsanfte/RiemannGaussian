/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.LogarithmicShiftPhase
import RiemannGaussian.PhaseConjugation

/-!
# All genuine derivatives of the logarithmic Dirichlet phase

The phase `-t*log(x)` has derivative of order `r+1` equal to
`(-1)^(r+1)*t*r!/x^(r+1)` on the positive axis. Multiplying the whole
family by the sign of a selected derivative makes that derivative positive,
while retaining the exact orientation for the original phase.
The dyadic lower scale and ratio are proved for every derivative order.
-/

namespace RiemannGaussian.LogarithmicDerivativeFamily
noncomputable section
open LogarithmicShiftPhase

/-- The original logarithmic phase and each of its explicit derivatives. -/
def jet (t : ℝ) : ℕ → ℝ → ℝ
  | 0, x => phase t x
  | r + 1, x => (-1 : ℝ) ^ (r + 1) * t * (r.factorial : ℝ) / x ^ (r + 1)

/-- Every member differentiates to the next on the genuine positive
axis, with the factorial and alternating sign retained exactly. -/
theorem hasDerivAt_jet (t : ℝ) (r : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (jet t r) (jet t (r + 1) x) x := by
  cases r with
  | zero =>
    convert! hasDerivAt_phase t hx using 1
    norm_num [jet]
  | succ r =>
    have hd := (hasDerivAt_const x ((-1 : ℝ) ^ (r + 1) * t * (r.factorial : ℝ))).div
      ((hasDerivAt_id x).pow (r + 1)) (pow_ne_zero _ hx.ne')
    convert! hd using 1
    dsimp [jet]
    simp only [zero_mul, zero_sub, mul_one, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp

/-- The entire derivative family with one fixed alternating orientation. -/
def oriented (t : ℝ) (m r : ℕ) (x : ℝ) : ℝ := (-1 : ℝ) ^ m * jet t r x

/-- One orientation is kept consistently through every derivative. -/
theorem hasDerivAt_oriented (t : ℝ) (m r : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (oriented t m r) (oriented t m (r + 1) x) x :=
  (hasDerivAt_jet t r hx).const_mul _

/-- Choosing the sign of the selected derivative gives its exact positive
magnitude, without altering any derivative or factorial factor. -/
theorem oriented_top (t : ℝ) (r : ℕ) (x : ℝ) :
    oriented t (r + 1) (r + 1) x = t * (r.factorial : ℝ) / x ^ (r + 1) := by
  unfold oriented
  rw [jet]
  calc
    _ = ((-1 : ℝ) ^ (r + 1) * (-1 : ℝ) ^ (r + 1)) * t * (r.factorial : ℝ) /
        x ^ (r + 1) := by ring
    _ = _ := by rw [PhaseConjugation.neg_one_pow_mul_self, one_mul]

/-- The actual dyadic lower magnitude at derivative order `k+2`. -/
def lowerScale (t X : ℝ) (k : ℕ) : ℝ :=
  t * ((k + 1).factorial : ℝ) / (2 * X) ^ (k + 2)

/-- The exact dyadic ratio between the upper and lower magnitudes. -/
def ratio (k : ℕ) : ℝ := (2 : ℝ) ^ (k + 2)

/-- Every positive height and scale gives a genuine positive derivative
lower bound at each finite order. -/
theorem lowerScale_pos {t X : ℝ} (ht : 0 < t) (hX : 0 < X) (k : ℕ) :
    0 < lowerScale t X k := by
  unfold lowerScale
  positivity

/-- The curvature ratio is positive at every order. -/
theorem ratio_pos (k : ℕ) : 0 < ratio k := by
  unfold ratio
  positivity

/-- All dyadic derivative bounds hold on the same original interval.
The orientation handles both parities of the derivative order. -/
theorem dyadic_bounds {t X x : ℝ} (ht : 0 ≤ t) (hX : 0 < X) (k : ℕ)
    (hl : X ≤ x) (hu : x ≤ 2 * X) :
    lowerScale t X k ≤ oriented t (k + 2) (k + 2) x ∧
      oriented t (k + 2) (k + 2) x ≤ ratio k * lowerScale t X k := by
  have hx : 0 < x := hX.trans_le hl
  have he : ratio k * lowerScale t X k = t * ((k + 1).factorial : ℝ) / X ^ (k + 2) := by
    unfold ratio lowerScale
    rw [mul_pow]
    field_simp
  change lowerScale t X k ≤ oriented t ((k + 1) + 1) ((k + 1) + 1) x ∧ _
  rw [oriented_top, he]
  constructor
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < x ^ (k + 2))
    gcongr
  · apply div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < X ^ (k + 2))
    gcongr

end
end RiemannGaussian.LogarithmicDerivativeFamily
