/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SecondDerivativeIncrements

/-!
# Derivative families on exact shifted overlaps

Differencing commutes with each derivative in a genuine finite derivative
family. The highest remaining derivative is controlled by the next one
on the interval between the two shifted points. The whole interval stays
inside the original phase domain; no extension by the shift is needed.
-/

namespace RiemannGaussian.ShiftedDerivativeFamily
noncomputable section

/-- The exact difference of each member of a derivative family. -/
def difference (F : ℕ → ℝ → ℝ) (h : ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  F r (x + h) - F r x

/-- Differentiating an exact real shift difference keeps both endpoints. -/
theorem hasDerivAt_difference (F : ℕ → ℝ → ℝ) (h : ℝ) (r : ℕ) (x : ℝ)
    (h0 : HasDerivAt (F r) (F (r + 1) x) x)
    (h1 : HasDerivAt (F r) (F (r + 1) (x + h)) (x + h)) :
    HasDerivAt (difference F h r) (difference F h (r + 1) x) x := by
  convert! (h1.comp x ((hasDerivAt_id x).add_const h)).sub h0 using 1
  simp only [difference, mul_one]

/-- Both points and the interval between them stay inside the original
domain for every point of the complete natural overlap. -/
theorem overlap_subset (a : ℝ) {N h : ℕ} (hh : h ≤ N) {x : ℝ}
    (hx : x ∈ Set.Icc a (a + (N - h : ℕ))) :
    Set.Icc x (x + h) ⊆ Set.Icc a (a + N) := by
  have hc : ((N - h : ℕ) : ℝ) = (N : ℝ) - h := Nat.cast_sub hh
  rw [hc] at hx
  intro y hy
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- A genuine derivative family remains a derivative family throughout
the exact overlap after shifting. -/
theorem derivative_family (F : ℕ → ℝ → ℝ) (a : ℝ) (N q h : ℕ) (hh : h ≤ N)
    (hd : ∀ r < q, ∀ x ∈ Set.Icc a (a + N), HasDerivAt (F r) (F (r + 1) x) x) :
    ∀ r < q, ∀ x ∈ Set.Icc a (a + (N - h : ℕ)),
      HasDerivAt (difference F h r) (difference F h (r + 1) x) x := by
  intro r hr x hx
  have hsub := overlap_subset a hh hx
  exact hasDerivAt_difference F h r x
    (hd r hr x (hsub ⟨le_rfl, by linarith [Nat.cast_nonneg (α := ℝ) h]⟩))
    (hd r hr (x + h) (hsub ⟨by linarith [Nat.cast_nonneg (α := ℝ) h], le_rfl⟩))

/-- The next derivative bounds the complete top difference by the
actual shift length. Its curvature ratio is unchanged on the overlap. -/
theorem top_bounds (F : ℕ → ℝ → ℝ) (a : ℝ) (N q h : ℕ) (hh : h ≤ N)
    {ℓ A : ℝ}
    (hd : ∀ x ∈ Set.Icc a (a + N), HasDerivAt (F q) (F (q + 1) x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), ℓ ≤ F (q + 1) x ∧ F (q + 1) x ≤ A * ℓ) :
    ∀ x ∈ Set.Icc a (a + (N - h : ℕ)),
      (h : ℝ) * ℓ ≤ difference F h q x ∧ difference F h q x ≤ A * ((h : ℝ) * ℓ) := by
  intro x hx
  have hsub := overlap_subset a hh hx
  have hb := SecondDerivativeIncrements.difference_bounds (F q) (F (q + 1))
    (show x ≤ x + (h : ℝ) by linarith [Nat.cast_nonneg (α := ℝ) h])
    (fun y hy ↦ hd y (hsub hy)) (fun y hy ↦ hr y (hsub hy))
  simpa only [difference, add_sub_cancel_left, mul_comm ℓ (h : ℝ),
    mul_assoc, mul_comm ℓ (h : ℝ)] using hb

end
end RiemannGaussian.ShiftedDerivativeFamily
