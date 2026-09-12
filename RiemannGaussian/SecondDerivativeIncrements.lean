/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.FirstDerivativeTest

/-!
# Second derivatives control the exact discrete phase increments

Apply the mean value theorem first to the derivative on each real unit
interval, and then to the real unit-increment function between two indices.
This retains their full separation, without the loss of one unit incurred
by comparing unrelated witnesses for the original phase increments.
Every derivative is evaluated inside the original closed phase domain.
-/

namespace RiemannGaussian.SecondDerivativeIncrements
noncomputable section
open FiniteKuzminLandau

/-- Bounds for a derivative give two-sided bounds for the exact endpoint
difference, including the degenerate interval. -/
theorem difference_bounds (f f' : ℝ → ℝ) {a b ℓ U : ℝ} (hab : a ≤ b)
    (hd : ∀ x ∈ Set.Icc a b, HasDerivAt f (f' x) x)
    (hr : ∀ x ∈ Set.Icc a b, ℓ ≤ f' x ∧ f' x ≤ U) :
    ℓ * (b - a) ≤ f b - f a ∧ f b - f a ≤ U * (b - a) := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f f' hab
    (fun y hy ↦ (hd y hy).continuousAt.continuousWithinAt)
    (fun y hy ↦ hd y (Set.Ioo_subset_Icc_self hy))
  have he' : f' x * (b - a) = f b - f a :=
    (eq_div_iff (sub_pos.mpr hab).ne').mp he
  have hr' := hr x (Set.Ioo_subset_Icc_self hx)
  constructor <;> nlinarith [hr'.1, hr'.2]

/-- The real unit increment retains the exact two phase endpoints. -/
def unitIncrement (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x + 1) - f x

/-- Its derivative is the exact difference of the two first derivatives. -/
theorem hasDerivAt_unitIncrement (f f' : ℝ → ℝ) (x : ℝ)
    (h0 : HasDerivAt f (f' x) x) (h1 : HasDerivAt f (f' (x + 1)) (x + 1)) :
    HasDerivAt (unitIncrement f) (f' (x + 1) - f' x) x := by
  convert! (h1.comp x ((hasDerivAt_id x).add_const 1)).sub h0 using 1
  simp only [mul_one]

/-- Sampling the real unit increment gives precisely the phase increment
used by finite summation by parts, with no index displacement. -/
theorem unitIncrement_eq (f : ℝ → ℝ) (a : ℝ) (n : ℕ) :
    unitIncrement f (a + n) = increment (fun k ↦ f (a + k)) n := by
  simp only [unitIncrement, increment, Nat.cast_add, Nat.cast_one, add_assoc]

/-- Two-sided second-derivative bounds control every exact separation of
discrete increments. The last required phase endpoint is `a + N`. -/
theorem increment_gap_bounds (f f' f'' : ℝ → ℝ) (a : ℝ) (N : ℕ) {ℓ U : ℝ}
    (hd : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f (f' x) x)
    (hd' : ∀ x ∈ Set.Icc a (a + N), HasDerivAt f' (f'' x) x)
    (hr : ∀ x ∈ Set.Icc a (a + N), ℓ ≤ f'' x ∧ f'' x ≤ U)
    {i j : ℕ} (hj : j < N) (hij : i ≤ j) :
    ℓ * ((j : ℝ) - i) ≤
        increment (fun k ↦ f (a + k)) j - increment (fun k ↦ f (a + k)) i ∧
      increment (fun k ↦ f (a + k)) j - increment (fun k ↦ f (a + k)) i ≤
        U * ((j : ℝ) - i) := by
  have hijR : (i : ℝ) ≤ j := by exact_mod_cast hij
  have hjR : (j : ℝ) + 1 ≤ N := by exact_mod_cast Nat.succ_le_iff.mpr hj
  have hsub {x : ℝ} (hx : x ∈ Set.Icc (a + i) (a + j)) :
      Set.Icc x (x + 1) ⊆ Set.Icc a (a + N) := by
    intro y hy
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2, Nat.cast_nonneg (α := ℝ) i]
  have hg : ∀ x ∈ Set.Icc (a + i) (a + j),
      HasDerivAt (unitIncrement f) (f' (x + 1) - f' x) x := by
    intro x hx
    exact hasDerivAt_unitIncrement f f' x
      (hd x (hsub hx ⟨le_rfl, by linarith⟩))
      (hd (x + 1) (hsub hx ⟨by linarith, le_rfl⟩))
  have hgr : ∀ x ∈ Set.Icc (a + i) (a + j),
      ℓ ≤ f' (x + 1) - f' x ∧ f' (x + 1) - f' x ≤ U := by
    intro x hx
    have h := difference_bounds f' f'' (show x ≤ x + 1 by linarith)
      (fun y hy ↦ hd' y (hsub hx hy)) (fun y hy ↦ hr y (hsub hx hy))
    simpa only [add_sub_cancel_left, mul_one] using h
  have h := difference_bounds (unitIncrement f) (fun x ↦ f' (x + 1) - f' x)
    (show a + (i : ℝ) ≤ a + j by linarith) hg hgr
  simpa only [unitIncrement_eq, add_sub_add_left_eq_sub] using h

end
end RiemannGaussian.SecondDerivativeIncrements
