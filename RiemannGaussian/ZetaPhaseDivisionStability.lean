/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseContactQuotient

/-!
# Stability of contact division with its signed recurrence retained

Synthetic division propagates a coefficient enclosure from the highest
degree downwards. The recurrence identity is retained before taking the
bound, avoiding any division by a contact separation. This will transfer
rational residual checks to the canonical exact quotient.
-/

open scoped Classical Polynomial
open Polynomial

namespace RiemannGaussian

noncomputable section

/-- One synthetic division is controlled by its input error, contact
error, and signed recurrence residual. The degree bound makes the
backwards recurrence finite. -/
theorem abs_coeff_divByMonic_sub_center_le
    {p : ℝ[X]} {q c e r M d : ℝ} {u v : ℕ → ℝ}
    (hp : p.natDegree ≤ 24) (hq : |q| ≤ 1) (he : 0 ≤ e) (hr : 0 ≤ r)
    (hM : 0 ≤ M) (hd : 0 ≤ d) (hqc : |q - c| ≤ r)
    (hu : ∀ k ≤ 24, |p.coeff k - u k| ≤ e)
    (hv : ∀ k ≤ 24, |v k| ≤ M) (htop : v 24 = 0)
    (hres : ∀ k < 24, |v k - u (k + 1) - c * v (k + 1)| ≤ d)
    {k : ℕ} (hk : k ≤ 24) :
    |(p /ₘ (X - C q)).coeff k - v k| ≤ 24 * (e + r * M + d) := by
  let s := p /ₘ (X - C q)
  let A := e + r * M + d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have htop' : s.coeff 24 = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    dsimp [s]
    rw [natDegree_divByMonic p (monic_X_sub_C q), natDegree_X_sub_C]
    omega
  have hstep {l : ℕ} (hl : l < 24) :
      |s.coeff l - v l| ≤ A + |s.coeff (l + 1) - v (l + 1)| := by
    have hid : s.coeff l - v l =
        (p.coeff (l + 1) - u (l + 1)) +
        q * (s.coeff (l + 1) - v (l + 1)) +
        (q - c) * v (l + 1) - (v l - u (l + 1) - c * v (l + 1)) := by
      rw [show s.coeff l = p.coeff (l + 1) + q * s.coeff (l + 1) from
        coeff_divByMonic_X_sub_C_rec p q l]
      ring
    have h1 := hu (l + 1) (by omega)
    have h2 : |q * (s.coeff (l + 1) - v (l + 1))| ≤ |s.coeff (l + 1) - v (l + 1)| := by
      rw [abs_mul]
      simpa using mul_le_mul_of_nonneg_right hq (abs_nonneg (s.coeff (l + 1) - v (l + 1)))
    have h3 : |(q - c) * v (l + 1)| ≤ r * M := by
      rw [abs_mul]
      exact mul_le_mul hqc (hv (l + 1) (by omega)) (abs_nonneg _) hr
    have h4 := hres l hl
    rw [hid]
    calc
      _ ≤ |p.coeff (l + 1) - u (l + 1)| +
          |q * (s.coeff (l + 1) - v (l + 1))| + |(q - c) * v (l + 1)| +
          |v l - u (l + 1) - c * v (l + 1)| := by
        grw [abs_sub, abs_add_le, abs_add_le]
      _ ≤ _ := by dsimp [A]; linarith
  have hback (m : ℕ) (hm : m ≤ 24) :
      |s.coeff (24 - m) - v (24 - m)| ≤ (m : ℝ) * A := by
    induction m with
    | zero => simp [htop, htop']
    | succ m ih =>
      have hm' : m ≤ 24 := by omega
      have ih' := ih hm'
      have h := hstep (l := 24 - (m + 1)) (by omega)
      rw [show 24 - (m + 1) + 1 = 24 - m by omega] at h
      norm_num only [Nat.cast_add, Nat.cast_one] at ⊢
      nlinarith
  have h := hback (24 - k) (by omega)
  rw [Nat.sub_sub_self hk] at h
  have hcast : ((24 - k : ℕ) : ℝ) ≤ 24 := by exact_mod_cast Nat.sub_le 24 k
  exact h.trans (mul_le_mul_of_nonneg_right hcast hA)

/-- The ordered contact used by each of the eight synthetic divisions. -/
def phaseContactDivisionPoint (q : Fin 4 → ℝ) (j : ℕ) : ℝ := q ⟨(j / 2) % 4, Nat.mod_lt _ (by decide)⟩

/-- All intermediate polynomial carriers in successive contact division. -/
def phaseContactDivisionStage (q : Fin 4 → ℝ) (p : ℝ[X]) : ℕ → ℝ[X]
  | 0 => p
  | j + 1 => phaseContactDivisionStage q p j /ₘ (X - C (phaseContactDivisionPoint q j))

/-- Every intermediate carrier stays within the original degree bound. -/
theorem phaseContactDivisionStage_natDegree_le (q : Fin 4 → ℝ) (p : ℝ[X]) (j : ℕ) :
    (phaseContactDivisionStage q p j).natDegree ≤ p.natDegree := by
  induction j with
  | zero => exact le_rfl
  | succ j ih =>
    rw [phaseContactDivisionStage, natDegree_divByMonic _ (monic_X_sub_C _), natDegree_X_sub_C]
    omega

/-- After eight steps the intermediate representation is the exact
linear deflation map used in the contact factorization. -/
theorem phaseContactDivisionStage_eight (q : Fin 4 → ℝ) (p : ℝ[X]) :
    phaseContactDivisionStage q p 8 = phaseContactDeflate q p := by
  rfl

end

end RiemannGaussian
