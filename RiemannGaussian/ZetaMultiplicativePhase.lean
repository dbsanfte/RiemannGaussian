/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPrimeFilterCalculus

/-!
# Exact multiplicative phase transport for arithmetic matrices

The logarithmic height phase factors into unit row and column phases on
positive integers. This gives an exact transport identity for the full
factorial kernel, retaining its polynomial amplitude and an arbitrary
arithmetic matrix. Uniform bounds over all complex coefficient families
with fixed magnitude budgets are consequently equivalent at every height.
The actual fixed Möbius coefficients have additional structure; the result
does not rule out cancellation estimates that exploit that structure.

The same quantifier issue applies to signed floors. A floor uniform over
all complex coefficient families is equivalent to a norm bound, since a
unit rotation of one family rotates the entire response. This remains
true at cofinally many orders. It does not strengthen the open floor for
the one fixed arithmetic family to such a uniform assertion.
-/

open Complex ComplexConjugate
open scoped Classical

namespace RiemannGaussian.MultiplicativePhase
noncomputable section

/-- The exact unit phase on the multiplicative logarithmic coordinate. -/
def phase (y x : ℝ) : ℂ := Complex.exp (-I * (y : ℂ) * (Real.log x : ℂ))

/-- Every phase modulation preserves the magnitude of a coefficient. -/
theorem norm_phase (y x : ℝ) : ‖phase y x‖ = 1 := by
  simp [phase, Complex.norm_exp]

/-- Positive factorization splits the exact phase into row and column factors. -/
theorem phase_mul (y : ℝ) {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    phase y (d * m : ℕ) = phase y d * phase y m := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [phase, Nat.cast_mul, Real.log_mul hd0 hm0, Complex.ofReal_add,
    mul_add, Complex.exp_add]

/-- The full complex polynomial amplitude is retained when shifting height. -/
theorem kernel_shift (p : Polynomial ℂ) (N : ℕ) (σ y z x : ℝ) :
    zetaPrimeFilterKernel p N ((σ : ℂ) + I * (y + z : ℝ)) x =
      phase z x * zetaPrimeFilterKernel p N ((σ : ℂ) + I * y) x := by
  have he : -((σ : ℂ) + I * (y + z : ℝ)) * (Real.log x : ℂ) =
      -I * (z : ℂ) * (Real.log x : ℂ) + -((σ : ℂ) + I * y) * (Real.log x : ℂ) := by
    push_cast
    ring
  rw [zetaPrimeFilterKernel, he, Complex.exp_add, zetaPrimeFilterKernel, phase]
  ring

/-- An arbitrary finite arithmetic matrix with the original factorial kernel.
The matrix can retain every cutoff, sieve and coprimality restriction. -/
def bilinear (p : Polynomial ℂ) (N : ℕ) (σ : ℝ) (T U : Finset ℕ)
    (c : ℕ → ℕ → ℂ) (y : ℝ) (a b : ℕ → ℂ) : ℂ :=
  ∑ d ∈ T, ∑ m ∈ U,
    a d * b m * c d m * zetaPrimeFilterKernel p N ((σ : ℂ) + I * y) (d * m : ℕ)

/-- The entire matrix retains the same response under exact row and column
phase modulation, even when its arithmetic restrictions couple both factors. -/
theorem bilinear_shift (p : Polynomial ℂ) (N : ℕ) (σ : ℝ) (T U : Finset ℕ)
    (hT : ∀ d ∈ T, 0 < d) (hU : ∀ m ∈ U, 0 < m)
    (c : ℕ → ℕ → ℂ) (y z : ℝ) (a b : ℕ → ℂ) :
    bilinear p N σ T U c (y + z) a b =
      bilinear p N σ T U c y (fun d ↦ a d * phase z d) (fun m ↦ b m * phase z m) := by
  unfold bilinear
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro m hm
  rw [kernel_shift, phase_mul z (hT d hd) (hU m hm)]
  ring

/-- Uniform bounds on all coefficient families with fixed magnitude budgets
cannot gain from height alone: they are equivalent at every height to zero
height. This does not remove phase information from the actual Möbius family. -/
theorem uniform_bound_iff_zero_height (p : Polynomial ℂ) (N : ℕ) (σ : ℝ)
    (T U : Finset ℕ) (hT : ∀ d ∈ T, 0 < d) (hU : ∀ m ∈ U, 0 < m)
    (c : ℕ → ℕ → ℂ) (y : ℝ) (A B : ℕ → ℝ) (C : ℝ) :
    (∀ a b : ℕ → ℂ, (∀ d ∈ T, ‖a d‖ ≤ A d) → (∀ m ∈ U, ‖b m‖ ≤ B m) →
      ‖bilinear p N σ T U c y a b‖ ≤ C) ↔
    (∀ a b : ℕ → ℂ, (∀ d ∈ T, ‖a d‖ ≤ A d) → (∀ m ∈ U, ‖b m‖ ≤ B m) →
      ‖bilinear p N σ T U c 0 a b‖ ≤ C) := by
  constructor
  · intro h a b ha hb
    have he := bilinear_shift p N σ T U hT hU c y (-y) a b
    rw [add_neg_cancel] at he
    rw [he]
    apply h
    · intro d hd
      simpa only [norm_mul, norm_phase, mul_one] using ha d hd
    · intro m hm
      simpa only [norm_mul, norm_phase, mul_one] using hb m hm
  · intro h a b ha hb
    have he := bilinear_shift p N σ T U hT hU c 0 y a b
    rw [zero_add] at he
    rw [he]
    apply h
    · intro d hd
      simpa only [norm_mul, norm_phase, mul_one] using ha d hd
    · intro m hm
      simpa only [norm_mul, norm_phase, mul_one] using hb m hm

/-- Rotating one coefficient family rotates the complete response, with
the correlated matrix, masks and factorial amplitude unchanged. -/
theorem bilinear_const_mul_left (p : Polynomial ℂ) (N : ℕ) (σ : ℝ)
    (T U : Finset ℕ) (c : ℕ → ℕ → ℂ) (y : ℝ) (a b : ℕ → ℂ) (v : ℂ) :
    bilinear p N σ T U c y (fun d => v * a d) b =
      v * bilinear p N σ T U c y a b := by
  simp only [bilinear, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- A signed floor UNIFORM over arbitrary complex coefficient families
is already a norm bound. This does not apply to the single fixed arithmetic
family in the joint-floor target: the unit rotation used here changes it. -/
theorem uniform_re_floor_iff_norm_bound (p : Polynomial ℂ) (N : ℕ) (σ : ℝ)
    (T U : Finset ℕ) (c : ℕ → ℕ → ℂ) (y : ℝ) (A B : ℕ → ℝ) (C : ℝ) :
    (∀ a b : ℕ → ℂ, (∀ d ∈ T, ‖a d‖ ≤ A d) → (∀ m ∈ U, ‖b m‖ ≤ B m) →
      -C ≤ (bilinear p N σ T U c y a b).re) ↔
    (∀ a b : ℕ → ℂ, (∀ d ∈ T, ‖a d‖ ≤ A d) → (∀ m ∈ U, ‖b m‖ ≤ B m) →
      ‖bilinear p N σ T U c y a b‖ ≤ C) := by
  constructor
  · intro h a b ha hb
    let z := bilinear p N σ T U c y a b
    by_cases hz : z = 0
    · have hf := h a b ha hb
      change -C ≤ z.re at hf
      change ‖z‖ ≤ C
      simp only [hz, zero_re, norm_zero] at hf ⊢
      linarith
    · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      let v : ℂ := -conj z / (‖z‖ : ℂ)
      have hv : ‖v‖ = 1 := by
        simp [v, hn]
      have hvz : v * z = -(‖z‖ : ℂ) := by
        dsimp [v]
        rw [div_mul_eq_mul_div, neg_mul, ← normSq_eq_conj_mul_self,
          normSq_eq_norm_sq, ofReal_pow]
        field_simp
      have hf := h (fun d => v * a d) b
        (fun d hd => by simpa only [norm_mul, hv, one_mul] using ha d hd) hb
      rw [bilinear_const_mul_left] at hf
      change -C ≤ (v * z).re at hf
      rw [hvz, neg_re, ofReal_re] at hf
      change ‖z‖ ≤ C
      linarith
  · intro h a b ha hb
    have hn := h a b ha hb
    have hr := Complex.re_le_norm (-bilinear p N σ T U c y a b)
    simp only [neg_re, norm_neg] at hr
    linarith

/-- Even a one-sided coefficient-uniform estimate at nonzero height is
equivalent to a zero-height norm estimate. No sign of the fixed arithmetic
matrix is changed, and no phase information about actual coefficients is
claimed to be expendable. -/
theorem uniform_re_floor_iff_zero_height_bound (p : Polynomial ℂ) (N : ℕ) (σ : ℝ)
    (T U : Finset ℕ) (hT : ∀ d ∈ T, 0 < d) (hU : ∀ m ∈ U, 0 < m)
    (c : ℕ → ℕ → ℂ) (y : ℝ) (A B : ℕ → ℝ) (C : ℝ) :
    (∀ a b : ℕ → ℂ, (∀ d ∈ T, ‖a d‖ ≤ A d) → (∀ m ∈ U, ‖b m‖ ≤ B m) →
      -C ≤ (bilinear p N σ T U c y a b).re) ↔
    (∀ a b : ℕ → ℂ, (∀ d ∈ T, ‖a d‖ ≤ A d) → (∀ m ∈ U, ‖b m‖ ≤ B m) →
      ‖bilinear p N σ T U c 0 a b‖ ≤ C) :=
  (uniform_re_floor_iff_norm_bound p N σ T U c y A B C).trans
    (uniform_bound_iff_zero_height p N σ T U hT hU c y A B C)

/-- Restricting a coefficient-uniform floor to arbitrarily late orders
does not avoid the same norm requirement. The cofinal quantifier remains
outside the coefficient quantifiers on BOTH sides; this is not a statement
about floors for a fixed family or family-dependent subsequences. -/
theorem cofinal_uniform_floor_iff_zero_height_bound
    (p : ℕ → Polynomial ℂ) (N : ℕ → ℕ) (σ y C : ℕ → ℝ)
    (T U : ℕ → Finset ℕ) (hT : ∀ j d, d ∈ T j → 0 < d)
    (hU : ∀ j m, m ∈ U j → 0 < m)
    (c : ℕ → ℕ → ℕ → ℂ) (A B : ℕ → ℕ → ℝ) :
    (∃ᶠ j in Filter.atTop, ∀ a b : ℕ → ℂ,
      (∀ d ∈ T j, ‖a d‖ ≤ A j d) → (∀ m ∈ U j, ‖b m‖ ≤ B j m) →
      -C j ≤ (bilinear (p j) (N j) (σ j) (T j) (U j) (c j) (y j) a b).re) ↔
    (∃ᶠ j in Filter.atTop, ∀ a b : ℕ → ℂ,
      (∀ d ∈ T j, ‖a d‖ ≤ A j d) → (∀ m ∈ U j, ‖b m‖ ≤ B j m) →
      ‖bilinear (p j) (N j) (σ j) (T j) (U j) (c j) 0 a b‖ ≤ C j) := by
  constructor
  · intro h
    exact h.mono fun j hj =>
      (uniform_re_floor_iff_zero_height_bound (p j) (N j) (σ j) (T j) (U j)
        (hT j) (hU j) (c j) (y j) (A j) (B j) (C j)).mp hj
  · intro h
    exact h.mono fun j hj =>
      (uniform_re_floor_iff_zero_height_bound (p j) (N j) (σ j) (T j) (U j)
        (hT j) (hU j) (c j) (y j) (A j) (B j) (C j)).mpr hj

end
end RiemannGaussian.MultiplicativePhase
