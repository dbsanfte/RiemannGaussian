/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovShortDirichlet
import RiemannGaussian.VinogradovDyadic

/-!
# Stronger savings on the actual dyadic zeta blocks

The shorter moment orders enter the literal interval [X,2X), retaining
all damping weights and the complete shift boundary. The saving on the
physical scale is 1/(6400*k^2), improved to 1/(2048*k^2) for k>=48.
-/

namespace RiemannGaussian.VinogradovShortDyadic
noncomputable section
open scoped BigOperators
open DirichletDyadicBlocks VinogradovShortResonance
open VinogradovDyadic (root_saving_le)

/-- The complete original block on [X,2X) has an explicit physical-scale
saving, including all real damping and the full shift boundary. -/
theorem original_block_bound (k M X : ℕ) (hk : 12 ≤ k) (hrM : (4 * k + 1) * k ≤ M)
    (hlo : M ^ 4 ≤ X) (hhi : X ≤ 2 * M ^ 4) (s : ℂ) (hσ : 0 ≤ s.re)
    (htlo : (M : ℝ) ^ (2 * k - 2) ≤ s.im) (hthi : s.im ≤ (M : ℝ) ^ (2 * k)) :
    ‖∑ n ∈ Finset.range X, zetaPrimeFeature s (X + n)‖ ≤
      6 * (X : ℝ) ^ (1 - s.re - saving k / 4) +
        2 * (X : ℝ) ^ (1 / 2 - s.re) := by
  have hkM : k ≤ M := by nlinarith
  have hM : 1 ≤ M := by omega
  have hX : 1 ≤ X := (Nat.one_le_pow _ _ hM).trans hlo
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hlow : (M : ℝ) ^ 4 ≤ X := by exact_mod_cast hlo
  have hhigh : (X : ℝ) ≤ 2 * (M : ℝ) ^ 4 := by exact_mod_cast hhi
  have hb := VinogradovShortDirichlet.feature_block_bound k hk M hM hrM s hσ
    htlo hthi X hlow hhigh (X - 1) (by omega)
  rw [Nat.sub_add_cancel hX] at hb
  have hmass : (∑ n ∈ Finset.range X, zetaPrimeExpWeight s.re (X + n)) ≤
      (X : ℝ) * (X : ℝ) ^ (-s.re) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range X, (X : ℝ) ^ (-s.re) := by
        apply Finset.sum_le_sum
        intro n _
        rw [weight_eq_rpow s.re (by omega : 0 < X + n)]
        exact Real.rpow_le_rpow_of_nonpos hXr
          (by exact_mod_cast Nat.le_add_right X n) (neg_nonpos.mpr hσ)
      _ = _ := by simp
  let delta := saving k
  have hd : 0 ≤ delta := (saving_bounds (by omega : 1 ≤ k)).1.le
  have hd4 : delta ≤ 4 := ((saving_bounds (by omega : 1 ≤ k)).2).trans (by norm_num)
  have hsav := root_saving_le hMr hXr hhigh hd hd4
  have hroot : (M : ℝ) ^ 2 ≤ (X : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    apply (Real.le_sqrt (sq_nonneg _) hXr.le).mpr
    simpa only [← pow_mul, show (2 : ℕ) * 2 = 4 by omega] using hlow
  rw [weight_eq_rpow s.re (by omega : 0 < X)] at hb
  have hbound := hb.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmass (by positivity)) le_rfl)
  have hlead : 3 * (2 * (X : ℝ) ^ (-delta / 4)) * ((X : ℝ) * (X : ℝ) ^ (-s.re)) =
      6 * (X : ℝ) ^ (1 - s.re - delta / 4) := by
    rw [show 1 - s.re - delta / 4 = (-delta / 4) + 1 + (-s.re) by ring,
      Real.rpow_add hXr, Real.rpow_add hXr, Real.rpow_one]
    ring
  have htail : 2 * (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (-s.re) =
      2 * (X : ℝ) ^ (1 / 2 - s.re) := by
    rw [mul_assoc, ← Real.rpow_add hXr]
    rfl
  calc
    _ ≤ 3 * (M : ℝ) ^ (-delta) * ((X : ℝ) * (X : ℝ) ^ (-s.re)) +
        2 * (M : ℝ) ^ 2 * (X : ℝ) ^ (-s.re) := hbound
    _ ≤ 3 * (2 * (X : ℝ) ^ (-delta / 4)) * ((X : ℝ) * (X : ℝ) ^ (-s.re)) +
        2 * (X : ℝ) ^ (1 / 2 : ℝ) * (X : ℝ) ^ (-s.re) := by gcongr
    _ = _ := by rw [hlead, htail]

/-- Specializing the original endpoint to a dyadic integer keeps exactly
the block used by the existing zeta reconstruction. -/
theorem dyadic_block_bound (k M j : ℕ) (hk : 12 ≤ k) (hrM : (4 * k + 1) * k ≤ M)
    (hlo : M ^ 4 ≤ 2 ^ j) (hhi : 2 ^ j ≤ 2 * M ^ 4) (s : ℂ) (hσ : 0 ≤ s.re)
    (htlo : (M : ℝ) ^ (2 * k - 2) ≤ s.im) (hthi : s.im ≤ (M : ℝ) ^ (2 * k)) :
    ‖block s j‖ ≤
      6 * ((2 ^ j : ℕ) : ℝ) ^ (1 - s.re - saving k / 4) +
        2 * ((2 ^ j : ℕ) : ℝ) ^ (1 / 2 - s.re) :=
  original_block_bound k M (2 ^ j) hk hrM hlo hhi s hσ htlo hthi

end
end RiemannGaussian.VinogradovShortDyadic
