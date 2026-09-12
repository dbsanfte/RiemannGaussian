/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.DirichletDyadicBlocks
import RiemannGaussian.EtaUniformTailBound
import RiemannGaussian.EtaZetaPoleBounds
import Mathlib.Data.Nat.Log

/-!
# Actual zeta reconstruction through complete dyadic eta truncations

The exact eta factor reconstructs zeta from all original dyadic blocks,
the final complex endpoint and the full signed tail. The proved adjacent
ratio identity bounds that tail without an extra height factor. An
explicit logarithmic depth discharges its scale condition for every
complex argument; reverse triangle bounds are only applied downstream.
-/

namespace RiemannGaussian.ZetaDyadicTruncation
noncomputable section
open DirichletDyadicBlocks

/-- The full complex dyadic factor multiplying zeta in the eta identity. -/
def etaFactor (s : ℂ) : ℂ := 1 - 2 * zetaPrimeFeature s 2

/-- The actual signed eta tail beyond a complete dyadic cutoff. -/
def remainder (s : ℂ) (J : ℕ) : ℂ := pairedEtaCore s - pairedEtaCorePartialSum (2 ^ J) s

/-- A canonical logarithmic block depth, large enough for the actual
height-uniform eta tail estimate. -/
def depth (s : ℂ) : ℕ := Nat.log 2 (⌈‖s‖⌉₊ + 1)

/-- The feature multiplier is exactly the usual eta factor. -/
theorem factor_eq (s : ℂ) : etaFactor s = 1 - 2 * (2 : ℂ) ^ (-s) := by
  rw [etaFactor, feature_eq_cpow s (by norm_num)]
  norm_num only [Nat.cast_ofNat]

/-- Every finite block and endpoint remains coupled in the exact zeta
reconstruction, before imposing any tail-scale or norm bound. -/
theorem reconstruction {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (J : ℕ) :
    etaFactor s * riemannZeta s =
      (∑ j ∈ Finset.range (J + 1), block s j) -
        2 * zetaPrimeFeature s 2 * (∑ j ∈ Finset.range J, block s j) -
          zetaPrimeFeature s (2 ^ (J + 1)) + remainder s J := by
  rw [factor_eq, ← pairedEtaCore_eq_factor_riemannZeta_of_re_pos_of_ne_one hs hs1,
    ← eta_pow_two_eq_blocks, remainder]
  ring

/-- The full signed remainder equals its actual complex boundary and
convergent adjacent-ratio variation, with every endpoint retained. -/
theorem remainder_eq_adjacent {s : ℂ} (hs : 0 < s.re) (J : ℕ)
    (hscale : ‖s‖ ≤ ((2 * 2 ^ J + 1 : ℕ) : ℝ)) :
    remainder s J = pairedEtaAdjacentBoundary s ((2 * 2 ^ J + 1 : ℕ) : ℝ) +
      ∑' n : ℕ, pairedEtaAdjacentDefect s ((2 * (n + 2 ^ J) + 1 : ℕ) : ℝ) :=
  pairedEtaCore_tail_eq_adjacent hs (2 ^ J) hscale

/-- The complete actual tail has no additional height factor once its
physical cutoff exceeds the argument norm. -/
theorem remainder_bound {s : ℂ} (hs : 0 < s.re) (J : ℕ)
    (hscale : ‖s‖ ≤ ((2 * 2 ^ J + 1 : ℕ) : ℝ)) :
    ‖remainder s J‖ ≤ 2 * (((2 * 2 ^ J + 1 : ℕ) : ℝ) ^ (-s.re)) :=
  norm_pairedEtaCore_tail_le_two hs (2 ^ J) hscale

/-- The dyadic factor has its exact reverse-triangle lower bound at
every argument; its complex value remains available upstream. -/
theorem factor_lower (s : ℂ) : (2 : ℝ) ^ (1 - s.re) - 1 ≤ ‖etaFactor s‖ := by
  have h := norm_sub_norm_le (2 * (2 : ℂ) ^ (-s)) (1 : ℂ)
  rw [norm_two_mul_two_cpow_neg, norm_one, norm_sub_rev, ← factor_eq] at h
  exact h

/-- The reverse-triangle factor is strictly positive left of one. -/
theorem factor_lower_pos {s : ℂ} (hs : s.re < 1) : 0 < (2 : ℝ) ^ (1 - s.re) - 1 := by
  have h : 1 < (2 : ℝ) ^ (1 - s.re) := Real.one_lt_rpow (by norm_num) (by linarith)
  linarith

/-- The original zeta function is bounded by the fully coupled finite
block expression and the proved tail, with no unknown analytic premise. -/
theorem zeta_norm_le {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) (J : ℕ)
    (hscale : ‖s‖ ≤ ((2 * 2 ^ J + 1 : ℕ) : ℝ)) :
    ‖riemannZeta s‖ ≤
      (‖(∑ j ∈ Finset.range (J + 1), block s j) -
          2 * zetaPrimeFeature s 2 * (∑ j ∈ Finset.range J, block s j) -
            zetaPrimeFeature s (2 ^ (J + 1))‖ +
        2 * (((2 * 2 ^ J + 1 : ℕ) : ℝ) ^ (-s.re))) /
          ((2 : ℝ) ^ (1 - s.re) - 1) := by
  have hne : s ≠ 1 := by intro h; simp [h] at hs1
  have he := congrArg norm (reconstruction hs hne J)
  rw [norm_mul] at he
  have hu := (norm_add_le
    ((∑ j ∈ Finset.range (J + 1), block s j) -
      2 * zetaPrimeFeature s 2 * (∑ j ∈ Finset.range J, block s j) -
        zetaPrimeFeature s (2 ^ (J + 1))) (remainder s J)).trans
    (add_le_add le_rfl (remainder_bound hs J hscale))
  rw [← he] at hu
  have hl := mul_le_mul_of_nonneg_right (factor_lower s) (norm_nonneg (riemannZeta s))
  apply (le_div_iff₀ (factor_lower_pos hs1)).mpr
  nlinarith

/-- The canonical logarithmic depth satisfies the actual tail-scale
condition at every complex argument. -/
theorem depth_scale (s : ℂ) : ‖s‖ ≤ ((2 * 2 ^ depth s + 1 : ℕ) : ℝ) := by
  have hc := Nat.le_ceil ‖s‖
  have hp := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (⌈‖s‖⌉₊ + 1)
  rw [Nat.succ_eq_add_one, pow_succ] at hp
  have hr : ((⌈‖s‖⌉₊ + 1 : ℕ) : ℝ) < ((2 : ℕ) ^ depth s * 2 : ℕ) := by
    exact_mod_cast hp
  push_cast at hr ⊢
  nlinarith

/-- The canonical dyadic cutoff stays below the argument norm plus two,
so its number of blocks is genuinely logarithmic in height. -/
theorem depth_length_lt (s : ℂ) : ((2 ^ depth s : ℕ) : ℝ) < ‖s‖ + 2 := by
  have hp := Nat.pow_log_le_self 2 (show ⌈‖s‖⌉₊ + 1 ≠ 0 by omega)
  have hr : ((2 ^ depth s : ℕ) : ℝ) ≤ ((⌈‖s‖⌉₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast hp
  have hc := Nat.ceil_lt_add_one (norm_nonneg s)
  push_cast at hr ⊢
  linarith

/-- An explicit real logarithmic bound for the canonical number of
dyadic blocks, uniform over all complex arguments. -/
theorem depth_le_log (s : ℂ) : (depth s : ℝ) ≤ Real.log (‖s‖ + 2) / Real.log 2 := by
  have hp : (2 : ℝ) ^ depth s ≤ ‖s‖ + 2 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using (depth_length_lt s).le
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ depth s) hp
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl

end
end RiemannGaussian.ZetaDyadicTruncation
