/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFirstExponent

/-!
# Transport the proved global exponent through the actual finite recurrence

The independent exponent k(2u+1)-1/(3k) pays every eligible padded quotient
with one common constant and threshold. Both homogeneous moment premises
in the mixed and signed conditioned recurrences are discharged. The full
finite sum of original intermediate energies remains in each conclusion.

An exact comparison identifies what changing the exponent accomplishes:
after restoring the source scale, only the deep remainder changes. Its
coarse-quotient factor improves by (X/p^a)^(-epsilon); every intermediate
energy is identical. This prevents treating a normalization improvement
as a bound for the remaining energies. The critical exponent is still open.
-/

namespace RiemannGaussian.VinogradovImprovedNormalization
noncomputable section
open VinogradovMeanValue VinogradovConditioningPowerSaving VinogradovNormalizedIteration

/-- The first proved exponent remains in the full normalized recurrence's admissible range. -/
theorem first_exponent_ge_critical {k u : ℕ} (hk : 2 ≤ k) :
    2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤
      (((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ))) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hfrac : 1 / (3 * (k : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have hgap : 1 ≤ (k : ℝ) * ((k : ℝ) - 1) / 2 := by nlinarith
  push_cast
  nlinarith

/-- Pay the exact padded quotient endpoint for any proved eventual homogeneous moment bound. -/
theorem rounded_actual_meanValue {s k p a X N₀ : ℕ} {C lam : ℝ}
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hp : 0 < p) (hX : p ^ a ≤ X)
    (hN : N₀ ≤ X / p ^ a + 1)
    (hJ : ∀ N : ℕ, N₀ ≤ N → meanValue s k N ≤ C * (N : ℝ) ^ lam) :
    meanValue s k (X / p ^ a + 1) ≤
      (C * (2 : ℝ) ^ lam) * ((X : ℝ) / (p : ℝ) ^ a) ^ lam := by
  have hq := quotient_size_le_two (Nat.pow_pos hp) hX
  have he := Real.rpow_le_rpow (Nat.cast_nonneg (X / p ^ a + 1)) hq hlam
  apply (hJ _ hN).trans ((mul_le_mul_of_nonneg_left he hC).trans_eq _)
  simp only [Nat.cast_pow]
  rw [Real.mul_rpow (by norm_num) (by positivity)]
  ring

/-- One common constant pays the newly proved exponent at all sufficiently large padded quotient scales. -/
theorem exists_improved_rounded_budget (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∀ p a X : ℕ,
      0 < p → p ^ a ≤ X → N₀ ≤ X / p ^ a + 1 →
        meanValue ((u + 1) * k) k (X / p ^ a + 1) ≤
          C * ((X : ℝ) / (p : ℝ) ^ a) ^
            ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) := by
  obtain ⟨C, hC, N₀, hJ⟩ := VinogradovFirstExponent.exists_global_first_exponent k u hk hu
  let lam : ℝ := (((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))
  refine ⟨max 1 (C * (2 : ℝ) ^ lam), le_max_left _ _, N₀, ?_⟩
  intro p a X hp hX hN
  have he := rounded_actual_meanValue hC.le (VinogradovFirstExponent.first_exponent_pos hk hu).le hp hX hN hJ
  exact he.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))


/-- The actual full signed normalized recurrence runs at the independently proved improved exponent, with both homogeneous moment premises discharged. -/
theorem exists_improved_normalized_iteration (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∀ (p a b xi eta X H : ℕ) (hp : p.Prime),
      let _ : Fact p.Prime := ⟨hp⟩
      a < b → 1 ≤ H → k * b - b ≤ 2 * H → p ^ (k * b + H) ≤ X →
      N₀ ≤ X / p ^ (k * b + H) + 1 →
      (C * iterationConstant k u) ^ 2 ≤ (p : ℝ) → eta < p ^ b →
      ∀ colourA colourB : Fin k → Bool,
        VinogradovNonsingularConditioning.conditionedMoment p k a b xi eta X u colourA colourB ≤
          (VinogradovSignedCongruence.colourFactorial colourA : ℝ) * C ^ (1 - 1 / (u : ℝ)) *
            VinogradovCongruencingScaling.momentScale X p k u a b
              ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) *
            (p : ℝ) ^ (-((k : ℝ) * ((k : ℝ) - 1) / 2 - 1 / (3 * (k : ℝ))) * ((b : ℝ) - a)) *
            conditioningAllowance p k b (k * b) eta X u H colourB
              ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) ^ (1 / (u : ℝ)) := by
  obtain ⟨C, hC, N₀, hbudget⟩ := exists_improved_rounded_budget k u hk hu
  refine ⟨C, hC, N₀, ?_⟩
  intro p a b xi eta X H hp
  let : Fact p.Prime := ⟨hp⟩
  dsimp only
  intro hab hH hgap hX hN hcost heta colourA colourB
  have hpow : p ^ b ≤ p ^ (k * b + H) := Nat.pow_le_pow_right hp.one_lt.le (by nlinarith)
  have hquot : X / p ^ (k * b + H) ≤ X / p ^ b :=
    (Nat.le_div_iff_mul_le (Nat.pow_pos hp.pos)).mpr
      ((Nat.mul_le_mul_left _ hpow).trans (Nat.div_mul_le_self X (p ^ (k * b + H))))
  have hJ := hbudget p b X hp.pos (hpow.trans hX) (by omega)
  have hJdeep := hbudget p (k * b + H) X hp.pos hX hN
  have hX0 : 0 < X := (Nat.pow_pos hp.pos).trans_le hX
  have he := normalized_iteration_of_scaled_bounds (xi := xi) hk hu hab hH hgap hX0 hC
    (first_exponent_ge_critical hk) hcost hJ hJdeep heta colourA colourB
  have hdefect : ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) -
      2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 =
        (k : ℝ) * ((k : ℝ) - 1) / 2 - 1 / (3 * (k : ℝ)) := by
    push_cast
    ring
  simpa only [hdefect] using he


/-- Discharge both actual homogeneous moment estimates in the complete mixed-moment recurrence at the improved exponent. -/
theorem exists_improved_mixed_iteration (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∀ (p a b xi X H : ℕ) [NeZero p],
      a ≤ b → 1 ≤ H → b - a ≤ 2 * H → p ^ (b + H) ≤ X →
      N₀ ≤ X / p ^ (b + H) + 1 →
      (C * iterationConstant k u) ^ 2 ≤ (p : ℝ) → ∀ colour : Fin k → Bool,
        VinogradovConditioningRemainder.levelMixedMaximum p k a b xi X u colour ≤
          VinogradovCongruencingScaling.momentScale X p k u a b
            ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) *
          conditioningAllowance p k a b xi X u H colour
            ((((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))) := by
  obtain ⟨C, hC, N₀, hbudget⟩ := exists_improved_rounded_budget k u hk hu
  refine ⟨C, hC, N₀, ?_⟩
  intro p a b xi X H inst hab hH hgap hX hN hp colour
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hpow : p ^ a ≤ p ^ (b + H) := Nat.pow_le_pow_right (by omega) (by omega)
  have hquot : X / p ^ (b + H) ≤ X / p ^ a :=
    (Nat.le_div_iff_mul_le (Nat.pow_pos hp0)).mpr
      ((Nat.mul_le_mul_left _ hpow).trans (Nat.div_mul_le_self X (p ^ (b + H))))
  have hJa := hbudget p a X hp0 (hpow.trans hX) (by omega)
  have hJb := hbudget p (b + H) X hp0 hX hN
  exact mixed_le_scale_allowance_of_scaled_bounds hk hu hab hH hgap
    ((Nat.pow_pos hp0).trans_le hX) hC (first_exponent_ge_critical hk) hp hJa hJb colour

open VinogradovCongruencingScaling

/-- Lowering the moment exponent changes the source scale by the exact coarse-quotient power. -/
theorem moment_scale_exponent_shift {x P : ℝ} (hx : 0 < x) (hP : 0 < P)
    (k u a b lam eps : ℝ) :
    momentScale x P k u a b (lam - eps) =
      momentScale x P k u a b lam * (x / P ^ a) ^ (-eps) := by
  unfold momentScale
  have hq : 0 < x / P ^ a := by positivity
  have he : lam - eps - 2 * k * u = (lam - 2 * k * u) + -eps := by ring
  rw [he, Real.rpow_add hq]
  ring

/-- The full unnormalized allowance changes only in its deep remainder: every actual intermediate energy is unchanged. -/
theorem allowance_exponent_shift_identity {p k a b xi X u H : ℕ} [NeZero p]
    (hX : 0 < X) (colour : Fin k → Bool) (lam eps : ℝ) :
    momentScale X p k u a b (lam - eps) *
        conditioningAllowance p k a b xi X u H colour (lam - eps) +
      momentScale X p k u a b lam *
        (1 - ((X : ℝ) / (p : ℝ) ^ a) ^ (-eps)) * (p : ℝ) ^ (-((H : ℝ) / 2)) =
      momentScale X p k u a b lam *
        conditioningAllowance p k a b xi X u H colour lam := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  rw [allowance_scale_identity hX, allowance_scale_identity hX,
    moment_scale_exponent_shift hX0 hp0]
  simp only [Real.rpow_natCast]
  ring

/-- With a complete coarse window, a lower exponent gives a no-larger full allowance after restoring its actual scale. -/
theorem scaled_allowance_exponent_mono {p k a b xi X u H : ℕ} [NeZero p]
    (hX : p ^ a ≤ X) (colour : Fin k → Bool) (lam : ℝ) {eps : ℝ} (heps : 0 ≤ eps) :
    momentScale X p k u a b (lam - eps) *
        conditioningAllowance p k a b xi X u H colour (lam - eps) ≤
      momentScale X p k u a b lam *
        conditioningAllowance p k a b xi X u H colour lam := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hX0 : 0 < X := (Nat.pos_of_ne_zero (NeZero.ne (p ^ a))).trans_le hX
  have hq : 1 ≤ (X : ℝ) / (p : ℝ) ^ a := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (p : ℝ) ^ a)).mpr
    simpa only [one_mul, Nat.cast_pow] using (show ((p ^ a : ℕ) : ℝ) ≤ X by exact_mod_cast hX)
  have hc : 0 ≤ 1 - ((X : ℝ) / (p : ℝ) ^ a) ^ (-eps) :=
    sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos hq (by linarith))
  have hid := allowance_exponent_shift_identity (p := p) (a := a) (b := b)
    (xi := xi) (u := u) (H := H) hX0 colour lam eps
  have hcorr : 0 ≤ momentScale X p k u a b lam *
      (1 - ((X : ℝ) / (p : ℝ) ^ a) ^ (-eps)) * (p : ℝ) ^ (-((H : ℝ) / 2)) :=
    mul_nonneg (mul_nonneg (momentScale_pos (by exact_mod_cast hX0) hp0 _ _ _ _ _).le hc)
      (Real.rpow_nonneg hp0.le _)
  linarith

end
end RiemannGaussian.VinogradovImprovedNormalization
