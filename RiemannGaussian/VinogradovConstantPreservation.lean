/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovDefectRemainder

/-!
# Linear homogeneous constants through the complete conditioning allowance

Only the iteration cost is absorbed into the prime threshold. The original
homogeneous constant multiplies the deep remainder and survives every actual
conditioned energy with exact linear dependence. Full intermediate levels,
residues and colours remain. The sharper exponent-defect theorem stays
upstream of the named half-depth relaxation used by the present iteration.
-/

namespace RiemannGaussian.VinogradovConstantPreservation
noncomputable section
open scoped BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovRemainderScaling
open VinogradovConditioningPowerSaving VinogradovSingularConditioning
open VinogradovNormalizedIteration VinogradovCongruencingScaling
open VinogradovNonsingularConditioning VinogradovProfileIteration
open VinogradovFirstExponent VinogradovExponentBootstrap
open VinogradovDefectRemainder

/-- Transfer an admissible real exponent and two explicit actual moment bounds to the deeper remainder; the final specialization discharges these bounds. -/
theorem deep_remainder_preserving_constant {p k a b xi X u H : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b) (hH : 1 ≤ H) (hgap : b - a ≤ 2 * H)
    (hX : 0 < X) {C lam : ℝ} (hC : 1 ≤ C)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam)
    (hbudget : iterationConstant k u ^ 2 ≤ (p : ℝ))
    (hA : meanValue ((u + 1) * k) k (X / p ^ a + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ a) ^ lam)
    (hB : meanValue ((u + 1) * k) k (X / p ^ (b + H) + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ lam)
    (colour : Fin k → Bool) :
    singularCost p k u ^ H * levelMixedMaximum p k a (b + H) xi X u colour ≤
      C * ((((X : ℝ) / (p : ℝ) ^ a) ^ (lam - 2 * (k : ℝ) * u) *
        ((X : ℝ) / (p : ℝ) ^ b) ^ (2 * (k * u))) * (p : ℝ) ^ (-((H : ℝ) / 2))) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hd : 0 ≤ lam - (2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2) := by linarith
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hsep : 0 ≤ (b : ℝ) - (a : ℝ) + H := by linarith only [habR, Nat.cast_nonneg (α := ℝ) H]
  have hu0 : (0 : ℝ) < u + 1 := by positivity
  have hextra : 0 ≤ (lam - (2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2)) *
      (u : ℝ) / ((u : ℝ) + 1) * ((b : ℝ) - (a : ℝ) + H) := by positivity
  have h := VinogradovDefectRemainder.deep_remainder_preserving_defect (xi := xi)
    hk hu hH hgap hX hC hbudget hA hB colour
  dsimp only at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le hp1 (by linarith only [hextra])

/-- The original finite allowance retaining the actual homogeneous constant
in its deep remainder and every unscaled intermediate energy. -/
def constantAllowance (C : ℝ) (p k a b xi X u H : ℕ) [NeZero p]
    (colour : Fin k → Bool) (lam : ℝ) : ℝ :=
  C * (p : ℝ) ^ (-((H : ℝ) / 2)) + selectionCost k u * ∑ h ∈ Finset.range H,
    singularCost p k u ^ h * (p : ℝ) ^ (-2 * (k : ℝ) * u * h) *
      normalizedLevel p k a (b + h) xi X u colour lam

/-- Retaining the constant changes exactly the deep term, with all
intermediate energies identical. -/
theorem constantAllowance_eq_old (C : ℝ) (p k a b xi X u H : ℕ) [NeZero p]
    (colour : Fin k → Bool) (lam : ℝ) :
    constantAllowance C p k a b xi X u H colour lam =
      conditioningAllowance p k a b xi X u H colour lam +
        (C - 1) * (p : ℝ) ^ (-((H : ℝ) / 2)) := by
  unfold constantAllowance conditioningAllowance
  ring

/-- The retained allowance is nonnegative for every admissible source constant. -/
theorem constantAllowance_nonneg {C : ℝ} (hC : 1 ≤ C)
    {p k a b xi X u H : ℕ} [NeZero p] (hX : 0 < X)
    (colour : Fin k → Bool) (lam : ℝ) :
    0 ≤ constantAllowance C p k a b xi X u H colour lam := by
  rw [constantAllowance_eq_old]
  exact add_nonneg (allowance_nonneg hX colour lam)
    (mul_nonneg (sub_nonneg.mpr hC) (by positivity))

/-- Exact source normalization preserves the actual constant and all finite
intermediate levels before any profile estimate. -/
theorem constantAllowance_scale_identity {p k a b xi X u H : ℕ} [NeZero p]
    (hX : 0 < X) (C : ℝ) (colour : Fin k → Bool) (lam : ℝ) :
    momentScale X p k u a b lam * constantAllowance C p k a b xi X u H colour lam =
      C * (momentScale X p k u a b lam * (p : ℝ) ^ (-((H : ℝ) / 2))) +
      selectionCost k u * ∑ h ∈ Finset.range H,
        singularCost p k u ^ h * levelConditionedMaximum p k a (b + h) xi X u colour := by
  rw [constantAllowance_eq_old, mul_add, allowance_scale_identity hX]
  ring

/-- Retain two explicitly stated sharper homogeneous estimates through the complete finite conditioning remainder; their truth is not asserted here. -/
theorem mixed_le_constant_allowance {p k a b xi X u H : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b) (hH : 1 ≤ H)
    (hgap : b - a ≤ 2 * H) (hX : 0 < X) {C lam : ℝ} (hC : 1 ≤ C)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam)
    (hp : iterationConstant k u ^ 2 ≤ (p : ℝ))
    (hA : meanValue ((u + 1) * k) k (X / p ^ a + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ a) ^ lam)
    (hB : meanValue ((u + 1) * k) k (X / p ^ (b + H) + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ lam)
    (colour : Fin k → Bool) :
    levelMixedMaximum p k a b xi X u colour ≤
      momentScale X p k u a b lam * constantAllowance C p k a b xi X u H colour lam := by
  have hkp := (degree_lt_of_budget hk hu (C := 1) le_rfl (by simpa only [one_mul] using hp)).le
  rw [constantAllowance_scale_identity hX]
  apply (finite_conditioning_iteration hkp (by omega) (by omega) colour b H).trans
  apply add_le_add _ (le_refl _)
  have he := deep_remainder_preserving_constant (xi := xi) hk hu hab hH hgap hX hC hlam hp hA hB colour
  simpa only [momentScale, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using he

/-- Two explicit actual homogeneous estimates suffice for the complete finite normalized recurrence at any exponent in the critical range. -/
theorem normalized_iteration_preserving_constant {p k a b xi eta X u H : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a < b) (hH : 1 ≤ H)
    (hgap : k * b - b ≤ 2 * H) (hX : 0 < X) {C lam : ℝ} (hC : 1 ≤ C)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam)
    (hp : iterationConstant k u ^ 2 ≤ (p : ℝ))
    (hA : meanValue ((u + 1) * k) k (X / p ^ b + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ b) ^ lam)
    (hB : meanValue ((u + 1) * k) k (X / p ^ (k * b + H) + 1) ≤
      C * ((X : ℝ) / (p : ℝ) ^ (k * b + H)) ^ lam)
    (heta : eta < p ^ b) (colourA colourB : Fin k → Bool) :
    conditionedMoment p k a b xi eta X u colourA colourB ≤
      (VinogradovSignedCongruence.colourFactorial colourA : ℝ) *
        C ^ (1 - 1 / (u : ℝ)) * momentScale X p k u a b lam *
        (p : ℝ) ^ (-(lam - 2 * (k : ℝ) * ((u : ℝ) + 1) +
          (k : ℝ) * ((k : ℝ) + 1) / 2) * ((b : ℝ) - a)) *
        constantAllowance C p k b (k * b) eta X u H colourB lam ^ (1 / (u : ℝ)) := by
  have hkp := degree_lt_of_budget hk hu (C := 1) le_rfl (by simpa only [one_mul] using hp)
  have hbk : b ≤ k * b := by nlinarith
  have hI := mixed_le_constant_allowance (xi := eta) hk hu hbk hH hgap hX hC hlam hp hA hB colourB
  exact normalized_congruencing_transfer (xi := xi)
    (R := constantAllowance C p k b (k * b) eta X u H colourB lam)
    hkp (by omega) hab (by omega) hX heta colourA colourB
    (le_trans zero_le_one hC) (constantAllowance_nonneg hC hX colourB _) hA
    (by simpa only [Nat.cast_mul] using hI)

/-- The whole retained allowance has a profile bound with the actual source
constant in its deep contribution and no factor proportional to depth. -/
theorem constantAllowance_le_profile {p k b eta X u H : ℕ} [NeZero p]
    {C B delta beta lam : ℝ} (hC : 1 ≤ C) (hB : 0 ≤ B)
    (hratio : singularCost p k u * (p : ℝ) ^ (beta - 2 * (k : ℝ) * u) ≤ 1 / 2)
    (hdeep : -((H : ℝ) / 2) ≤ (delta + (k : ℝ) * beta) * b)
    (colour : Fin k → Bool)
    (hnext : ∀ h < H, normalizedLevel p k b (k * b + h) eta X u colour lam ≤
      B * (p : ℝ) ^ (delta * b + beta * ((k * b + h : ℕ) : ℝ))) :
    constantAllowance C p k b (k * b) eta X u H colour lam ≤
      (C + 2 * selectionCost k u * B) * (p : ℝ) ^ ((delta + (k : ℝ) * beta) * b) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have h := allowance_le_profile hB hratio hdeep colour hnext
  rw [constantAllowance_eq_old]
  have hd := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hp1 hdeep) (sub_nonneg.mpr hC)
  apply (add_le_add h hd).trans_eq
  ring

/-- The full original signed recurrence improves any admissible uniform next-level profile, retaining its actual colour factor. -/
theorem conditioned_profile_preserving_constant {p k a b xi eta X u H : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a < b) (hH : 1 ≤ H)
    (hgap : k * b - b ≤ 2 * H) (hX : 0 < X) {C B lam beta : ℝ} (hC : 1 ≤ C) (hB : 0 ≤ B)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam)
    (hbudget : iterationConstant k u ^ 2 ≤ (p : ℝ))
    (hJa : meanValue ((u + 1) * k) k (X / p ^ b + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ b) ^ lam)
    (hJdeep : meanValue ((u + 1) * k) k (X / p ^ (k * b + H) + 1) ≤
      C * ((X : ℝ) / (p : ℝ) ^ (k * b + H)) ^ lam)
    (heta : eta < p ^ b) (colourA colourB : Fin k → Bool)
    (hbeta : beta ≤ (k : ℝ) * u)
    (hdeep : -((H : ℝ) / 2) ≤
      (lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2 + (k : ℝ) * beta) * b)
    (hnext : ∀ h < H, normalizedLevel p k b (k * b + h) eta X u colourB lam ≤
      B * (p : ℝ) ^ ((lam - 2 * (k : ℝ) * ((u : ℝ) + 1) +
        (k : ℝ) * ((k : ℝ) + 1) / 2) * b + beta * ((k * b + h : ℕ) : ℝ))) :
    let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
    conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
      ((VinogradovSignedCongruence.colourFactorial colourA : ℝ) * C ^ (1 - 1 / (u : ℝ)) *
        (C + 2 * selectionCost k u * B) ^ (1 / (u : ℝ))) *
        (p : ℝ) ^ (delta * a + (-(1 - 1 / (u : ℝ)) * delta + (k : ℝ) / u * beta) * b) := by
  let delta := lam - 2 * (k : ℝ) * ((u : ℝ) + 1) + (k : ℝ) * ((k : ℝ) + 1) / 2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.Prime.pos (Fact.out : p.Prime)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hM := momentScale_pos hX0 hp0 (k : ℝ) (u : ℝ) (a : ℝ) (b : ℝ) lam
  have hi := normalized_iteration_preserving_constant (xi := xi) hk hu hab hH hgap hX hC hlam
    hbudget hJa hJdeep heta colourA colourB
  have hallow := constantAllowance_le_profile (delta := delta) hC hB
    (profile_ratio_le_half hk hu (C := 1) le_rfl (by simpa only [one_mul] using hbudget) hbeta) hdeep colourB hnext
  have hcoeff : 0 ≤ (C + 2 * selectionCost k u * B) := by unfold selectionCost; positivity
  have hscale := profile_exponent_identity hp0 (u := (u : ℝ))
    (by exact_mod_cast (by omega : u ≠ 0)) (a : ℝ) (b : ℝ) (k : ℝ) delta beta
  apply (div_le_iff₀ hM).mpr
  have hbound := hi.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (constantAllowance_nonneg hC hX colourB lam) hallow (by positivity))
    (by unfold momentScale; positivity))
  apply hbound.trans_eq
  rw [Real.mul_rpow hcoeff (by positivity)]
  change _ = ((VinogradovSignedCongruence.colourFactorial colourA : ℝ) * C ^ (1 - 1 / (u : ℝ)) *
    (C + 2 * selectionCost k u * B) ^ (1 / (u : ℝ))) *
    (p : ℝ) ^ (delta * a + (-(1 - 1 / (u : ℝ)) * delta + (k : ℝ) / u * beta) * b) *
      momentScale X p k u a b lam
  calc
    _ = ((VinogradovSignedCongruence.colourFactorial colourA : ℝ) * C ^ (1 - 1 / (u : ℝ)) *
        (C + 2 * selectionCost k u * B) ^ (1 / (u : ℝ))) *
      ((p : ℝ) ^ (-delta * ((b : ℝ) - a)) *
        ((p : ℝ) ^ ((delta + (k : ℝ) * beta) * b)) ^ (1 / (u : ℝ))) *
      momentScale X p k u a b lam := by ring
    _ = _ := by rw [hscale]

/-- The two Holder powers retain exact linear dependence on the original
positive moment constant when the next profile has that same dependence. -/
theorem profile_constant_homogeneity {C Q : ℝ} (hC : 0 < C) (hQ : 0 ≤ Q) (theta : ℝ) :
    C ^ (1 - theta) * (C * Q) ^ theta = C * Q ^ theta := by
  rw [Real.mul_rpow hC.le hQ, ← mul_assoc, ← Real.rpow_add hC]
  rw [show 1 - theta + theta = 1 by ring, Real.rpow_one]

end
end RiemannGaussian.VinogradovConstantPreservation
