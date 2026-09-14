/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovInitialIteration

/-!
# A first independent saving for the full global mean value

The actual elementary quotient moment has an exact source-scale defect.
At coarse level zero the congruencing gain exceeds that cost, leaving
k(k-1)(u-1)/(2(u+1))>=1/3 for k,u>=2. This bounds the entire residue and
colour maximum, then the full depth-one allowance by a fixed constant
times p^(-1/3). Initial global conditioning yields the same independent
saving for J_((u+1)k,k)(X), with every prime threshold and cutoff explicit.

No upper moment budget is assumed. The conversion to an improved exponent
at every sufficiently large endpoint is in `VinogradovFirstExponent`.
The critical high-moment exponent and VK zeta-growth argument remain open.
-/

namespace RiemannGaussian.VinogradovInitialSaving
noncomputable section
open scoped Classical BigOperators
open VinogradovMeanValue VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovNormalizedIteration VinogradovCongruencingScaling VinogradovNonsingularConditioning
open VinogradovRemainderScaling VinogradovIteratedCongruencing

/-- The elementary two-scale moment cost has an exact explicit defect from the source scale. -/
theorem elementary_mixed_scale_identity {x P : ℝ} (hx : 0 < x) (hP : 0 < P)
    (k u a b : ℝ) (hu : u + 1 ≠ 0) :
    (x / P ^ a) ^ (k * (2 * u + 1) / (u + 1)) *
      (x / P ^ b) ^ (k * (2 * u + 1) * u / (u + 1)) =
        momentScale x P k u a b (k * (2 * u + 1)) *
          P ^ (k * u / (u + 1) * (b - a)) := by
  unfold momentScale
  simp_rw [quotient_power_exp hx hP]
  simp only [Real.rpow_def_of_pos hP, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- The actual elementary level bound retains the precise power cost at every scale pair. -/
theorem elementary_level_le_scaled {p k a b xi X u : ℕ} [NeZero p]
    (hu : 0 < u) (hXa : p ^ a ≤ X) (hXb : p ^ b ≤ X) (colour : Fin k → Bool) :
    levelMixedMaximum p k a b xi X u colour ≤
      elementaryConstant k u * momentScale X p k u a b (((k * (2 * u + 1) : ℕ) : ℝ)) *
        (p : ℝ) ^ ((k : ℝ) * u / ((u : ℝ) + 1) * ((b : ℝ) - a)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hX0 : (0 : ℝ) < X := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne (p ^ a))).trans_le hXa
  have he := elementary_mixed_scale_identity hX0 hp0 (k : ℝ) (u : ℝ) (a : ℝ) (b : ℝ)
    (by positivity)
  have hb := level_mixed_le_rounded (xi := xi) hu hXa hXb colour
  push_cast at hb ⊢
  simp only [Real.rpow_natCast] at he
  rw [he] at hb
  simpa only [mul_assoc] using hb

/-- At the initial coarse scale, congruencing beats the remaining elementary quotient cost. -/
theorem conditioned_initial_elementary_saving {p k b xi eta X u : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hu : 2 ≤ u) (hkp : k < p) (hb : 0 < b)
    (hX : p ^ (k * b) ≤ X) (heta : eta < p ^ b) (colourA colourB : Fin k → Bool) :
    conditionedMoment p k 0 b xi eta X u colourA colourB ≤
      (VinogradovSignedCongruence.colourFactorial colourA : ℝ) * elementaryConstant k u *
        momentScale X p k u 0 b (((k * (2 * u + 1) : ℕ) : ℝ)) *
          (p : ℝ) ^ (-((k : ℝ) * ((k : ℝ) - 1) * ((u : ℝ) - 1) /
            (2 * ((u : ℝ) + 1))) * b) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.Prime.pos (Fact.out : p.Prime)
  have hX0 : 0 < X := (Nat.pos_of_ne_zero (NeZero.ne (p ^ (k * b)))).trans_le hX
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hkb : b ≤ k * b := by nlinarith
  have hXb : p ^ b ≤ X := (Nat.pow_le_pow_right (by omega : 1 ≤ p) hkb).trans hX
  have hJ := higher_meanValue_rounded (k := k) (u := u) hXb
  have hI := elementary_level_le_scaled (xi := eta) (by omega : 0 < u) hXb hX colourB
  have hC : 0 < elementaryConstant k u := lt_of_lt_of_le zero_lt_one (elementaryConstant_one_le k u)
  let T : ℝ := (k : ℝ) * u / ((u : ℝ) + 1) * ((k * b : ℕ) - b)
  have hbound := normalized_congruencing_transfer (a := 0) (xi := xi) (u := u) (X := X)
    (lam := (((k * (2 * u + 1) : ℕ) : ℝ)))
    (R := elementaryConstant k u * (p : ℝ) ^ T)
    hkp (by omega) hb (by omega) hX0 heta colourA colourB hC.le (by positivity)
    (by simpa only [Real.rpow_natCast] using hJ)
    (by simpa only [T, Nat.cast_mul, mul_left_comm, mul_assoc, mul_comm] using hI)
  apply hbound.trans_eq
  have hdefect : ((k * (2 * u + 1) : ℕ) : ℝ) - 2 * (k : ℝ) * ((u : ℝ) + 1) +
      (k : ℝ) * ((k : ℝ) + 1) / 2 = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    push_cast
    ring
  simp only [hdefect, Nat.cast_zero, sub_zero]
  rw [Real.mul_rpow hC.le (by positivity), ← Real.rpow_mul hp0.le]
  have hCmerge : elementaryConstant k u ^ (1 - 1 / (u : ℝ)) *
      elementaryConstant k u ^ (1 / (u : ℝ)) = elementaryConstant k u := by
    rw [← Real.rpow_add hC]
    simp
  have hPmerge : (p : ℝ) ^ (-((k : ℝ) * ((k : ℝ) - 1) / 2) * b) *
      (p : ℝ) ^ (T * (1 / (u : ℝ))) =
      (p : ℝ) ^ (-((k : ℝ) * ((k : ℝ) - 1) * ((u : ℝ) - 1) /
        (2 * ((u : ℝ) + 1))) * b) := by
    rw [← Real.rpow_add hp0]
    congr 1
    unfold T
    push_cast
    field_simp
    ring
  calc
    _ = (VinogradovSignedCongruence.colourFactorial colourA : ℝ) *
      (elementaryConstant k u ^ (1 - 1 / (u : ℝ)) * elementaryConstant k u ^ (1 / (u : ℝ))) *
      momentScale X p k u 0 b (((k * (2 * u + 1) : ℕ) : ℝ)) *
      ((p : ℝ) ^ (-((k : ℝ) * ((k : ℝ) - 1) / 2) * b) *
        (p : ℝ) ^ (T * (1 / (u : ℝ)))) := by ring
    _ = _ := by rw [hCmerge, hPmerge]


/-- The net congruencing exponent is uniformly at least one third from degree and order two onward. -/
theorem saving_exponent_one_third {k u : ℝ} (hk : 2 ≤ k) (hu : 2 ≤ u) :
    (1 / 3 : ℝ) ≤ k * (k - 1) * (u - 1) / (2 * (u + 1)) := by
  apply (le_div_iff₀ (by linarith : 0 < 2 * (u + 1))).mpr
  have hkk : 2 ≤ k * (k - 1) := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hkk (show 0 ≤ u - 1 by linarith)
  nlinarith

/-- The complete actual residue and colour maximum receives the uniform initial one-third saving. -/
theorem initial_level_saving {p k xi X u : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hu : 2 ≤ u) (hkp : k < p) (hX : p ^ k ≤ X)
    (colour : Fin k → Bool) :
    levelConditionedMaximum p k 0 1 xi X u colour ≤
      (VinogradovSignedCongruence.colourFactorial colour : ℝ) * elementaryConstant k u *
        momentScale X p k u 0 1 (((k * (2 * u + 1) : ℕ) : ℝ)) *
          (p : ℝ) ^ (-1 / 3 : ℝ) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.Prime.one_lt (Fact.out : p.Prime)).le
  have hexp := saving_exponent_one_third (k := (k : ℝ)) (u := (u : ℝ)) (by exact_mod_cast hk) (by exact_mod_cast hu)
  unfold levelConditionedMaximum
  apply Finset.sup'_le Finset.univ_nonempty
  intro c hc
  unfold conditionedMaximum
  apply Finset.sup'_le Finset.univ_nonempty
  intro colourB hcolourB
  have he := conditioned_initial_elementary_saving (b := 1) (xi := xi) hk hu hkp (by norm_num)
    (by simpa only [mul_one] using hX) c.isLt colour colourB
  simp only [Nat.cast_one, mul_one] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hp1 (by linarith))
  unfold momentScale elementaryConstant
  positivity

/-- The full finite allowance at depth one has an independently proved one-third saving. -/
theorem initial_allowance_saving {p k xi X u : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hu : 2 ≤ u) (hkp : k < p) (hX : p ^ k ≤ X)
    (colour : Fin k → Bool) :
    conditioningAllowance p k 0 1 xi X u 1 colour (((k * (2 * u + 1) : ℕ) : ℝ)) ≤
      (1 + selectionCost k u * (VinogradovSignedCongruence.colourFactorial colour : ℝ) *
        elementaryConstant k u) * (p : ℝ) ^ (-1 / 3 : ℝ) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.Prime.pos (Fact.out : p.Prime)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.Prime.one_lt (Fact.out : p.Prime)).le
  have hX0 : (0 : ℝ) < X := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne (p ^ k))).trans_le hX
  have hscale := momentScale_pos hX0 hp0 (k : ℝ) (u : ℝ) 0 1
    (((k * (2 * u + 1) : ℕ) : ℝ))
  have hlevel := initial_level_saving (xi := xi) hk hu hkp hX colour
  have hn : normalizedLevel p k 0 1 xi X u colour (((k * (2 * u + 1) : ℕ) : ℝ)) ≤
      (VinogradovSignedCongruence.colourFactorial colour : ℝ) * elementaryConstant k u *
        (p : ℝ) ^ (-1 / 3 : ℝ) := by
    unfold normalizedLevel
    simp only [Nat.cast_zero, Nat.cast_one]
    apply (div_le_iff₀ hscale).mpr
    exact hlevel.trans_eq (by ring)
  unfold conditioningAllowance
  simp only [Finset.sum_range_one, pow_zero, Nat.cast_zero, mul_zero,
    Real.rpow_zero, one_mul, add_zero, Nat.cast_one]
  calc
    _ ≤ (p : ℝ) ^ (-1 / 3 : ℝ) + selectionCost k u *
      ((VinogradovSignedCongruence.colourFactorial colour : ℝ) * elementaryConstant k u *
        (p : ℝ) ^ (-1 / 3 : ℝ)) :=
      add_le_add (Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num))
        (mul_le_mul_of_nonneg_left hn (by unfold selectionCost; positivity))
    _ = _ := by ring

/-- All fixed costs in the first global moment saving. -/
def firstSavingConstant (k u : ℕ) : ℝ :=
  1 + selectionCost k u * (VinogradovSignedCongruence.colourFactorial (fun _ : Fin k => true) : ℝ) *
    elementaryConstant k u

/-- The full original Vinogradov mean value has an independent prime-scale power saving, with all moment premises discharged. -/
theorem global_meanValue_first_saving (M R k u X : ℕ)
    (hk : 2 ≤ k) (hu : k ≤ u) (hM : 0 < M) (hR : 0 < R)
    (hbudget : X ^ (k * (k - 1)) < M ^ R) (hsize : 4 * k ^ 4 ≤ X)
    (hcutoff : (2 ^ R * M) ^ k ≤ X)
    (hprime : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (M : ℝ)) :
    meanValue ((u + 1) * k) k X ≤
      (2 * (R : ℝ)) ^ 2 * firstSavingConstant k u *
        (X : ℝ) ^ (k * (2 * u + 1)) * (M : ℝ) ^ (-1 / 3 : ℝ) := by
  have hcutoff' : (2 ^ R * M) ^ (1 + 1) ≤ X :=
    (Nat.pow_le_pow_right (Nat.succ_le_of_lt (by positivity : 0 < 2 ^ R * M)) hk).trans hcutoff
  obtain ⟨p, hp, hMp, hpM, hglobal⟩ :=
    VinogradovInitialIteration.exists_initial_finite_iteration M R k u 1 X
      hk hu (by norm_num) hM hR hbudget hsize hcutoff' hprime
  let : Fact p.Prime := ⟨hp⟩
  have hpbudget : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (p : ℝ) :=
    hprime.trans (by exact_mod_cast hMp.le)
  have hkp := degree_lt_of_budget hk hu (elementaryConstant_one_le k u) hpbudget
  have hX : p ^ k ≤ X := (Nat.pow_le_pow_left hpM _).trans hcutoff
  have hallow := initial_allowance_saving (xi := 0) hk (hk.trans hu) hkp hX (fun _ => true)
  change _ ≤ firstSavingConstant k u * (p : ℝ) ^ (-1 / 3 : ℝ) at hallow
  have he := hglobal.trans (mul_le_mul_of_nonneg_left hallow (by positivity))
  have hP : (p : ℝ) ^ (-1 / 3 : ℝ) ≤ (M : ℝ) ^ (-1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hM) (by exact_mod_cast hMp.le) (by norm_num)
  calc
    _ ≤ _ := he
    _ = (2 * (R : ℝ)) ^ 2 * firstSavingConstant k u *
        (X : ℝ) ^ (k * (2 * u + 1)) * (p : ℝ) ^ (-1 / 3 : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hP (by unfold firstSavingConstant selectionCost elementaryConstant; positivity)

end
end RiemannGaussian.VinogradovInitialSaving
