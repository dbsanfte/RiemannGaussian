/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovIteratedCongruencing
import RiemannGaussian.VinogradovCongruencingScaling

/-!
# A normalized finite recurrence for actual signed conditioned moments

The full original intermediate sum is normalized by an exact identity.
The general recurrence retains its two explicitly required homogeneous
estimates at the coarse and deepest quotient endpoints. The final theorem
supplies both estimates at the proved elementary exponent k(2u+1), with
rounding, all iteration constants and finite cutoff conditions paid.

Both block colours and the actual conditioned energies survive. The full
sum remains upstream of its explicit geometric upper bound; no arbitrary
moment budget occurs in the specialized terminal theorems. This is the
finite normalized mechanism underlying Wooley (2012), Lemma 6.3, with
explicit constants and the elementary starting exponent. The critical moment
exponent, full iteration and VK zeta growth are not proved here. A first
global exponent improvement is proved in `VinogradovFirstExponent`. The initial
global entry is proved in `VinogradovInitialConditioning` and connected to
this finite recurrence in `VinogradovInitialIteration`. The original weighted Riesz moments
remain distinct from these unweighted conditioned moments.
https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf
-/

namespace RiemannGaussian.VinogradovNormalizedIteration
noncomputable section
open UnitAddTorus MeasureTheory
open VinogradovMeanValue VinogradovNonsingularConditioning
open VinogradovConditioningRemainder VinogradovConditioningPowerSaving
open VinogradovCongruencingStep
/-- The original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
open VinogradovIteratedCongruencing VinogradovCongruencingScaling

/-- A stated actual next-moment bound gives the exact normalized defect factor; the hypothesis is kept visible for later discharge. -/
theorem normalized_congruencing_transfer {p k a b xi eta X u : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (hu : 0 < u) (hX : 0 < X)
    (heta : eta < p ^ b) (colourA colourB : Fin k → Bool)
    {C lam R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hJ : meanValue ((u + 1) * k) k (X / p ^ b + 1) ≤
      C * ((X : ℝ) / (p : ℝ) ^ b) ^ lam)
    (hI : levelMixedMaximum p k b (k * b) eta X u colourB ≤
      momentScale X p k u b (k * b) lam * R) :
    conditionedMoment p k a b xi eta X u colourA colourB ≤
      (VinogradovSignedCongruence.colourFactorial colourA : ℝ) *
        C ^ (1 - 1 / (u : ℝ)) * momentScale X p k u a b lam *
        (p : ℝ) ^ (-(lam - 2 * (k : ℝ) * ((u : ℝ) + 1) +
          (k : ℝ) * ((k : ℝ) + 1) / 2) * ((b : ℝ) - a)) * R ^ (1 / (u : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.Prime.pos (Fact.out : p.Prime)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hu1 : (1 : ℝ) ≤ u := by exact_mod_cast hu
  have ht : 0 ≤ 1 - 1 / (u : ℝ) := by
    have h := (div_le_one hu0).mpr hu1
    linarith
  have hM := momentScale_pos hX0 hp0 (k : ℝ) (u : ℝ) (b : ℝ) ((k : ℝ) * b) lam
  have he := conditioned_le_level_mixed (xi := xi) (X := X) hkp hk hab hu heta colourA colourB
  apply he.trans
  calc
    _ ≤ stepCost p k a b colourA *
        ((C * ((X : ℝ) / (p : ℝ) ^ b) ^ lam) ^ (1 - 1 / (u : ℝ)) *
         (momentScale X p k u b (k * b) lam * R) ^ (1 / (u : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by unfold stepCost; positivity)
      apply mul_le_mul
      · exact Real.rpow_le_rpow (by rw [meanValue_eq_count]; positivity) hJ ht
      · exact Real.rpow_le_rpow (level_mixed_nonneg colourB) hI (by positivity)
      · exact Real.rpow_nonneg (level_mixed_nonneg colourB) _
      · positivity
    _ = _ := by
      rw [stepCost_eq_power (by omega) hab.le colourA,
        Real.mul_rpow hC (by positivity), ← Real.rpow_mul (by positivity),
        Real.mul_rpow hM.le hR]
      have hscale := congruencing_scale_identity (k := (k : ℝ)) (a := (a : ℝ))
        (b := (b : ℝ)) (lam := lam) hX0 hp0 hu0.ne'
      simp only [Real.rpow_natCast] at hscale
      calc
        _ = ((VinogradovSignedCongruence.colourFactorial colourA : ℝ) * C ^ (1 - 1 / (u : ℝ))) *
          ((p : ℝ) ^ (((a : ℝ) + b) * ((k : ℝ) * ((k : ℝ) - 1) / 2) + (k : ℝ) * ((k : ℝ) * b - a)) *
            ((X : ℝ) / (p : ℝ) ^ b) ^ (lam * (1 - 1 / (u : ℝ))) *
            momentScale X p k u b (k * b) lam ^ (1 / (u : ℝ))) * R ^ (1 / (u : ℝ)) := by ring
        _ = _ := by rw [hscale]; ring

/-- The actual conditioned level at an explicit source normalization. -/
def normalizedLevel (p k a b xi X u : ℕ) [NeZero p]
    (colour : Fin k → Bool) (lam : ℝ) : ℝ :=
  levelConditionedMaximum p k a b xi X u colour / momentScale X p k u a b lam

/-- Retain the whole finite intermediate sum and its independently bounded deep remainder at the source normalization. -/
def conditioningAllowance (p k a b xi X u H : ℕ) [NeZero p]
    (colour : Fin k → Bool) (lam : ℝ) : ℝ :=
  (p : ℝ) ^ (-((H : ℝ) / 2)) + selectionCost k u * ∑ h ∈ Finset.range H,
    singularCost p k u ^ h * (p : ℝ) ^ (-2 * (k : ℝ) * u * h) *
      normalizedLevel p k a (b + h) xi X u colour lam

/-- No signs are introduced by dividing the actual nonnegative level energies by their positive scale. -/
theorem allowance_nonneg {p k a b xi X u H : ℕ} [NeZero p] (hX : 0 < X)
    (colour : Fin k → Bool) (lam : ℝ) :
    0 ≤ conditioningAllowance p k a b xi X u H colour lam := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  unfold conditioningAllowance
  apply add_nonneg (by positivity)
  apply mul_nonneg (by unfold selectionCost; positivity)
  apply Finset.sum_nonneg
  intro h hh
  apply mul_nonneg (by unfold singularCost; positivity)
  exact div_nonneg (level_conditioned_nonneg colour) (momentScale_pos hX0 hp0 _ _ _ _ _).le

/-- Normalize the full intermediate sum by an exact identity, without replacing it by a maximum or dropping levels. -/
theorem allowance_scale_identity {p k a b xi X u H : ℕ} [NeZero p] (hX : 0 < X)
    (colour : Fin k → Bool) (lam : ℝ) :
    momentScale X p k u a b lam * conditioningAllowance p k a b xi X u H colour lam =
      momentScale X p k u a b lam * (p : ℝ) ^ (-((H : ℝ) / 2)) +
      selectionCost k u * ∑ h ∈ Finset.range H,
        singularCost p k u ^ h * levelConditionedMaximum p k a (b + h) xi X u colour := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hM := momentScale_pos hX0 hp0 (k : ℝ) (u : ℝ) (a : ℝ) (b : ℝ) lam
  have hterm (h : ℕ) :
      momentScale X p k u a b lam *
        (singularCost p k u ^ h * (p : ℝ) ^ (-2 * (k : ℝ) * u * h) *
          normalizedLevel p k a (b + h) xi X u colour lam) =
      singularCost p k u ^ h * levelConditionedMaximum p k a (b + h) xi X u colour := by
    have hscale := intermediate_scale_identity hX0 hp0 (k : ℝ) (u : ℝ) (a : ℝ) (b : ℝ) (h : ℝ) lam
    unfold normalizedLevel
    push_cast
    rw [hscale]
    have hPpow : (p : ℝ) ^ (-2 * (k : ℝ) * u * h) ≠ 0 :=
      (Real.rpow_pos_of_pos hp0 _).ne'
    field_simp
  unfold conditioningAllowance
  calc
    _ = momentScale X p k u a b lam * (p : ℝ) ^ (-((H : ℝ) / 2)) +
        selectionCost k u * ∑ h ∈ Finset.range H,
          momentScale X p k u a b lam *
            (singularCost p k u ^ h * (p : ℝ) ^ (-2 * (k : ℝ) * u * h) *
              normalizedLevel p k a (b + h) xi X u colour lam) := by
      rw [← Finset.mul_sum]
      ring
    _ = _ := by simp_rw [hterm]

/-- Discharge the actual next-level moment bound using only proved elementary moments and explicit finite scale conditions. -/
theorem mixed_le_scale_allowance {p k a b xi X u H : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b) (hH : 1 ≤ H)
    (hgap : b - a ≤ 2 * H) (hX : p ^ (b + H) ≤ X)
    (hp : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (p : ℝ))
    (colour : Fin k → Bool) :
    levelMixedMaximum p k a b xi X u colour ≤
      momentScale X p k u a b (((k * (2 * u + 1) : ℕ) : ℝ)) *
        conditioningAllowance p k a b xi X u H colour (((k * (2 * u + 1) : ℕ) : ℝ)) := by
  have hX0 : 0 < X := (Nat.pos_of_ne_zero (NeZero.ne (p ^ (b + H)))).trans_le hX
  rw [allowance_scale_identity hX0, elementary_scale]
  exact finite_conditioning_power_saving hk hu hab hH hgap hX hp colour

/-- Retain two explicitly stated sharper homogeneous estimates through the complete finite conditioning remainder; their truth is not asserted here. -/
theorem mixed_le_scale_allowance_of_scaled_bounds {p k a b xi X u H : ℕ} [NeZero p]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a ≤ b) (hH : 1 ≤ H)
    (hgap : b - a ≤ 2 * H) (hX : 0 < X) {C lam : ℝ} (hC : 1 ≤ C)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam)
    (hp : (C * iterationConstant k u) ^ 2 ≤ (p : ℝ))
    (hA : meanValue ((u + 1) * k) k (X / p ^ a + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ a) ^ lam)
    (hB : meanValue ((u + 1) * k) k (X / p ^ (b + H) + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ (b + H)) ^ lam)
    (colour : Fin k → Bool) :
    levelMixedMaximum p k a b xi X u colour ≤
      momentScale X p k u a b lam * conditioningAllowance p k a b xi X u H colour lam := by
  have hkp := (degree_lt_of_budget hk hu hC hp).le
  rw [allowance_scale_identity hX]
  apply (finite_conditioning_iteration hkp (by omega) (by omega) colour b H).trans
  apply add_le_add _ (le_refl _)
  have he := deep_remainder_of_scaled_bounds (xi := xi) hk hu hab hH hgap hX hC hlam hp hA hB colour
  simpa only [momentScale, ← Real.rpow_natCast, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using he

/-- Two explicit actual homogeneous estimates suffice for the complete finite normalized recurrence at any exponent in the critical range. -/
theorem normalized_iteration_of_scaled_bounds {p k a b xi eta X u H : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a < b) (hH : 1 ≤ H)
    (hgap : k * b - b ≤ 2 * H) (hX : 0 < X) {C lam : ℝ} (hC : 1 ≤ C)
    (hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ lam)
    (hp : (C * iterationConstant k u) ^ 2 ≤ (p : ℝ))
    (hA : meanValue ((u + 1) * k) k (X / p ^ b + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ b) ^ lam)
    (hB : meanValue ((u + 1) * k) k (X / p ^ (k * b + H) + 1) ≤
      C * ((X : ℝ) / (p : ℝ) ^ (k * b + H)) ^ lam)
    (heta : eta < p ^ b) (colourA colourB : Fin k → Bool) :
    conditionedMoment p k a b xi eta X u colourA colourB ≤
      (VinogradovSignedCongruence.colourFactorial colourA : ℝ) *
        C ^ (1 - 1 / (u : ℝ)) * momentScale X p k u a b lam *
        (p : ℝ) ^ (-(lam - 2 * (k : ℝ) * ((u : ℝ) + 1) +
          (k : ℝ) * ((k : ℝ) + 1) / 2) * ((b : ℝ) - a)) *
        conditioningAllowance p k b (k * b) eta X u H colourB lam ^ (1 / (u : ℝ)) := by
  have hkp := degree_lt_of_budget hk hu hC hp
  have hbk : b ≤ k * b := by nlinarith
  have hI := mixed_le_scale_allowance_of_scaled_bounds (xi := eta) hk hu hbk hH hgap hX hC hlam hp hA hB colourB
  exact normalized_congruencing_transfer (xi := xi)
    (R := conditioningAllowance p k b (k * b) eta X u H colourB lam)
    hkp (by omega) hab (by omega) hX heta colourA colourB
    (le_trans zero_le_one hC) (allowance_nonneg hX colourB _) hA
    (by simpa only [Nat.cast_mul] using hI)

/-- The actual signed finite recurrence exposes the exponent-defect factor with every moment premise discharged at the elementary exponent. -/
theorem normalized_finite_iteration {p k a b xi eta X u H : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a < b) (hH : 1 ≤ H)
    (hgap : k * b - b ≤ 2 * H) (hX : p ^ (k * b + H) ≤ X)
    (hp : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (p : ℝ))
    (heta : eta < p ^ b) (colourA colourB : Fin k → Bool) :
    conditionedMoment p k a b xi eta X u colourA colourB ≤
      (VinogradovSignedCongruence.colourFactorial colourA : ℝ) *
        elementaryConstant k u ^ (1 - 1 / (u : ℝ)) *
        momentScale X p k u a b (((k * (2 * u + 1) : ℕ) : ℝ)) *
        (p : ℝ) ^ (-((k : ℝ) * ((k : ℝ) - 1) / 2) * ((b : ℝ) - a)) *
        conditioningAllowance p k b (k * b) eta X u H colourB
          (((k * (2 * u + 1) : ℕ) : ℝ)) ^ (1 / (u : ℝ)) := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)
  have hX0 : 0 < X := (Nat.pos_of_ne_zero (NeZero.ne (p ^ (k * b + H)))).trans_le hX
  have hbk : b ≤ k * b := by nlinarith
  have hXb : p ^ b ≤ X := (Nat.pow_le_pow_right hp1 (by omega : b ≤ k * b + H)).trans hX
  have hJ : meanValue ((u + 1) * k) k (X / p ^ b + 1) ≤ elementaryConstant k u *
      ((X : ℝ) / (p : ℝ) ^ b) ^ (((k * (2 * u + 1) : ℕ) : ℝ)) := by
    simpa only [Real.rpow_natCast] using higher_meanValue_rounded (k := k) (u := u) hXb
  have hJdeep : meanValue ((u + 1) * k) k (X / p ^ (k * b + H) + 1) ≤ elementaryConstant k u *
      ((X : ℝ) / (p : ℝ) ^ (k * b + H)) ^ (((k * (2 * u + 1) : ℕ) : ℝ)) := by
    simpa only [Real.rpow_natCast] using higher_meanValue_rounded (k := k) (u := u) hX
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hlam : 2 * (k : ℝ) * ((u : ℝ) + 1) - (k : ℝ) * ((k : ℝ) + 1) / 2 ≤
      ((k * (2 * u + 1) : ℕ) : ℝ) := by push_cast; nlinarith
  have he := normalized_iteration_of_scaled_bounds (xi := xi) hk hu hab hH hgap hX0
    (elementaryConstant_one_le k u) hlam hp hJ hJdeep heta colourA colourB
  have hdefect : ((k * (2 * u + 1) : ℕ) : ℝ) - 2 * (k : ℝ) * ((u : ℝ) + 1) +
      (k : ℝ) * ((k : ℝ) + 1) / 2 = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    push_cast
    ring
  simpa only [hdefect] using he

/-- The full retained intermediate weight has an explicit geometric upper bound, including the per-step constant. -/
theorem intermediate_weight_le {p k u h : ℕ} [NeZero p] (hk : 1 ≤ k) :
    singularCost p k u ^ h * (p : ℝ) ^ (-2 * (k : ℝ) * u * h) ≤
      iterationConstant k u ^ h *
        (p : ℝ) ^ (-(2 * (k : ℝ) * u - k + 1) * h) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hscale : ((p : ℝ) ^ (k - 1)) ^ h * (p : ℝ) ^ (-2 * (k : ℝ) * u * h) =
      (p : ℝ) ^ (-(2 * (k : ℝ) * u - k + 1) * h) := by
    rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_add hp0]
    congr 1
    simp only [Nat.cast_mul, Nat.cast_sub hk, Nat.cast_one]
    ring
  calc
    _ ≤ (iterationConstant k u * (p : ℝ) ^ (k - 1)) ^ h *
        (p : ℝ) ^ (-2 * (k : ℝ) * u * h) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by unfold singularCost; positivity) (singularCost_le_power p k u) h)
        (by positivity)
    _ = iterationConstant k u ^ h *
        (((p : ℝ) ^ (k - 1)) ^ h * (p : ℝ) ^ (-2 * (k : ℝ) * u * h)) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hscale]

/-- An explicit geometric budget for the same actual intermediate conditioned levels. -/
def geometricAllowance (p k a b xi X u H : ℕ) [NeZero p]
    (colour : Fin k → Bool) (lam : ℝ) : ℝ :=
  (p : ℝ) ^ (-((H : ℝ) / 2)) + selectionCost k u * ∑ h ∈ Finset.range H,
    iterationConstant k u ^ h * (p : ℝ) ^ (-(2 * (k : ℝ) * u - k + 1) * h) *
      normalizedLevel p k a (b + h) xi X u colour lam

/-- Pay each singular weight explicitly before any largest-level selection. -/
theorem allowance_le_geometric {p k a b xi X u H : ℕ} [NeZero p]
    (hk : 1 ≤ k) (hX : 0 < X) (colour : Fin k → Bool) (lam : ℝ) :
    conditioningAllowance p k a b xi X u H colour lam ≤
      geometricAllowance p k a b xi X u H colour lam := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  unfold conditioningAllowance geometricAllowance
  apply add_le_add (le_refl _)
  apply mul_le_mul_of_nonneg_left _ (by unfold selectionCost; positivity)
  apply Finset.sum_le_sum
  intro h hh
  exact mul_le_mul_of_nonneg_right (intermediate_weight_le hk)
    (div_nonneg (level_conditioned_nonneg colour) (momentScale_pos hX0 hp0 _ _ _ _ _).le)

/-- The actual signed normalized recurrence has a geometric intermediate budget, with all moment estimates and constants supplied by proved theorems. -/
theorem conditioned_le_geometric_iteration {p k a b xi eta X u H : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a < b) (hH : 1 ≤ H)
    (hgap : k * b - b ≤ 2 * H) (hX : p ^ (k * b + H) ≤ X)
    (hp : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (p : ℝ))
    (heta : eta < p ^ b) (colourA colourB : Fin k → Bool) :
    conditionedMoment p k a b xi eta X u colourA colourB ≤
      (VinogradovSignedCongruence.colourFactorial colourA : ℝ) *
        elementaryConstant k u ^ (1 - 1 / (u : ℝ)) *
        momentScale X p k u a b (((k * (2 * u + 1) : ℕ) : ℝ)) *
        (p : ℝ) ^ (-((k : ℝ) * ((k : ℝ) - 1) / 2) * ((b : ℝ) - a)) *
        geometricAllowance p k b (k * b) eta X u H colourB
          (((k * (2 * u + 1) : ℕ) : ℝ)) ^ (1 / (u : ℝ)) := by
  have hX0 : 0 < X := (Nat.pos_of_ne_zero (NeZero.ne (p ^ (k * b + H)))).trans_le hX
  apply (normalized_finite_iteration hk hu hab hH hgap hX hp heta colourA colourB).trans
  apply mul_le_mul_of_nonneg_left _ (by unfold momentScale elementaryConstant; positivity)
  exact Real.rpow_le_rpow (allowance_nonneg hX0 colourB _)
    (allowance_le_geometric (by omega) hX0 colourB _) (by positivity)

end
end RiemannGaussian.VinogradovNormalizedIteration
