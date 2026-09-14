/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovConditioningPowerSaving
import RiemannGaussian.VinogradovCongruencingStep

/-!
# Actual finite conditioning inside signed congruencing

The reverse maximum in the original signed congruencing step is exactly
the next original conditioning maximum at scales b,kb. The proved finite
conditioning recurrence and its explicit deep remainder therefore feed back
into that step, retaining both original block colours, the canonical coarse
class, every finite intermediate level and the unchanged endpoint.

The integer congruence cost is also rewritten exactly as a positive real
power, including triangular division and truncated-subtraction side
conditions. The normalized recurrence is in `VinogradovNormalizedIteration`.
These are finite ingredients underlying Wooley (2012), Lemma 6.3; the full
high-moment exponent improvement and VK zeta growth remain open.
https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf
-/

namespace RiemannGaussian.VinogradovIteratedCongruencing
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

/-- The reverse maximum is exactly the original next conditioning maximum, with its canonical coarse class. -/
theorem reverse_maximum_eq_level {p k b eta X u : ℕ} [NeZero p]
    (heta : eta < p ^ b) (colour : Fin k → Bool) :
    reverseConditionedMaximum p k b u X (eta : ℤ) colour =
      levelMixedMaximum p k b (k * b) eta X u colour := by
  unfold reverseConditionedMaximum VinogradovInterpolation.reverseMaximum
    levelMixedMaximum VinogradovSingularConditioning.mixedMoment
  have heq : (((eta : ℤ) : ZMod (p ^ b))).val = eta := by
    rw [Int.cast_natCast, ZMod.val_natCast_of_lt heta]
  simp only [Nat.mul_assoc]
  congr!

/-- The signed congruencing cost retains its original colour factorial and all finite base powers. -/
def stepCost (p k a b : ℕ) (colour : Fin k → Bool) : ℝ :=
  ((p ^ ((a + b) * (k * (k - 1) / 2)) *
    VinogradovSignedCongruence.colourFactorial colour : ℕ) : ℝ) *
      ((p ^ (k * b - a)) ^ k : ℕ)

/-- The original signed conditioned moment transfers to the actual next conditioning maximum. -/
theorem conditioned_le_level_mixed {p k a b xi eta X u : ℕ} [Fact p.Prime]
    (hkp : k < p) (hk : 0 < k) (hab : a < b) (hu : 0 < u)
    (heta : eta < p ^ b) (colourA colourB : Fin k → Bool) :
    conditionedMoment p k a b xi eta X u colourA colourB ≤
      stepCost p k a b colourA *
        (meanValue ((u + 1) * k) k (X / p ^ b + 1) ^ (1 - 1 / (u : ℝ)) *
          levelMixedMaximum p k b (k * b) eta X u colourB ^ (1 / (u : ℝ))) := by
  have he := conditioned_congruencing_step (xi := xi) (X := X) hkp hk hab hu
    (eta : ℤ) colourA colourB
  rw [reverse_maximum_eq_level heta colourB] at he
  have heq : (((eta : ℤ) : ZMod (p ^ b))).val = eta := by
    rw [Int.cast_natCast, ZMod.val_natCast_of_lt heta]
  convert he using 1 <;> simp only [conditionedMoment, stepCost, mul_assoc]
  all_goals congr!
  all_goals exact heq.symm

/-- The actual level maximum is nonnegative, including empty original windows. -/
theorem level_mixed_nonneg {p k a b xi X u : ℕ} [NeZero p] (colour : Fin k → Bool) :
    0 ≤ levelMixedMaximum p k a b xi X u colour := by
  have hi : 0 ≤ VinogradovSingularConditioning.mixedMoment p k a b xi 0 X (k * u) colour :=
    integral_nonneg (fun _ => by positivity)
  apply hi.trans
  exact Finset.le_sup' (fun c : Fin (p ^ b) =>
    VinogradovSingularConditioning.mixedMoment p k a b xi c.val X (k * u) colour)
    (Finset.mem_univ 0)

/-- Feed the proved deep remainder and the full intermediate sum into the actual signed congruencing step. -/
theorem conditioned_le_finite_iteration {p k a b xi eta X u H : ℕ} [Fact p.Prime]
    (hk : 2 ≤ k) (hu : k ≤ u) (hab : a < b) (hH : 1 ≤ H)
    (hgap : k * b - b ≤ 2 * H) (hX : p ^ (k * b + H) ≤ X)
    (hp : (elementaryConstant k u * iterationConstant k u) ^ 2 ≤ (p : ℝ))
    (heta : eta < p ^ b) (colourA colourB : Fin k → Bool) :
    conditionedMoment p k a b xi eta X u colourA colourB ≤
      stepCost p k a b colourA *
        (meanValue ((u + 1) * k) k (X / p ^ b + 1) ^ (1 - 1 / (u : ℝ)) *
          ((((X : ℝ) / (p : ℝ) ^ b) ^ k *
              ((X : ℝ) / (p : ℝ) ^ (k * b)) ^ (2 * (k * u))) *
            (p : ℝ) ^ (-((H : ℝ) / 2)) +
           selectionCost k u * ∑ h ∈ Finset.range H,
             singularCost p k u ^ h *
               levelConditionedMaximum p k b (k * b + h) eta X u colourB) ^ (1 / (u : ℝ))) := by
  have hkp := degree_lt_of_budget hk hu (elementaryConstant_one_le k u) hp
  have hbk : b ≤ k * b := by nlinarith
  have hI := finite_conditioning_power_saving (xi := eta) hk hu hbk hH hgap hX hp colourB
  apply (conditioned_le_level_mixed hkp (by omega) hab (by omega) heta colourA colourB).trans
  apply mul_le_mul_of_nonneg_left _ (by unfold stepCost; positivity)
  apply mul_le_mul_of_nonneg_left _ (by apply Real.rpow_nonneg; rw [meanValue_eq_count]; positivity)
  exact Real.rpow_le_rpow (level_mixed_nonneg colourB) hI (by positivity)

/-- Extract an attained largest intermediate term while retaining the exact finite cardinality. -/
theorem exists_dominant_intermediate {H : ℕ} (hH : 0 < H) (f : ℕ → ℝ) :
    ∃ h < H, (∑ j ∈ Finset.range H, f j) ≤ (H : ℝ) * f h := by
  obtain ⟨h, hh, hmax⟩ := Finset.exists_max_image (Finset.range H) f
    (by exact ⟨0, Finset.mem_range.mpr hH⟩)
  refine ⟨h, Finset.mem_range.mp hh, ?_⟩
  calc
    _ ≤ ∑ j ∈ Finset.range H, f h := Finset.sum_le_sum hmax
    _ = _ := by simp

/-- Rewrite the literal integer congruence cost as its exact positive real-power scale, retaining the sign factorial. -/
theorem stepCost_eq_power {p k a b : ℕ} [NeZero p]
    (hk : 1 ≤ k) (hab : a ≤ b) (colour : Fin k → Bool) :
    stepCost p k a b colour =
      (VinogradovSignedCongruence.colourFactorial colour : ℝ) *
        (p : ℝ) ^ (((a : ℝ) + b) * ((k : ℝ) * ((k : ℝ) - 1) / 2) +
          (k : ℝ) * ((k : ℝ) * b - a)) := by
  have hP : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have htri : ((k * (k - 1) / 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
    rw [Nat.cast_div (Nat.two_dvd_mul_sub_one k) (by norm_num : (2 : ℝ) ≠ 0)]
    simp only [Nat.cast_mul, Nat.cast_sub hk, Nat.cast_one, Nat.cast_ofNat]
  have hkb : a ≤ k * b := hab.trans (by nlinarith)
  have hA : ((p ^ ((a + b) * (k * (k - 1) / 2)) : ℕ) : ℝ) =
      (p : ℝ) ^ (((a : ℝ) + b) * ((k : ℝ) * ((k : ℝ) - 1) / 2)) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_mul, Nat.cast_add, htri]
  have hB : (((p ^ (k * b - a)) ^ k : ℕ) : ℝ) =
      (p : ℝ) ^ ((k : ℝ) * ((k : ℝ) * b - a)) := by
    rw [← pow_mul, Nat.cast_pow, ← Real.rpow_natCast]
    congr 1
    rw [Nat.cast_mul, Nat.cast_sub hkb, Nat.cast_mul]
    ring
  unfold stepCost
  rw [Nat.cast_mul, hA, hB]
  calc
    _ = (VinogradovSignedCongruence.colourFactorial colour : ℝ) *
        ((p : ℝ) ^ (((a : ℝ) + b) * ((k : ℝ) * ((k : ℝ) - 1) / 2)) *
         (p : ℝ) ^ ((k : ℝ) * ((k : ℝ) * b - a))) := by ring
    _ = _ := by rw [← Real.rpow_add hP]

/-- The actual conditioned level maximum is nonnegative, even when original windows are empty. -/
theorem level_conditioned_nonneg {p k a b xi X u : ℕ} [NeZero p] (colour : Fin k → Bool) :
    0 ≤ levelConditionedMaximum p k a b xi X u colour := by
  have h0 : 0 ≤ conditionedMaximum p k a b xi 0 X u colour := by
    apply (conditionedMoment_nonneg p k a b xi 0 X u colour colour).trans
    exact Finset.le_sup' (fun c : Fin k → Bool => conditionedMoment p k a b xi 0 X u colour c)
      (Finset.mem_univ colour)
  exact h0.trans (level_conditioned_le colour (0 : Fin (p ^ b)))

end
end RiemannGaussian.VinogradovIteratedCongruencing
