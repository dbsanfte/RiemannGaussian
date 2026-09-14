/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovInterpolation

/-!
# Continuous Holder and explicit absorption for conditioning

The exact pointwise factorization includes zeros and every natural order
q>1. Continuity supplies all integral hypotheses for the actual torus.
Weighted arithmetic-geometric mean then absorbs the original moment with
an explicit q and selection-cost power, without a supplied moment budget.
-/

namespace RiemannGaussian.VinogradovConditioningHolder
noncomputable section
open UnitAddTorus MeasureTheory
/-- Use the original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle Haar measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The pointwise Holder factorization holds at every nonnegative value, including zeros. -/
theorem conditioning_atom {q k : ℕ} (hq : 1 < q)
    {w g f : ℝ} (hw : 0 ≤ w) (hg : 0 ≤ g) (hf : 0 ≤ f) :
    (w * g ^ q) ^ (1 / (q : ℝ)) * (w * f ^ (k * q)) ^ (1 - 1 / (q : ℝ)) =
      w * g * f ^ (k * (q - 1)) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hq0 : (q : ℝ) ≠ 0 := by linarith
  have ht : 0 < 1 / (q : ℝ) := one_div_pos.mpr (by linarith)
  by_cases hw0 : w = 0
  · simp only [hw0, zero_mul, Real.zero_rpow ht.ne']
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  rw [Real.mul_rpow hw (pow_nonneg hg _), Real.mul_rpow hw (pow_nonneg hf _)]
  simp_rw [← Real.rpow_natCast, ← Real.rpow_mul hg, ← Real.rpow_mul hf]
  have hgexp : (q : ℝ) * (1 / (q : ℝ)) = 1 := by field_simp
  have hfexp : ((k * q : ℕ) : ℝ) * (1 - 1 / (q : ℝ)) = ((k * (q - 1) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    field_simp
  rw [hgexp, Real.rpow_one, hfexp, Real.rpow_natCast]
  calc
    _ = (w ^ (1 / (q : ℝ)) * w ^ (1 - 1 / (q : ℝ))) * g * f ^ (k * (q - 1)) := by ring
    _ = _ := by rw [← Real.rpow_add hwpos]; simp

/-- Prove the actual continuous torus Holder estimate with every integral condition discharged. -/
theorem conditioning_holder {d : Type*} [Fintype d] {q k : ℕ} (hq : 1 < q)
    (A B C : UnitAddTorus d → ℂ) (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) :
    (∫ theta, ‖A theta‖ ^ 2 * ‖B theta‖ * ‖C theta‖ ^ (k * (q - 1))) ≤
      (∫ theta, ‖A theta‖ ^ 2 * ‖B theta‖ ^ q) ^ (1 / (q : ℝ)) *
        (∫ theta, ‖A theta‖ ^ 2 * ‖C theta‖ ^ (k * q)) ^ (1 - 1 / (q : ℝ)) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have ht : 0 < 1 / (q : ℝ) := one_div_pos.mpr hqpos
  have ht1 : 1 / (q : ℝ) < 1 := (div_lt_one hqpos).mpr hqR
  have he := VinogradovInterpolation.integral_geometric_le ht ht1
    (fun theta => ‖A theta‖ ^ 2 * ‖B theta‖ ^ q)
    (fun theta => ‖A theta‖ ^ 2 * ‖C theta‖ ^ (k * q))
    ((hA.norm.pow 2).mul (hB.norm.pow _)) ((hA.norm.pow 2).mul (hC.norm.pow _))
    (fun _ => by positivity) (fun _ => by positivity)
  simpa only [conditioning_atom hq (sq_nonneg _) (norm_nonneg _) (norm_nonneg _)] using he


/-- Weighted AM-GM absorbs the original moment with explicit order and selection-cost constants. -/
theorem holder_absorption {q : ℕ} (hq : 1 < q) {I S K D : ℝ}
    (hI : 0 ≤ I) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (h : I ≤ S + D * K ^ (1 / (q : ℝ)) * I ^ (1 - 1 / (q : ℝ))) :
    I ≤ (q : ℝ) * S + D ^ q * K := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have ht : 0 ≤ 1 / (q : ℝ) := by positivity
  have ht' : 0 ≤ 1 - 1 / (q : ℝ) := by
    have hlt := (div_lt_one hqpos).mpr hqR
    linarith
  have hy := Real.geom_mean_le_arith_mean2_weighted ht ht'
    (mul_nonneg (pow_nonneg hD q) hK) hI (by ring)
  have hroot : (D ^ q * K) ^ (1 / (q : ℝ)) = D * K ^ (1 / (q : ℝ)) := by
    rw [Real.mul_rpow (pow_nonneg hD _) hK, ← Real.rpow_natCast, ← Real.rpow_mul hD]
    have hq0 : (q : ℝ) ≠ 0 := hqpos.ne'
    have hx : (q : ℝ) * (1 / (q : ℝ)) = 1 := by field_simp
    rw [hx, Real.rpow_one]
  rw [hroot] at hy
  have hh := h.trans (add_le_add (le_refl S) hy)
  have hh' := mul_le_mul_of_nonneg_left hh hqpos.le
  have hq0 : (q : ℝ) ≠ 0 := hqpos.ne'
  have he : (q : ℝ) * (S + (1 / (q : ℝ) * (D ^ q * K) + (1 - 1 / (q : ℝ)) * I)) =
      (q : ℝ) * S + D ^ q * K + ((q : ℝ) - 1) * I := by field_simp; ring
  rw [he] at hh'
  linarith

end
end RiemannGaussian.VinogradovConditioningHolder
