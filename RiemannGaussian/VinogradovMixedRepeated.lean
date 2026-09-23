/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovEndpointDeletion
import RiemannGaussian.VinogradovRepeatedSolutions

/-!
# Repeated coordinates with a fixed mixed tail

The repeated-coordinate Holder bound retains the actual doubled-block
mixed moment and the original tail moment separately. It does not invoke
dilation invariance for only one factor of a mixed moment.
-/

namespace RiemannGaussian.VinogradovMixedRepeated
noncomputable section
open scoped BigOperators Classical ComplexConjugate
open MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open VinogradovPartitionEnergy VinogradovProductEnergy VinogradovCrossMoment
open VinogradovMixedMoments VinogradovRepeatedSolutions

/-- The original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Three-factor Holder keeps the last nonconstant factor instead of
replacing it by probability mass. -/
theorem integral_triple_geometric_le {d : Type*} [Fintype d] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < 1)
    (A B W : UnitAddTorus d → ℝ) (hA : Continuous A) (hB : Continuous B)
    (hW : Continuous W) (hA0 : ∀ t, 0 ≤ A t) (hB0 : ∀ t, 0 ≤ B t)
    (hW0 : ∀ t, 0 ≤ W t) :
    (∫ t, A t ^ a * B t ^ b * W t ^ (1 - (a + b))) ≤
      (∫ t, A t) ^ a * (∫ t, B t) ^ b * (∫ t, W t) ^ (1 - (a + b)) := by
  have hsum : 0 < a + b := by linarith
  have ht : 0 < a / (a + b) := div_pos ha hsum
  have ht1 : a / (a + b) < 1 := (div_lt_one hsum).mpr (by linarith)
  have hc : 1 - a / (a + b) = b / (a + b) := by field_simp; ring
  let H (t : UnitAddTorus d) := A t ^ (a / (a + b)) * B t ^ (b / (a + b))
  have hH : Continuous H :=
    (hA.rpow_const (fun _ => Or.inr ht.le)).mul
      (hB.rpow_const (fun _ => Or.inr (div_pos hb hsum).le))
  have hH0 (t) : 0 ≤ H t :=
    mul_nonneg (Real.rpow_nonneg (hA0 t) _) (Real.rpow_nonneg (hB0 t) _)
  have hi := VinogradovInterpolation.integral_geometric_le ht ht1 A B hA hB hA0 hB0
  rw [hc] at hi
  have ho := VinogradovInterpolation.integral_geometric_le hsum hab H W hH hW hH0 hW0
  have he (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      (x ^ (a / (a + b)) * y ^ (b / (a + b))) ^ (a + b) = x ^ a * y ^ b := by
    rw [Real.mul_rpow (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _),
      ← Real.rpow_mul hx, ← Real.rpow_mul hy,
      div_mul_cancel₀ a hsum.ne', div_mul_cancel₀ b hsum.ne']
  have hHpow (t) : H t ^ (a + b) = A t ^ a * B t ^ b := he _ _ (hA0 t) (hB0 t)
  simp_rw [hHpow] at ho
  apply ho.trans
  have hp := Real.rpow_le_rpow (integral_nonneg hH0) hi hsum.le
  rw [he _ _ (integral_nonneg hA0) (integral_nonneg hB0)] at hp
  exact mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (integral_nonneg hW0) _)

private theorem repeated_atom {m : ℕ} (hm : 2 ≤ m) {x y w : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hw : 0 ≤ w) :
    (x ^ (2 * m) * w) ^ (1 - 1 / (m : ℝ)) *
        (y ^ (2 * m) * w) ^ (1 / (2 * (m : ℝ))) *
          w ^ (1 / (2 * (m : ℝ))) = x ^ (2 * m - 2) * y * w := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have ha : 0 ≤ 1 - 1 / (m : ℝ) :=
    sub_nonneg.mpr ((div_le_one hm0).mpr (by linarith))
  have hb : 0 ≤ 1 / (2 * (m : ℝ)) := by positivity
  have hex : ((2 * m : ℕ) : ℝ) * (1 - 1 / (m : ℝ)) = (2 * m - 2 : ℕ) := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * m)]
    push_cast
    field_simp
  have hey : ((2 * m : ℕ) : ℝ) * (1 / (2 * (m : ℝ))) = 1 := by
    push_cast
    field_simp
  have hew : (1 - 1 / (m : ℝ)) + 1 / (2 * (m : ℝ)) + 1 / (2 * (m : ℝ)) = 1 := by
    field_simp
    ring
  rw [Real.mul_rpow (pow_nonneg hx _) hw, Real.mul_rpow (pow_nonneg hy _) hw]
  calc
    _ = (x ^ (2 * m)) ^ (1 - 1 / (m : ℝ)) *
        (y ^ (2 * m)) ^ (1 / (2 * (m : ℝ))) *
        (w ^ (1 - 1 / (m : ℝ)) * w ^ (1 / (2 * (m : ℝ))) *
          w ^ (1 / (2 * (m : ℝ)))) := by ring
    _ = _ := by
      rw [← Real.rpow_add_of_nonneg hw ha hb,
        ← Real.rpow_add_of_nonneg hw (add_nonneg ha hb) hb, hew, Real.rpow_one,
        ← Real.rpow_natCast x (2 * m), ← Real.rpow_mul hx,
        ← Real.rpow_natCast y (2 * m), ← Real.rpow_mul hy,
        hex, hey, Real.rpow_natCast, Real.rpow_one]

/-- The repeated-coordinate integral keeps the fixed tail in all three
Holder factors, including the actual doubled-block mixed moment. -/
theorem repeated_integral_le {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    {m : ℕ} (hm : 2 ≤ m) (s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) :
    (∫ t : UnitAddTorus d,
      ‖polynomial v (fun _ => 1) t‖ ^ (2 * m - 2) *
        ‖polynomial (fun i j => 2 * v i j) (fun _ => 1) t‖ *
          ‖polynomial u (fun _ => 1) t‖ ^ (2 * s)) ≤
      mixedMoment m s v u ^ (1 - 1 / (m : ℝ)) *
        mixedMoment m s (fun i j => 2 * v i j) u ^ (1 / (2 * (m : ℝ))) *
          moment s u ^ (1 / (2 * (m : ℝ))) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have ha : 0 < 1 - 1 / (m : ℝ) :=
    sub_pos.mpr ((div_lt_one hm0).mpr (by linarith))
  have hb : 0 < 1 / (2 * (m : ℝ)) := by positivity
  have hsum : (1 - 1 / (m : ℝ)) + 1 / (2 * (m : ℝ)) < 1 := by
    have h : 1 / (2 * (m : ℝ)) + 1 / (2 * (m : ℝ)) = 1 / (m : ℝ) := by ring
    linarith
  have hc : 1 - ((1 - 1 / (m : ℝ)) + 1 / (2 * (m : ℝ))) =
      1 / (2 * (m : ℝ)) := by ring
  have h := integral_triple_geometric_le ha hb hsum
    (fun t : UnitAddTorus d => ‖polynomial v (fun _ => 1) t‖ ^ (2 * m) *
      ‖polynomial u (fun _ => 1) t‖ ^ (2 * s))
    (fun t : UnitAddTorus d => ‖polynomial (fun i j => 2 * v i j) (fun _ => 1) t‖ ^ (2 * m) *
      ‖polynomial u (fun _ => 1) t‖ ^ (2 * s))
    (fun t : UnitAddTorus d => ‖polynomial u (fun _ => 1) t‖ ^ (2 * s))
    (((continuous_polynomial _ _).norm.pow _).mul ((continuous_polynomial _ _).norm.pow _))
    (((continuous_polynomial _ _).norm.pow _).mul ((continuous_polynomial _ _).norm.pow _))
    ((continuous_polynomial _ _).norm.pow _)
    (fun _ => by positivity) (fun _ => by positivity) (fun _ => by positivity)
  rw [hc] at h
  have hatom (t : UnitAddTorus d) := repeated_atom hm
    (norm_nonneg (polynomial v (fun _ => 1) t))
    (norm_nonneg (polynomial (fun i j => 2 * v i j) (fun _ => 1) t))
    (show 0 ≤ ‖polynomial u (fun _ => 1) t‖ ^ (2 * s) by positivity)
  simp_rw [hatom] at h
  simpa only [mixedMoment, polynomial, one_mul, moment] using h

/-- Maximality over doubled blocks produces the required fractional
deficit without changing the original tail frequencies. -/
theorem repeated_integral_le_of_doubling {ι κ d : Type*}
    [Fintype ι] [Fintype κ] [Fintype d] {m : ℕ} (hm : 2 ≤ m)
    (s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ)
    (hdouble : mixedMoment m s (fun i j => 2 * v i j) u ≤ mixedMoment m s v u) :
    (∫ t : UnitAddTorus d,
      ‖polynomial v (fun _ => 1) t‖ ^ (2 * m - 2) *
        ‖polynomial (fun i j => 2 * v i j) (fun _ => 1) t‖ *
          ‖polynomial u (fun _ => 1) t‖ ^ (2 * s)) ≤
      mixedMoment m s v u ^ (1 - 1 / (2 * (m : ℝ))) *
        moment s u ^ (1 / (2 * (m : ℝ))) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have ha : 0 ≤ 1 - 1 / (m : ℝ) :=
    sub_nonneg.mpr ((div_le_one (by linarith)).mpr (by linarith))
  have hb : 0 ≤ 1 / (2 * (m : ℝ)) := by positivity
  have h := Real.rpow_le_rpow (mixedMoment_nonneg _ _ _ _) hdouble hb
  have hJ : 0 ≤ moment s u := integral_nonneg (fun _ => by positivity)
  have h' :
      mixedMoment m s v u ^ (1 - 1 / (m : ℝ)) *
        mixedMoment m s (fun i j => 2 * v i j) u ^ (1 / (2 * (m : ℝ))) *
          moment s u ^ (1 / (2 * (m : ℝ))) ≤
      mixedMoment m s v u ^ (1 - 1 / (m : ℝ)) *
        mixedMoment m s v u ^ (1 / (2 * (m : ℝ))) *
          moment s u ^ (1 / (2 * (m : ℝ))) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h (Real.rpow_nonneg (mixedMoment_nonneg _ _ _ _) _))
      (Real.rpow_nonneg hJ _)
  have he : (1 - 1 / (m : ℝ)) + 1 / (2 * (m : ℝ)) =
      1 - 1 / (2 * (m : ℝ)) := by ring
  rw [← Real.rpow_add_of_nonneg (mixedMoment_nonneg _ _ _ _) ha hb, he] at h'
  exact (repeated_integral_le hm s v u).trans h'

end
end RiemannGaussian.VinogradovMixedRepeated
