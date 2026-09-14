/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovImprovedNormalization

/-!
# Higher-moment bounds for both actual conditioned blocks

Continuous Holder bounds the original two signed blocks at their actual
padded quotients. An exact identity retains both scale exponents before
any uniform profile estimate. The independently proved first global
exponent supplies the actual moment premises in the terminal upper bound.
This alone gives no decay of the normalized conditioned energy.
-/

namespace RiemannGaussian.VinogradovConditionedUpper
noncomputable section
open scoped Classical BigOperators
open UnitAddTorus MeasureTheory
open VinogradovMeanValue VinogradovPartitionEnergy VinogradovProductEnergy
open VinogradovNonsingularConditioning VinogradovConditioningRemainder
open VinogradovConditioningPowerSaving VinogradovCongruencingScaling
open VinogradovImprovedNormalization VinogradovRemainderScaling

/-- The original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle Haar measure has mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Both actual signed conditioned blocks have the same two-quotient homogeneous upper bound, retaining their original colours and residues. -/
theorem conditioned_le_higher_moments {p k a b xi eta X u : ℕ} [NeZero p]
    (hu : 0 < u) (colourA colourB : Fin k → Bool) :
    conditionedMoment p k a b xi eta X u colourA colourB ≤
      meanValue ((u + 1) * k) k (X / p ^ a + 1) ^ (1 / ((u + 1 : ℕ) : ℝ)) *
      meanValue ((u + 1) * k) k (X / p ^ b + 1) ^ (1 - 1 / ((u + 1 : ℕ) : ℝ)) := by
  let A := polynomial (blockFrequency (p := p) (a := a) (xi := xi) (X := X) colourA) (fun _ => 1)
  let B := polynomial (blockFrequency (p := p) (a := b) (xi := eta) (X := X) colourB) (fun _ => 1)
  have hA : Continuous A := continuous_polynomial _ _
  have hB : Continuous B := continuous_polynomial _ _
  have huR : (1 : ℝ) < ((u + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < u + 1)
  have hpos : 0 < 1 / ((u + 1 : ℕ) : ℝ) := by positivity
  have hlt : 1 / ((u + 1 : ℕ) : ℝ) < 1 := (div_lt_one (by linarith)).mpr huR
  have he := VinogradovInterpolation.integral_geometric_le hpos hlt
    (fun theta => ‖A theta‖ ^ (2 * (u + 1)))
    (fun theta => ‖B theta‖ ^ (2 * (u + 1)))
    (hA.norm.pow _) (hB.norm.pow _) (fun _ => by positivity) (fun _ => by positivity)
  have hid (theta : UnitAddTorus (Fin k)) :=
    separated_atom (k := 1) hu (norm_nonneg (A theta)) (norm_nonneg (B theta))
  simp only [one_mul, mul_one] at hid
  simp_rw [hid] at he
  apply he.trans
  apply mul_le_mul
  · exact Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity))
      (VinogradovConditionedHigherMoment.conditioned_moment_le colourA) hpos.le
  · exact Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity))
      (VinogradovConditionedHigherMoment.conditioned_moment_le colourB) (by linarith)
  · exact Real.rpow_nonneg (integral_nonneg (fun _ => by positivity)) _
  · exact Real.rpow_nonneg (by rw [meanValue_eq_count]; positivity) _

/-- Pay any two proved homogeneous scale bounds in both actual conditioned blocks. -/
theorem conditioned_le_scaled_moments {p k a b xi eta X u : ℕ} [NeZero p]
    (hu : 0 < u) {C lam : ℝ} (hC : 1 ≤ C)
    (hA : meanValue ((u + 1) * k) k (X / p ^ a + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ a) ^ lam)
    (hB : meanValue ((u + 1) * k) k (X / p ^ b + 1) ≤ C * ((X : ℝ) / (p : ℝ) ^ b) ^ lam)
    (colourA colourB : Fin k → Bool) :
    conditionedMoment p k a b xi eta X u colourA colourB ≤ C *
      (((X : ℝ) / (p : ℝ) ^ a) ^ (lam / ((u + 1 : ℕ) : ℝ)) *
       ((X : ℝ) / (p : ℝ) ^ b) ^ (lam * u / ((u + 1 : ℕ) : ℝ))) := by
  have huR : (1 : ℝ) < ((u + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < u + 1)
  have ht : 0 ≤ 1 - 1 / ((u + 1 : ℕ) : ℝ) := by
    have h := (div_lt_one (by linarith : (0 : ℝ) < ((u + 1 : ℕ) : ℝ))).mpr huR
    linarith
  have hCpos : 0 < C := by linarith
  apply (conditioned_le_higher_moments (p := p) (a := a) (b := b) (xi := xi)
    (eta := eta) (X := X) hu colourA colourB).trans
  calc
    _ ≤ (C * ((X : ℝ) / (p : ℝ) ^ a) ^ lam) ^ (1 / ((u + 1 : ℕ) : ℝ)) *
        (C * ((X : ℝ) / (p : ℝ) ^ b) ^ lam) ^ (1 - 1 / ((u + 1 : ℕ) : ℝ)) := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (by rw [meanValue_eq_count]; positivity) hA (by positivity)
      · exact Real.rpow_le_rpow (by rw [meanValue_eq_count]; positivity) hB ht
      · exact Real.rpow_nonneg (by rw [meanValue_eq_count]; positivity) _
      · positivity
    _ = _ := by
      rw [common_power_mean hCpos (by positivity) (by positivity)]
      have he : lam * (1 - 1 / ((u + 1 : ℕ) : ℝ)) = lam * u / ((u + 1 : ℕ) : ℝ) := by
        push_cast
        field_simp
        ring
      rw [he]
      simp only [mul_one_div]

/-- At every real exponent the complete two-scale cost differs from its source normalization by one explicit power of the residue-scale gap. -/
theorem conditioned_scale_identity {x P : ℝ} (hx : 0 < x) (hP : 0 < P)
    (k u a b lam : ℝ) (hu : u + 1 ≠ 0) :
    (x / P ^ a) ^ (lam / (u + 1)) * (x / P ^ b) ^ (lam * u / (u + 1)) =
      momentScale x P k u a b lam * P ^ (u * (2 * k - lam / (u + 1)) * (b - a)) := by
  unfold momentScale
  simp_rw [VinogradovRemainderScaling.quotient_power_exp hx hP]
  simp only [Real.rpow_def_of_pos hP, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- Every actual normalized signed conditioned energy has an independent scale-gap upper bound at the proved improved exponent. -/
theorem exists_normalized_conditioned_upper (k u : ℕ) (hk : 2 ≤ k) (hu : k ≤ u) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ N₀ : ℕ, ∀ (p a b xi eta X : ℕ) [NeZero p],
      a ≤ b → p ^ b ≤ X → N₀ ≤ X / p ^ b + 1 → ∀ colourA colourB : Fin k → Bool,
      let lam : ℝ := (((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))
      conditionedMoment p k a b xi eta X u colourA colourB / momentScale X p k u a b lam ≤
        C * (p : ℝ) ^ ((u : ℝ) * (2 * k - lam / ((u : ℝ) + 1)) * ((b : ℝ) - a)) := by
  obtain ⟨C, hC, N₀, hbudget⟩ := exists_improved_rounded_budget k u hk hu
  refine ⟨C, hC, N₀, ?_⟩
  intro p a b xi eta X inst hab hX hN colourA colourB
  let lam : ℝ := (((k * (2 * u + 1) : ℕ) : ℝ) - 1 / (3 * (k : ℝ)))
  have hp0 : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hXR : (0 : ℝ) < X := by exact_mod_cast (Nat.pow_pos hp0).trans_le hX
  have hpow : p ^ a ≤ p ^ b := Nat.pow_le_pow_right (by omega) hab
  have hquot : X / p ^ b ≤ X / p ^ a :=
    (Nat.le_div_iff_mul_le (Nat.pow_pos hp0)).mpr
      ((Nat.mul_le_mul_left _ hpow).trans (Nat.div_mul_le_self X (p ^ b)))
  have hJa := hbudget p a X hp0 (hpow.trans hX) (by omega)
  have hJb := hbudget p b X hp0 hX hN
  have he := conditioned_le_scaled_moments (xi := xi) (eta := eta) (by omega : 0 < u) hC hJa hJb colourA colourB
  have hid := conditioned_scale_identity hXR hpR (k : ℝ) (u : ℝ) (a : ℝ) (b : ℝ) lam (by positivity)
  simp only [Real.rpow_natCast] at hid
  simp only [Nat.cast_add, Nat.cast_one] at he
  rw [hid] at he
  apply (div_le_iff₀ (momentScale_pos hXR hpR _ _ _ _ _)).mpr
  exact he.trans_eq (by ring)

end
end RiemannGaussian.VinogradovConditionedUpper
