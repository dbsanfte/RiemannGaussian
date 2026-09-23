/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovCrossMoment

/-!
# Actual mixed moments and bounded boundary masks

These are mixed moments of two literal finite integer-frequency sums.
Their exact tuple count gives a majorant for bounded complex masks. Holder
then bounds the intermediate power needed in classical differencing by
the complete mixed count at one lower tuple order and the original tail
moment. In particular no pointwise comparison of oscillating sums is used.
-/

namespace RiemannGaussian.VinogradovMixedMoments
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory UnitAddTorus VinogradovMeanValue VinogradovShiftedMoment
open VinogradovPartitionEnergy VinogradovProductEnergy VinogradovCrossMoment

/-- The original normalized Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Both entire frequency vectors remain in the mixed moment. -/
def mixedMoment {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) : ℝ :=
  ∫ theta : UnitAddTorus d,
    ‖polynomial v (fun _ => 1) theta‖ ^ (2 * r) *
      ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)

/-- The complete original configuration frequency. -/
def configurationFrequency {ι κ d : Type*} (r s : ℕ)
    (v : ι → d → ℤ) (u : κ → d → ℤ)
    (x : (Fin r → ι) × (Fin s → κ)) : d → ℤ :=
  tupleFrequency r v x.1 + tupleFrequency s u x.2

/-- The weighted tuple polynomial is the exact power of the original sum. -/
theorem tuple_polynomial {ι d : Type*} [Fintype ι] [Fintype d]
    (r : ℕ) (v : ι → d → ℤ) (a : ι → ℂ) (theta : UnitAddTorus d) :
    polynomial (tupleFrequency r v) (tupleWeight r a) theta =
      polynomial v a theta ^ r := (weighted_power_expansion r v a theta).symm

/-- Form the full weighted configuration before taking the mixed norm. -/
theorem configuration_polynomial {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) (a : ι → ℂ) (b : κ → ℂ)
    (theta : UnitAddTorus d) :
    polynomial (configurationFrequency r s v u)
      (fun x => tupleWeight r a x.1 * tupleWeight s b x.2) theta =
      polynomial v a theta ^ r * polynomial u b theta ^ s := by
  change polynomial (fun x : (Fin r → ι) × (Fin s → κ) =>
    tupleFrequency r v x.1 + tupleFrequency s u x.2) _ theta = _
  rw [polynomial_prod, tuple_polynomial, tuple_polynomial]

/-- The full mixed moment is an actual homogeneous energy, including
all correlations between its two tuple families. -/
theorem mixedMoment_eq_energy {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) :
    mixedMoment r s v u = ∫ theta : UnitAddTorus d,
      ‖polynomial (configurationFrequency r s v u) (fun _ => 1) theta‖ ^ 2 := by
  unfold mixedMoment
  apply integral_congr_ae
  filter_upwards [] with theta
  have h := configuration_polynomial r s v u (fun _ => 1) (fun _ => 1) theta
  simp only [tupleWeight, Finset.prod_const_one, one_mul] at h
  rw [h, norm_mul, norm_pow, norm_pow, mul_pow, ← pow_mul, ← pow_mul,
    Nat.mul_comm r 2, Nat.mul_comm s 2]

/-- The mixed integral counts the literal complete frequency equations. -/
theorem mixedMoment_eq_count {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) :
    mixedMoment r s v u = differenceCount (configurationFrequency r s v u) 0 := by
  rw [mixedMoment_eq_energy]
  have h := weightedShift_one (configurationFrequency r s v u) 0
  rw [weightedShift_zero] at h
  simpa only [polynomial, one_mul, Complex.ofReal_re, Complex.natCast_re] using
    congrArg Complex.re h

/-- The actual mixed count is nonnegative. -/
theorem mixedMoment_nonneg {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) : 0 ≤ mixedMoment r s v u :=
  integral_nonneg (fun _ => by positivity)

/-- Arbitrary bounded complex masks, including all endpoint cuts, are
paid by the complete mixed count after the even moment is formed. -/
theorem weighted_mixedMoment_le {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    (r s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ) (a : ι → ℂ) (b : κ → ℂ)
    (ha : ∀ i, ‖a i‖ ≤ 1) (hb : ∀ j, ‖b j‖ ≤ 1) :
    (∫ theta : UnitAddTorus d, ‖polynomial v a theta‖ ^ (2 * r) *
      ‖polynomial u b theta‖ ^ (2 * s)) ≤ mixedMoment r s v u := by
  let V := configurationFrequency r s v u
  let W := fun x : (Fin r → ι) × (Fin s → κ) =>
    tupleWeight r a x.1 * tupleWeight s b x.2
  have hW (x) : ‖W x‖ ≤ 1 := by
    rw [show W x = tupleWeight r a x.1 * tupleWeight s b x.2 from rfl, norm_mul]
    exact mul_le_one₀ (tupleWeight_norm_le_one r a ha _) (norm_nonneg _)
      (tupleWeight_norm_le_one s b hb _)
  have he : (∫ theta : UnitAddTorus d, ‖polynomial V W theta‖ ^ 2) ≤
      ∫ theta : UnitAddTorus d, ‖polynomial V (fun _ => 1) theta‖ ^ 2 := by
    simpa only [polynomial, one_mul, moment, mul_one] using weighted_moment_le 1 V W hW
  rw [mixedMoment_eq_energy]
  simpa only [V, W, configuration_polynomial, norm_mul,
    norm_pow, mul_pow, ← pow_mul, Nat.mul_comm r 2, Nat.mul_comm s 2] using he

private theorem interpolation_atom {a w : ℝ} (ha : 0 ≤ a) (hw : 0 ≤ w)
    {m : ℕ} (hm : 2 ≤ m) :
    (a ^ (2 * (m - 1)) * w) ^ ((m : ℝ) / (2 * ((m : ℝ) - 1))) *
        w ^ (1 - (m : ℝ) / (2 * ((m : ℝ) - 1))) = a ^ m * w := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have ht : 0 < (m : ℝ) / (2 * ((m : ℝ) - 1)) := by positivity
  by_cases hw0 : w = 0
  · simp only [hw0, mul_zero, Real.zero_rpow ht.ne', zero_mul]
  have hwp : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  rw [Real.mul_rpow (pow_nonneg ha _) hw, mul_assoc, ← Real.rpow_add hwp]
  rw [show (m : ℝ) / (2 * ((m : ℝ) - 1)) +
      (1 - (m : ℝ) / (2 * ((m : ℝ) - 1))) = 1 by ring, Real.rpow_one]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
  have he : ((2 * (m - 1) : ℕ) : ℝ) * ((m : ℝ) / (2 * ((m : ℝ) - 1))) = m := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    field_simp [hd.ne']
    ring
  rw [he, Real.rpow_natCast]

/-- The actual intermediate difference power is controlled by the
complete mixed moment one tuple order lower and the original tail moment.
All endpoint masks remain inside the sum until the even-moment majorant. -/
theorem intermediate_power_le {ι κ d : Type*} [Fintype ι] [Fintype κ] [Fintype d]
    {m : ℕ} (hm : 2 ≤ m) (s : ℕ) (v : ι → d → ℤ) (u : κ → d → ℤ)
    (a : ι → ℂ) (ha : ∀ i, ‖a i‖ ≤ 1) :
    (∫ theta : UnitAddTorus d, ‖polynomial v a theta‖ ^ m *
      ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)) ≤
      mixedMoment (m - 1) s v u ^ ((m : ℝ) / (2 * ((m : ℝ) - 1))) *
        moment s u ^ (1 - (m : ℝ) / (2 * ((m : ℝ) - 1))) := by
  by_cases hm2 : m = 2
  · subst m
    norm_num only [Nat.cast_ofNat, sub_self, show (2 : ℝ) - 1 = 1 by norm_num,
      mul_one, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one, Real.rpow_zero]
    simpa using weighted_mixedMoment_le 1 s v u a (fun _ => 1) ha (by simp)
  have hmR : (2 : ℝ) < m := by exact_mod_cast (show 2 < m by omega)
  have hd : (0 : ℝ) < (m : ℝ) - 1 := by linarith
  have ht : 0 < (m : ℝ) / (2 * ((m : ℝ) - 1)) := by positivity
  have ht1 : (m : ℝ) / (2 * ((m : ℝ) - 1)) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  have he := VinogradovInterpolation.integral_geometric_le ht ht1
    (fun theta : UnitAddTorus d => ‖polynomial v a theta‖ ^ (2 * (m - 1)) *
      ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s))
    (fun theta : UnitAddTorus d => ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s))
    (((continuous_polynomial v a).norm.pow _).mul
      ((continuous_polynomial u (fun _ => 1)).norm.pow _))
    ((continuous_polynomial u (fun _ => 1)).norm.pow _)
    (fun _ => by positivity) (fun _ => by positivity)
  have hatom (theta : UnitAddTorus d) := interpolation_atom
    (norm_nonneg (polynomial v a theta))
    (show 0 ≤ ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s) by positivity) hm
  simp_rw [hatom] at he
  have htail : (∫ theta : UnitAddTorus d,
      ‖polynomial u (fun _ => 1) theta‖ ^ (2 * s)) = moment s u := by
    simp only [polynomial, one_mul, moment]
  rw [htail] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_right
  · exact Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity))
      (weighted_mixedMoment_le (m - 1) s v u a (fun _ => 1) ha (by simp)) ht.le
  · exact Real.rpow_nonneg (integral_nonneg (fun _ => by positivity)) _

end
end RiemannGaussian.VinogradovMixedMoments
