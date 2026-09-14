/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovCrossMoment

/-!
# The moment deficit from a repeated coordinate

Probability-space Holder retains a constant third factor when the two
positive exponents sum to less than one. Exact frequency-dilation invariance
then bounds the repeated-coordinate integral by J_r^(1-1/(2r)), without
assuming any numerical upper bound for the original moment.
-/

namespace RiemannGaussian.VinogradovRepeatedMoment.Holder
noncomputable section
open MeasureTheory UnitAddTorus
/-- The original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Probability mass supplies the missing Holder factor for a product whose two positive exponents sum to less than one. -/
theorem integral_subunit_product_le {d : Type*} [Fintype d] {t s : ℝ}
    (ht : 0 < t) (hs : 0 < s) (hts : t + s < 1)
    (A B : UnitAddTorus d → ℝ) (hA : Continuous A) (hB : Continuous B)
    (hA0 : ∀ theta, 0 ≤ A theta) (hB0 : ∀ theta, 0 ≤ B theta) :
    (∫ theta, A theta ^ t * B theta ^ s) ≤
      (∫ theta, A theta) ^ t * (∫ theta, B theta) ^ s := by
  have hsum : 0 < t + s := by linarith
  have hfrac : 0 < t / (t + s) := div_pos ht hsum
  have hfrac1 : t / (t + s) < 1 := (div_lt_one hsum).mpr (by linarith)
  have hcomp : 1 - t / (t + s) = s / (t + s) := by field_simp; ring
  let F (theta : UnitAddTorus d) := A theta ^ (t / (t + s)) * B theta ^ (s / (t + s))
  have hF : Continuous F :=
    (hA.rpow_const (fun _ => Or.inr hfrac.le)).mul
      (hB.rpow_const (fun _ => Or.inr (div_pos hs hsum).le))
  have hF0 (theta) : 0 ≤ F theta :=
    mul_nonneg (Real.rpow_nonneg (hA0 theta) _) (Real.rpow_nonneg (hB0 theta) _)
  have hinner := VinogradovInterpolation.integral_geometric_le hfrac hfrac1 A B hA hB hA0 hB0
  rw [hcomp] at hinner
  have houter := VinogradovInterpolation.integral_geometric_le hsum hts F (fun _ => 1)
    hF continuous_const hF0 (fun _ => zero_le_one)
  have houter' : (∫ theta, F theta ^ (t + s)) ≤ (∫ theta, F theta) ^ (t + s) := by
    simpa using houter
  have he (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      (a ^ (t / (t + s)) * b ^ (s / (t + s))) ^ (t + s) = a ^ t * b ^ s := by
    rw [Real.mul_rpow (Real.rpow_nonneg ha _) (Real.rpow_nonneg hb _),
      ← Real.rpow_mul ha, ← Real.rpow_mul hb,
      div_mul_cancel₀ t hsum.ne', div_mul_cancel₀ s hsum.ne']
  have hid (theta) : F theta ^ (t + s) = A theta ^ t * B theta ^ s :=
    he _ _ (hA0 theta) (hB0 theta)
  simp_rw [hid] at houter'
  apply houter'.trans
  have hi := Real.rpow_le_rpow (integral_nonneg hF0) hinner hsum.le
  simpa only [he _ _ (integral_nonneg hA0) (integral_nonneg hB0)] using hi

/-- The repeated-coordinate product receives both actual higher moments with its full one-factor deficit. -/
theorem repeated_factor_bound {d : Type*} [Fintype d] {q : ℝ} (hq : 2 < q)
    (A B : UnitAddTorus d → ℂ) (hA : Continuous A) (hB : Continuous B) :
    (∫ theta, ‖A theta‖ * ‖B theta‖ ^ (q - 2)) ≤
      (∫ theta, ‖A theta‖ ^ q) ^ (1 / q) *
      (∫ theta, ‖B theta‖ ^ q) ^ ((q - 2) / q) := by
  have hq0 : 0 < q := by linarith
  have ht : 0 < 1 / q := by positivity
  have hs : 0 < (q - 2) / q := div_pos (by linarith) hq0
  have hsum : 1 / q + (q - 2) / q < 1 := by
    rw [← add_div]
    apply (div_lt_one hq0).mpr
    linarith
  have he := integral_subunit_product_le ht hs hsum
    (fun theta => ‖A theta‖ ^ q) (fun theta => ‖B theta‖ ^ q)
    (hA.norm.rpow_const (fun _ => Or.inr hq0.le))
    (hB.norm.rpow_const (fun _ => Or.inr hq0.le))
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hr (a : ℂ) (c : ℝ) : (‖a‖ ^ q) ^ c = ‖a‖ ^ (q * c) :=
    (Real.rpow_mul (norm_nonneg a) q c).symm
  have h1 : q * (1 / q) = 1 := mul_one_div_cancel hq0.ne'
  have h2 : q * ((q - 2) / q) = q - 2 := by field_simp
  simp_rw [hr, h1, h2, Real.rpow_one] at he
  exact he

/-- Equal actual higher moments turn the repeated-coordinate estimate into a strict exponent deficit, including a zero common moment. -/
theorem repeated_factor_bound_of_equal_moment {d : Type*} [Fintype d] {q : ℝ} (hq : 2 < q)
    (A B : UnitAddTorus d → ℂ) (hA : Continuous A) (hB : Continuous B)
    (heq : (∫ theta, ‖A theta‖ ^ q) = ∫ theta, ‖B theta‖ ^ q) :
    (∫ theta, ‖A theta‖ * ‖B theta‖ ^ (q - 2)) ≤
      (∫ theta, ‖B theta‖ ^ q) ^ (1 - 1 / q) := by
  have hq0 : 0 < q := by linarith
  have hJ : 0 ≤ ∫ theta, ‖B theta‖ ^ q := integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hsum : 1 / q + (q - 2) / q = 1 - 1 / q := by field_simp; ring
  have he := repeated_factor_bound hq A B hA hB
  rw [heq, ← Real.rpow_add_of_nonneg hJ (by positivity) (div_nonneg (by linarith) hq0.le), hsum] at he
  exact he

end
end RiemannGaussian.VinogradovRepeatedMoment.Holder

namespace RiemannGaussian.VinogradovRepeatedMoment
noncomputable section
open MeasureTheory UnitAddTorus
open VinogradovMeanValue VinogradovPartitionEnergy
open VinogradovCrossMoment VinogradovRepeatedMoment.Holder
/-- The original normalized circle Haar measure. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The literal doubled-frequency term forced by a repeated coordinate has a proved deficit relative to the actual homogeneous moment. -/
theorem repeated_coordinate_integral_le {ι d : Type*} [Fintype ι] [Fintype d]
    {r : ℕ} (hr : 2 ≤ r) (v : ι → d → ℤ) :
    (∫ theta : UnitAddTorus d,
      ‖polynomial (fun i j => (2 : ℤ) * v i j) (fun _ => 1) theta‖ *
        ‖polynomial v (fun _ => 1) theta‖ ^ (2 * r - 2)) ≤
      moment r v ^ (1 - 1 / ((2 * r : ℕ) : ℝ)) := by
  have hq : (2 : ℝ) < ((2 * r : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 < 2 * r)
  have heq : (∫ theta : UnitAddTorus d,
      ‖polynomial (fun i j => (2 : ℤ) * v i j) (fun _ => 1) theta‖ ^ ((2 * r : ℕ) : ℝ)) =
      ∫ theta : UnitAddTorus d, ‖polynomial v (fun _ => 1) theta‖ ^ ((2 * r : ℕ) : ℝ) := by
    simpa only [Real.rpow_natCast] using weighted_even_moment_dilation r 2 (by norm_num) v (fun _ => 1)
  have he := repeated_factor_bound_of_equal_moment hq
    (polynomial (fun i j => (2 : ℤ) * v i j) (fun _ => 1)) (polynomial v (fun _ => 1))
    (continuous_polynomial _ _) (continuous_polynomial _ _) heq
  have hextype : ((2 * r - 2 : ℕ) : ℝ) = ((2 * r : ℕ) : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * r)]
    norm_num
  simpa only [← hextype, Real.rpow_natCast, polynomial, one_mul, moment] using he

end
end RiemannGaussian.VinogradovRepeatedMoment
