/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovProductEnergy
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Interpolation of actual mixed torus moments

Finite-measure Holder interpolation separates the mixed moment
integral |f|^(2k)*|F|^(2u) into the actual higher moment of F and the
reverse mixed moment integral |F|^2*|f|^(2ku). All compact-support and
Lp hypotheses follow from continuity, and zero values and u=1 are included.
The statement applies to arbitrary continuous complex functions, so both
original Riesz tails and actual conditioned block polynomials qualify.

This supplies the analytic interpolation in Wooley (2012), equation (6.8),
https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n3-p12-p.pdf.
It does not prove the remaining high-moment or singular-conditioning bounds.
-/

namespace RiemannGaussian.VinogradovInterpolation
noncomputable section
open scoped BigOperators Classical
open MeasureTheory UnitAddTorus

/-- Use the original normalized Haar measure on the circle. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Holder interpolation of actual nonnegative continuous torus functions, with all Lp conditions proved. -/
theorem integral_geometric_le {d : Type*} [Fintype d]
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (f g : UnitAddTorus d → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ theta, 0 ≤ f theta) (hg0 : ∀ theta, 0 ≤ g theta) :
    (∫ theta, f theta ^ t * g theta ^ (1 - t)) ≤
      (∫ theta, f theta) ^ t * (∫ theta, g theta) ^ (1 - t) := by
  have ht' : 0 < 1 - t := by linarith
  have hpq : (1 / t).HolderConjugate (1 / (1 - t)) := by
    constructor
    · simp
    · positivity
    · positivity
  have hfc := hf.rpow_const (fun _ => Or.inr ht.le)
  have hgc := hg.rpow_const (fun _ => Or.inr ht'.le)
  have he := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hpq
    (Filter.Eventually.of_forall (fun theta => Real.rpow_nonneg (hf0 theta) _))
    (Filter.Eventually.of_forall (fun theta => Real.rpow_nonneg (hg0 theta) _))
    (hfc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hgc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hff (theta) : (f theta ^ t) ^ (1 / t) = f theta := by
    rw [← Real.rpow_mul (hf0 theta), mul_one_div_cancel ht.ne', Real.rpow_one]
  have hgg (theta) : (g theta ^ (1 - t)) ^ (1 / (1 - t)) = g theta := by
    rw [← Real.rpow_mul (hg0 theta), mul_one_div_cancel ht'.ne', Real.rpow_one]
  simpa only [hff, hgg, one_div_one_div] using he

/-- The pointwise exponent identity retains zero values before applying integral Holder. -/
theorem interpolation_atom {k u : ℕ} (hu : 1 < u)
    {f g : ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g) :
    (g ^ (2 * u + 2)) ^ (1 - 1 / (u : ℝ)) *
      (g ^ 2 * f ^ (2 * k * u)) ^ (1 / (u : ℝ)) = f ^ (2 * k) * g ^ (2 * u) := by
  have huR : (1 : ℝ) < u := by exact_mod_cast hu
  have hu0 : (u : ℝ) ≠ 0 := by linarith
  have ht0 : 0 < 1 - 1 / (u : ℝ) := by
    have : 1 / (u : ℝ) < 1 := (div_lt_one (by linarith : (0 : ℝ) < u)).mpr huR
    linarith
  by_cases hg0 : g = 0
  · simp only [hg0, zero_pow (by omega : 2 * u + 2 ≠ 0),
      Real.zero_rpow ht0.ne', zero_mul, zero_pow (by omega : 2 * u ≠ 0), mul_zero]
  have hgpos : 0 < g := lt_of_le_of_ne hg (Ne.symm hg0)
  rw [Real.mul_rpow (sq_nonneg g) (pow_nonneg hf _)]
  simp_rw [← Real.rpow_natCast, ← Real.rpow_mul hg, ← Real.rpow_mul hf]
  have hfexp : ((2 * k * u : ℕ) : ℝ) * (1 / (u : ℝ)) = (2 * k : ℕ) := by
    push_cast
    field_simp
  rw [hfexp]
  rw [← mul_assoc, mul_comm _ (f ^ ((2 * k : ℕ) : ℝ)), ← Real.rpow_add hgpos]
  congr 2
  push_cast
  field_simp
  ring

/-- Interpolate the actual mixed energy into a higher tail moment and reverse mixed moment, including the endpoint u=1. -/
theorem mixed_interpolation {d : Type*} [Fintype d] {k u : ℕ} (hu : 0 < u)
    (f g : UnitAddTorus d → ℂ) (hf : Continuous f) (hg : Continuous g) :
    (∫ theta, ‖f theta‖ ^ (2 * k) * ‖g theta‖ ^ (2 * u)) ≤
      (∫ theta, ‖g theta‖ ^ (2 * u + 2)) ^ (1 - 1 / (u : ℝ)) *
        (∫ theta, ‖g theta‖ ^ 2 * ‖f theta‖ ^ (2 * k * u)) ^ (1 / (u : ℝ)) := by
  by_cases hu1 : u = 1
  · subst u
    simp only [Nat.cast_one, div_one, sub_self, Real.rpow_zero, one_mul,
      Real.rpow_one, mul_one]
    apply le_of_eq
    apply integral_congr_ae
    filter_upwards [] with theta
    exact mul_comm _ _
  have hu2 : 1 < u := by omega
  have huR : (1 : ℝ) < u := by exact_mod_cast hu2
  have huR0 : (0 : ℝ) < u := by linarith
  have ht : 0 < 1 - 1 / (u : ℝ) := by
    have := (div_lt_one huR0).mpr huR
    linarith
  have ht1 : 1 - 1 / (u : ℝ) < 1 := by linarith [one_div_pos.mpr huR0]
  have he := integral_geometric_le ht ht1
    (fun theta => ‖g theta‖ ^ (2 * u + 2))
    (fun theta => ‖g theta‖ ^ 2 * ‖f theta‖ ^ (2 * k * u))
    (hg.norm.pow _) ((hg.norm.pow 2).mul (hf.norm.pow _))
    (fun _ => by positivity) (fun _ => by positivity)
  simpa only [sub_sub_cancel, interpolation_atom hu2 (norm_nonneg _) (norm_nonneg _)] using he

/-- The actual finite maximum of the reverse mixed moments, retaining all original functions. -/
def reverseMaximum {ι d : Type*} [Fintype ι] [Nonempty ι] [Fintype d]
    (f : ι → UnitAddTorus d → ℂ) (g : UnitAddTorus d → ℂ) (k u : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i =>
    ∫ theta, ‖g theta‖ ^ 2 * ‖f i theta‖ ^ (2 * k * u))

/-- Every original mixed moment is bounded by the actual higher tail moment and actual reverse-moment maximum. -/
theorem mixed_le_higher_reverse_max {ι d : Type*} [Fintype ι] [Nonempty ι] [Fintype d]
    {k u : ℕ} (hu : 0 < u) (f : ι → UnitAddTorus d → ℂ) (g : UnitAddTorus d → ℂ)
    (hf : ∀ i, Continuous (f i)) (hg : Continuous g) (i : ι) :
    (∫ theta, ‖f i theta‖ ^ (2 * k) * ‖g theta‖ ^ (2 * u)) ≤
      (∫ theta, ‖g theta‖ ^ (2 * u + 2)) ^ (1 - 1 / (u : ℝ)) *
        reverseMaximum f g k u ^ (1 / (u : ℝ)) := by
  have hm : (∫ theta, ‖g theta‖ ^ 2 * ‖f i theta‖ ^ (2 * k * u)) ≤
      reverseMaximum f g k u := by
    exact Finset.le_sup' (fun j => ∫ theta, ‖g theta‖ ^ 2 * ‖f j theta‖ ^ (2 * k * u))
      (Finset.mem_univ i)
  apply (mixed_interpolation hu (f i) g (hf i) hg).trans
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (integral_nonneg (fun _ => by positivity)) hm (by positivity))
    (Real.rpow_nonneg (integral_nonneg (fun _ => by positivity)) _)

end
end RiemannGaussian.VinogradovInterpolation
