/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovInterpolation
import RiemannGaussian.VinogradovMeanValue

/-!
# Interpolation between actual Vinogradov moment orders

Holder interpolation on the original compact torus bounds every integer
order between two supplied moment orders. All continuity and integrability
conditions are discharged; zero values of the exponential sum and both
interpolation endpoints are included.

This is the interpolation used after Ford's Lemma 3.6 in the proof of
Theorem 3, arXiv:1910.08209v1. It supplies no unproved moment bound.
-/

namespace RiemannGaussian.VinogradovMomentInterpolation
noncomputable section
open MeasureTheory UnitAddTorus VinogradovMeanValue

/-- Use the normalized Haar measure of the original moment. -/
local instance unitCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The original circle measure has total mass one. -/
local instance unitCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Exact interpolation of the nonnegative power, including its zero value. -/
theorem power_interpolation {a b s : ℕ} {t x : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hx : 0 ≤ x)
    (hs : (s : ℝ) = (1 - t) * (a : ℝ) + t * (b : ℝ)) :
    (x ^ (2 * a)) ^ (1 - t) * (x ^ (2 * b)) ^ t = x ^ (2 * s) := by
  rw [← Real.rpow_natCast x (2 * a), ← Real.rpow_natCast x (2 * b),
    ← Real.rpow_mul hx, ← Real.rpow_mul hx,
    ← Real.rpow_add_of_nonneg hx (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr ht1))
      (mul_nonneg (Nat.cast_nonneg _) ht)]
  have he : ((2 * a : ℕ) : ℝ) * (1 - t) + ((2 * b : ℕ) : ℝ) * t = (2 * s : ℕ) := by
    push_cast
    nlinarith only [hs]
  rw [he, Real.rpow_natCast]

/-- The literal torus moments are log-convex in their integer order. -/
theorem moment_geometric_le {d ι : Type*} [Fintype d] [Fintype ι]
    {a b s : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : (s : ℝ) = (1 - t) * (a : ℝ) + t * (b : ℝ))
    (v : ι → d → ℤ) :
    moment s v ≤ moment a v ^ (1 - t) * moment b v ^ t := by
  by_cases ht0 : t = 0
  · have hsa : s = a := by
      have hh : (s : ℝ) = a := by simpa only [ht0, sub_zero, one_mul, zero_mul, add_zero] using hs
      exact_mod_cast hh
    subst s
    simp [ht0]
  by_cases htone : t = 1
  · have hsb : s = b := by
      have hh : (s : ℝ) = b := by simpa only [htone, sub_self, zero_mul, one_mul, zero_add] using hs
      exact_mod_cast hh
    subst s
    simp [htone]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  have htlt : t < 1 := lt_of_le_of_ne ht1 htone
  have hh := VinogradovInterpolation.integral_geometric_le
    (show 0 < 1 - t by linarith) (show 1 - t < 1 by linarith)
    (fun theta : UnitAddTorus d => ‖∑ i, mFourier (v i) theta‖ ^ (2 * a))
    (fun theta : UnitAddTorus d => ‖∑ i, mFourier (v i) theta‖ ^ (2 * b))
    (by fun_prop) (by fun_prop) (fun _ => by positivity) (fun _ => by positivity)
  simpa only [sub_sub_cancel, power_interpolation ht ht1 (norm_nonneg _) hs, moment] using hh

/-- Specialization to the original complete equal-power-sum system. -/
theorem meanValue_geometric_le {a b s k P : ℕ} {t : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : (s : ℝ) = (1 - t) * (a : ℝ) + t * (b : ℝ)) :
    meanValue s k P ≤ meanValue a k P ^ (1 - t) * meanValue b k P ^ t :=
  moment_geometric_le ht ht1 hs _

/-- Supplied estimates for two actual moments interpolate with their exact
coefficients and affine power exponent. -/
theorem meanValue_bound {a b s k P : ℕ} {t Ca Cb Ea Eb : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : (s : ℝ) = (1 - t) * (a : ℝ) + t * (b : ℝ))
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hP : 1 ≤ P)
    (ha : meanValue a k P ≤ Ca * (P : ℝ) ^ Ea)
    (hb : meanValue b k P ≤ Cb * (P : ℝ) ^ Eb) :
    meanValue s k P ≤ Ca ^ (1 - t) * Cb ^ t *
      (P : ℝ) ^ ((1 - t) * Ea + t * Eb) := by
  have hPa : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hma : 0 ≤ meanValue a k P := integral_nonneg (fun _ => by positivity)
  have hmb : 0 ≤ meanValue b k P := integral_nonneg (fun _ => by positivity)
  refine (meanValue_geometric_le ht ht1 hs).trans ?_
  have hh := mul_le_mul (Real.rpow_le_rpow hma ha (sub_nonneg.mpr ht1))
    (Real.rpow_le_rpow hmb hb ht) (Real.rpow_nonneg hmb _)
    (Real.rpow_nonneg (mul_nonneg hCa (Real.rpow_nonneg hPa.le _)) _)
  refine hh.trans_eq ?_
  rw [Real.mul_rpow hCa (Real.rpow_nonneg hPa.le _),
    Real.mul_rpow hCb (Real.rpow_nonneg hPa.le _),
    ← Real.rpow_mul hPa.le, ← Real.rpow_mul hPa.le,
    mul_mul_mul_comm, ← Real.rpow_add hPa]
  congr 2
  ring

end
end RiemannGaussian.VinogradovMomentInterpolation
