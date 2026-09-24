/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovMomentInterpolation
import RiemannGaussian.VinogradovFordOrderBudget

/-!
# Ford's quantitative moment bound at every published order

The actual mean-value integral receives Holder interpolation between the
adjacent multiples of k. The explicit coefficient and defect are exactly
those in the k>=1000 part of Ford's Theorem 3, arXiv:1910.08209v1.

The only unproved arithmetic input is still `ShortPrimeSupply k (3/50)`.
This module does not assert that input, the lower-degree numerical tables,
the incomplete-system estimates, or a zeta zero-free region.
-/

namespace RiemannGaussian.VinogradovFordAllOrders
noncomputable section
open VinogradovMeanValue VinogradovFordScales VinogradovFordOrderBudget

/-- The proved multiple-order theorem in the exact paper-index envelopes. -/
theorem multiple_moment_bound {k J : ℕ} (hk : 1000 ≤ k)
    (hlower : 2 * k ≤ J + 1)
    (hupper : (J : ℝ) + 1 ≤ ((k : ℝ) / 2) *
      (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1)
    (hsupply : VinogradovFordGlobalStep.ShortPrimeSupply k (3 / 50))
    {P : ℕ} (hP : 1 ≤ P) :
    meanValue ((J + 1) * k) k P ≤ stepCoefficient k ((J : ℝ) + 1) *
      (P : ℝ) ^ sourceExponent k ((J + 1) * k) (stepDefect k ((J : ℝ) + 1)) := by
  have he : stepCoefficient k ((J : ℝ) + 1) =
      (k : ℝ) ^ ((411 / 200) * (k : ℝ) ^ 3 -
        (591 / 100) * (k : ℝ) ^ 2 + 3 * ((J : ℝ) + 1) * (k : ℝ)) *
      (53 / 50 : ℝ) ^ (((J : ℝ) + 1) * (k : ℝ) ^ 2 +
        2 * (k : ℝ) * ((J : ℝ) ^ 2 + (J : ℝ)) - (48639 / 5000) * (k : ℝ) ^ 3) := by
    unfold stepCoefficient
    congr 1
    congr 1
    ring
  rw [he]
  exact VinogradovFordClosedCoefficient.selected_moment_closed hk hlower hupper hsupply hP

/-- Every intermediate integer order receives the original closed estimate. -/
theorem intermediate_moment_bound {k J s : ℕ} (hk : 1000 ≤ k)
    (hlower : 2 * k ≤ J + 1)
    (hupper : (J : ℝ) + 2 ≤ ((k : ℝ) / 2) *
      (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1)
    (hsupply : VinogradovFordGlobalStep.ShortPrimeSupply k (3 / 50))
    {P : ℕ} (hP : 1 ≤ P) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hs : (s : ℝ) = ((J : ℝ) + 1 + t) * (k : ℝ)) :
    meanValue s k P ≤ coefficient k (s : ℝ) *
      (P : ℝ) ^ sourceExponent k s (defect k (s : ℝ)) := by
  have h0 := multiple_moment_bound hk hlower
    (show (J : ℝ) + 1 ≤ ((k : ℝ) / 2) * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1 by linarith)
    hsupply hP
  have h1 := multiple_moment_bound (J := J + 1) hk (by omega : 2 * k ≤ J + 1 + 1)
    (by push_cast; linarith) hsupply hP
  have horder : (s : ℝ) = (1 - t) * (((J + 1) * k : ℕ) : ℝ) +
      t * (((J + 1 + 1) * k : ℕ) : ℝ) := by
    rw [hs]
    push_cast
    ring
  have hh := VinogradovMomentInterpolation.meanValue_bound ht ht1 horder
    (stepCoefficient_pos (by omega : 0 < k) _).le
    (stepCoefficient_pos (by omega : 0 < k) _).le hP h0 h1
  have hcoeff : stepCoefficient k ((J : ℝ) + 1) ^ (1 - t) *
      stepCoefficient k ((J + 1 : ℕ) + 1) ^ t ≤ coefficient k (s : ℝ) := by
    rw [hs]
    convert coefficient_interpolation (n := (J : ℝ) + 1) (t := t) hk (by positivity) using 1
    push_cast
    rfl
  have hdef := defect_interpolation hk ((J : ℝ) + 1) ht ht1
  have hexp : (1 - t) * sourceExponent k ((J + 1) * k) (stepDefect k ((J : ℝ) + 1)) +
      t * sourceExponent k ((J + 1 + 1) * k) (stepDefect k ((J + 1 : ℕ) + 1)) ≤
        sourceExponent k s (defect k (s : ℝ)) := by
    unfold sourceExponent
    push_cast at hdef ⊢
    rw [hs]
    nlinarith only [hdef]
  refine hh.trans (mul_le_mul hcoeff ?_ (by positivity)
    (coefficient_pos (by omega : 0 < k) _).le)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hP) hexp

/-- Ford Theorem 3 on its full k>=1000 order interval, with the published
constants and all positive integer endpoints. Dense short-prime supply
remains explicit; no moment or interpolation estimate is assumed. -/
theorem published_moment_bound {k s : ℕ} (hk : 1000 ≤ k)
    (hlower : 2 * k ^ 2 ≤ s)
    (hupper : (s : ℝ) ≤ ((k : ℝ) ^ 2 / 2) *
      (1 / 2 + Real.log (3 * (k : ℝ) / 8)))
    (hsupply : VinogradovFordGlobalStep.ShortPrimeSupply k (3 / 50))
    {P : ℕ} (hP : 1 ≤ P) :
    meanValue s k P ≤ coefficient k (s : ℝ) *
      (P : ℝ) ^ sourceExponent k s (defect k (s : ℝ)) := by
  have hkN : 0 < k := by omega
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hkN
  have hn : 2 * k ≤ s / k := (Nat.le_div_iff_mul_le hkN).mpr (by nlinarith)
  have hn1 : 1 ≤ s / k := by omega
  have hj : s / k - 1 + 1 = s / k := Nat.sub_add_cancel hn1
  have hjR : ((s / k - 1 : ℕ) : ℝ) + 1 = (s / k : ℕ) := by exact_mod_cast hj
  have hdiv : ((s / k : ℕ) : ℝ) * (k : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self s k
  have hquotient : ((s / k : ℕ) : ℝ) ≤ ((k : ℝ) / 2) *
      (1 / 2 + Real.log (3 * (k : ℝ) / 8)) := by
    apply (mul_le_mul_iff_right₀ hkpos).mp
    nlinarith only [hdiv, hupper]
  have ht0 : (0 : ℝ) ≤ (s % k : ℕ) / (k : ℝ) := by positivity
  have ht1 : ((s % k : ℕ) : ℝ) / (k : ℝ) ≤ 1 := by
    apply (div_le_one hkpos).mpr
    exact_mod_cast (Nat.mod_lt s hkN).le
  apply intermediate_moment_bound (J := s / k - 1) hk (by omega)
    (by linarith) hsupply hP ht0 ht1
  rw [hjR, add_mul, div_mul_cancel₀ _ hkpos.ne']
  have he : ((s % k : ℕ) : ℝ) + (k : ℝ) * ((s / k : ℕ) : ℝ) = (s : ℝ) := by
    exact_mod_cast Nat.mod_add_div s k
  linarith

/-- The published moment exponent is nonnegative on its full order range. -/
theorem published_exponent_nonneg {k s : ℕ} (hk : 1000 ≤ k)
    (hlower : 2 * k ^ 2 ≤ s) : 0 ≤ sourceExponent k s (defect k (s : ℝ)) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hsR : 2 * (k : ℝ) ^ 2 ≤ (s : ℝ) := by exact_mod_cast hlower
  have hd : 0 ≤ defect k (s : ℝ) := by unfold defect; positivity
  unfold sourceExponent
  nlinarith [sq_nonneg ((k : ℝ) - 1)]

/-- The same theorem at every real endpoint P>=1, using the literal floor
cutoff in the original complete moment. Constants and order range are unchanged. -/
theorem published_moment_bound_real {k s : ℕ} (hk : 1000 ≤ k)
    (hlower : 2 * k ^ 2 ≤ s)
    (hupper : (s : ℝ) ≤ ((k : ℝ) ^ 2 / 2) *
      (1 / 2 + Real.log (3 * (k : ℝ) / 8)))
    (hsupply : VinogradovFordGlobalStep.ShortPrimeSupply k (3 / 50))
    {P : ℝ} (hP : 1 ≤ P) :
    meanValue s k ⌊P⌋₊ ≤ coefficient k (s : ℝ) *
      P ^ sourceExponent k s (defect k (s : ℝ)) := by
  have hP0 : 0 ≤ P := by linarith
  have hf : 1 ≤ ⌊P⌋₊ := (Nat.le_floor_iff hP0).mpr (by simpa using hP)
  refine (published_moment_bound hk hlower hupper hsupply hf).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hP0)
      (published_exponent_nonneg hk hlower))
    (coefficient_pos (by omega : 0 < k) _).le

end
end RiemannGaussian.VinogradovFordAllOrders
