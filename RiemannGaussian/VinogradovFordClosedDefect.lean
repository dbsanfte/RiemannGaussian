/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovFordPotentialIteration

/-!
# Ford's closed defect bound with the original constant

The cumulative potential estimate is evaluated at both endpoints. The
final rank-k step pays the stopped case throughout Ford's full order
range; the numerical constant is exactly `1.69`, not an enlarged reserve.
Here the paper's moment index is `n = J + 1`.

The scalar defect bound has no prime-supply premise. Its transport to the
actual homogeneous moment retains the unproved `ShortPrimeSupply` and
the original recursively defined coefficient. The paper's closed
coefficient estimate is a separate remaining obligation.

Source: Kevin Ford, *Vinogradov's integral and bounds for the Riemann
zeta function*, Lemma 3.6, arXiv:1910.08209v1.
-/

namespace RiemannGaussian.VinogradovFordClosedDefect
noncomputable section
open VinogradovFordSelectedIteration VinogradovFordPotential
open VinogradovFordPotentialIteration

/-- The initial diagonal defect retains the full `7/(6*k)` reserve. -/
theorem initial_potential_le {k : ℕ} (hk : 1000 ≤ k) :
    potential (normalized k 0) ≤ Real.log (3 / 4) + 1 / 2 - 7 / (6 * (k : ℝ)) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hq : 1 / (k : ℝ) < 1 := (div_lt_one hkpos).mpr (by linarith)
  have ha : 0 < 1 - 1 / (k : ℝ) := by linarith
  have hb : 0 < 1 + 1 / (3 * (k : ℝ)) := by positivity
  have hd : normalized k 0 = (1 / 2) * (1 - 1 / (k : ℝ)) := by
    unfold normalized selectedDefect
    field_simp
  have ht : 2 - normalized k 0 = (3 / 2) * (1 + 1 / (3 * (k : ℝ))) := by
    rw [hd]
    field_simp
    ring
  have hl := Real.log_le_sub_one_of_pos ha
  have hr := Real.log_le_sub_one_of_pos hb
  have he : Real.log (1 / 2) + Real.log (3 / 2) = Real.log (3 / 4) := by
    rw [← Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    norm_num
  unfold potential
  rw [ht, hd, Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0) ha.ne',
    Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) hb.ne']
  have hbudget : (1 / 2 : ℝ) * (1 - 1 / k) - 1 / k + 1 / (3 * k) =
      1 / 2 - 7 / (6 * k) := by ring
  linarith

/-- The rational endpoint reserve, uniformly down to the last active defect. -/
theorem endpoint_reserve {k d : ℝ} (hk : 1000 ≤ k) (hd0 : 0 < d)
    (hd : d ≤ 1 / 2) (hkd : 999 / 1000 ≤ k * d) :
    49 / (100 * k) ≤ d - d / (2 - d) := by
  have hkpos : 0 < k := by linarith
  have ht : 0 < 2 - d := by linarith
  have hp : (49 / 100) * (2 - d) ≤ k * d * (1 - d) := by
    by_cases hh : d ≤ 1 / 100
    · have hm := mul_le_mul hkd (show (99 : ℝ) / 100 ≤ 1 - d by linarith)
        (by norm_num : (0 : ℝ) ≤ 99 / 100) (by positivity : 0 ≤ k * d)
      nlinarith
    · have hkdl : 10 ≤ k * d := by
        have hm := mul_le_mul hk (show (1 : ℝ) / 100 ≤ d by linarith)
          (by norm_num : (0 : ℝ) ≤ 1 / 100) hkpos.le
        norm_num at hm
        linarith
      have hm := mul_le_mul hkdl (show (1 : ℝ) / 2 ≤ 1 - d by linarith)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity : 0 ≤ k * d)
      nlinarith
  have he : d - d / (2 - d) = d * (1 - d) / (2 - d) := by
    field_simp
    ring
  rw [he]
  apply (div_le_div_iff₀ (by positivity : 0 < 100 * k) ht).mpr
  nlinarith only [hp]

/-- The logarithmic endpoint contributes a negative `0.49/k` to the
final upper exponent. This is proved directly from the actual potential. -/
theorem endpoint_potential_ge {k d : ℝ} (hk : 1000 ≤ k) (hd0 : 0 < d)
    (hd : d ≤ 1 / 2) (hkd : 999 / 1000 ≤ k * d) :
    Real.log d + Real.log 2 + 49 / (100 * k) ≤ potential d := by
  have ht : 0 < 2 - d := by linarith
  have hh := Real.log_le_sub_one_of_pos (show 0 < 2 / (2 - d) by positivity)
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) ht.ne'] at hh
  have he : 2 / (2 - d) - 1 = d / (2 - d) := by field_simp; ring
  rw [he] at hh
  have hp := endpoint_reserve hk hd0 hd hkd
  unfold potential
  linarith

/-- The active selected sequence has Ford's original logarithmic defect bound. -/
theorem active_log_bound {k J : ℕ} (hk : 1000 ≤ k)
    (hfinal : (k : ℝ) - 1 < selectedDefect k J) :
    Real.log (normalized k J) ≤ Real.log (3 / 8) + 1 / 2 -
      2 * ((J : ℝ) + 1) / k + 169 / (100 * (k : ℝ)) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hactive := active_prefix (by omega : 26 ≤ k) hfinal
  have hs := potential_cumulative hk hactive
  have hi := initial_potential_le hk
  have hd := normalized_bounds (by omega : 26 ≤ k) J
  have hkd : 999 / 1000 ≤ (k : ℝ) * normalized k J := by
    have he : (k : ℝ) * normalized k J = selectedDefect k J / k := by
      unfold normalized
      field_simp
    rw [he]
    apply (le_div_iff₀ hkpos).mpr
    linarith
  have hl := endpoint_potential_ge hkR hd.1 hd.2 hkd
  have he : Real.log (3 / 4) = Real.log (3 / 8) + Real.log 2 := by
    rw [← Real.log_mul (by norm_num : (3 / 8 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  have hc : 1 / 2 - 2 * (J : ℝ) / k + 67 / (50 * (k : ℝ)) -
      7 / (6 * (k : ℝ)) - 49 / (100 * (k : ℝ)) ≤
        1 / 2 - 2 * ((J : ℝ) + 1) / k + 169 / (100 * (k : ℝ)) := by
    field_simp
    nlinarith
  rw [he] at hi
  linarith

/-- Exponentiating the checked potential yields the original `1.69/k`
constant whenever the selected defect is still above `k-1`. -/
theorem active_defect_bound {k J : ℕ} (hk : 1000 ≤ k)
    (hfinal : (k : ℝ) - 1 < selectedDefect k J) :
    selectedDefect k J ≤ (3 / 8) * (k : ℝ) ^ 2 *
      Real.exp (1 / 2 - 2 * ((J : ℝ) + 1) / k + 169 / (100 * (k : ℝ))) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hd := (normalized_bounds (by omega : 26 ≤ k) J).1
  have hh := Real.exp_le_exp.mpr (active_log_bound hk hfinal)
  rw [Real.exp_log hd] at hh
  have he : Real.log (3 / 8) + 1 / 2 - 2 * ((J : ℝ) + 1) / k + 169 / (100 * (k : ℝ)) =
      Real.log (3 / 8) + (1 / 2 - 2 * ((J : ℝ) + 1) / k + 169 / (100 * (k : ℝ))) := by ring
  rw [he, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 3 / 8)] at hh
  have hm := mul_le_mul_of_nonneg_right hh (sq_nonneg (k : ℝ))
  have hc : normalized k J * (k : ℝ) ^ 2 = selectedDefect k J := by
    unfold normalized
    exact div_mul_cancel₀ _ (pow_ne_zero _ hkpos.ne')
  rw [hc] at hm
  nlinarith only [hm]

/-- The published order ceiling pays the stopped case with room to spare: its
closed allowance is at least `k-31/100`, hence at least `k-1`. -/
theorem stopped_bound {k J : ℕ} (hk : 1000 ≤ k)
    (horder : (J : ℝ) + 1 ≤ ((k : ℝ) / 2) *
      (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1) :
    (k : ℝ) - 1 ≤ (3 / 8) * (k : ℝ) ^ 2 *
      Real.exp (1 / 2 - 2 * ((J : ℝ) + 1) / k + 169 / (100 * (k : ℝ))) := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hA : 0 < 3 * (k : ℝ) / 8 := by positivity
  have hn : 2 * ((J : ℝ) + 1) / k ≤
      (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 2 / k := by
    apply (div_le_iff₀ hkpos).mpr
    have he : ((1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 2 / k) * k =
        ((k : ℝ) / 2) * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) * 2 + 2 := by
      field_simp
    rw [he]
    linarith
  have hsplit : 2 / (k : ℝ) - 169 / (100 * (k : ℝ)) = 31 / (100 * (k : ℝ)) := by ring
  have hr : -Real.log (3 * (k : ℝ) / 8) - 31 / (100 * (k : ℝ)) ≤
      1 / 2 - 2 * ((J : ℝ) + 1) / k + 169 / (100 * (k : ℝ)) := by linarith
  have hm := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hr)
    (show (0 : ℝ) ≤ (3 / 8) * (k : ℝ) ^ 2 by positivity)
  have he : (3 / 8) * (k : ℝ) ^ 2 *
      Real.exp (-Real.log (3 * (k : ℝ) / 8) - 31 / (100 * (k : ℝ))) =
        (k : ℝ) * Real.exp (-(31 / (100 * (k : ℝ)))) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log hA]
    field_simp
  rw [he] at hm
  have ht := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (-(31 / (100 * (k : ℝ))))) hkpos.le
  have hb : (k : ℝ) * (-(31 / (100 * (k : ℝ))) + 1) = (k : ℝ) - 31 / 100 := by
    field_simp
    ring
  rw [hb] at ht
  linarith

/-- Ford's closed defect estimate on the full published upper order range.
No dense-prime or source-moment estimate is assumed. -/
theorem selected_defect_bound {k J : ℕ} (hk : 1000 ≤ k)
    (horder : (J : ℝ) + 1 ≤ ((k : ℝ) / 2) *
      (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1) :
    selectedDefect k J ≤ (3 / 8) * (k : ℝ) ^ 2 *
      Real.exp (1 / 2 - 2 * ((J : ℝ) + 1) / k + 169 / (100 * (k : ℝ))) := by
  by_cases hfinal : (k : ℝ) - 1 < selectedDefect k J
  · exact active_defect_bound hk hfinal
  · exact (le_of_not_gt hfinal).trans (stopped_bound hk horder)

/-- The paper's real order ceiling implies the natural iteration cap;
the cap need not be imposed as a separate hypothesis. -/
theorem paper_order_le {k J : ℕ} (hk : 1000 ≤ k)
    (horder : (J : ℝ) + 1 ≤ ((k : ℝ) / 2) *
      (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1) : J + 1 ≤ k ^ 2 := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by linarith
  have hl := Real.log_le_sub_one_of_pos (show 0 < 3 * (k : ℝ) / 8 by positivity)
  have hm := mul_le_mul_of_nonneg_left hl (show (0 : ℝ) ≤ k / 2 by positivity)
  have hJ : (J : ℝ) + 1 ≤ (k : ℝ) ^ 2 := by nlinarith [sq_nonneg ((k : ℝ) - 1000)]
  exact_mod_cast hJ

/-- The actual all-endpoint moment estimate with the closed published
defect. Its recursive coefficient and explicit short-prime-supply premise
remain; this does not assert the later closed coefficient bound. -/
theorem selected_moment_closed_defect {k J : ℕ} {omega : ℝ}
    (hk : 1000 ≤ k)
    (horder : (J : ℝ) + 1 ≤ ((k : ℝ) / 2) *
      (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1)
    (homega : 0 < omega) (homegaHalf : omega ≤ 1 / 2)
    (hsupply : VinogradovFordGlobalStep.ShortPrimeSupply k omega)
    {P : ℕ} (hP : 1 ≤ P) :
    VinogradovMeanValue.meanValue (VinogradovFordMomentSequence.order k J) k P ≤
      selectedCoefficient k omega J * (P : ℝ) ^
        VinogradovFordScales.sourceExponent k (VinogradovFordMomentSequence.order k J)
          ((3 / 8) * (k : ℝ) ^ 2 *
            Real.exp (1 / 2 - 2 * ((J : ℝ) + 1) / k + 169 / (100 * (k : ℝ)))) := by
  have hm := selected_moment_bound (by omega : 26 ≤ k) (paper_order_le hk horder)
    homega homegaHalf hsupply P hP
  refine hm.trans (mul_le_mul_of_nonneg_left ?_
    (selectedCoefficient_pos (by omega : 0 < k) homega J).le)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hP)
  unfold VinogradovFordScales.sourceExponent
  have hd := selected_defect_bound hk horder
  linarith

end
end RiemannGaussian.VinogradovFordClosedDefect
