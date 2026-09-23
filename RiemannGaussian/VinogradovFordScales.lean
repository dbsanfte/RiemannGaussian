/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.VinogradovLiteratureIteration

/-!
# Ford's original mixed-iteration scales

Ford, Lemma 3.4 (arXiv:1910.08209v1), also Bellotti, Lemma 2.4,
retains the triangular depth term in its scale recurrence. Under the
paper's depth restriction it pays our shrinking-tuple conditioning
exponent with a nonpositive remainder. The sharper displayed recurrence
in Ford's subsequent remark and Bellotti 2.3 remains a separate audit.
-/

namespace RiemannGaussian.VinogradovFordScales
noncomputable section
open VinogradovLiteratureIteration

/-- The ordinary source moment exponent. -/
def sourceExponent (k s : ℕ) (delta : ℝ) : ℝ :=
  2 * (s : ℝ) - (k : ℝ) * ((k : ℝ) + 1) / 2 + delta

/-- The exact prime cost after retaining the quotient source moment. -/
def primeGap (k d r s : ℕ) (delta : ℝ) : ℝ :=
  conditioningExponent d r s - sourceExponent k s delta

/-- Ford's original recurrence, including its triangular depth term. -/
def previousScale (k d r : ℕ) (delta psi : ℝ) : ℝ :=
  1 / (2 * (r : ℝ)) +
    ((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r + (d : ℝ) ^ 2 - d - 2 * delta) /
      (4 * k * r) * psi

/-- The defect after one full mixed iteration in Ford's Lemma 3.4. -/
def nextDefect (k r : ℕ) (delta phi : ℝ) : ℝ :=
  delta * (1 - phi) - k + phi * ((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r) / 2

/-- Throughout the usual defect range the coupled prime exponent is
nonnegative, and is at least the remaining active dimension. -/
theorem primeGap_ge {k d r s : ℕ} (hds : d ≤ 2 * s) {delta : ℝ}
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    (k : ℝ) - d ≤ primeGap k d r s delta := by
  have ht : (0 : ℝ) ≤ ((r - d) * (r - d - 1) / 2 : ℕ) := Nat.cast_nonneg _
  unfold primeGap conditioningExponent sourceExponent
  rw [Nat.cast_add, Nat.cast_sub hds, Nat.cast_mul, Nat.cast_ofNat]
  nlinarith only [ht, hdelta]

/-- Ford's previous scale is strictly positive in the moment iteration's
initial defect range. -/
theorem previousScale_pos {k d r : ℕ} (hk : 0 < k) (hr : 0 < r)
    {delta psi : ℝ} (hpsi : 0 ≤ psi)
    (hdelta : delta ≤ (k : ℝ) * ((k : ℝ) - 1) / 2) :
    0 < previousScale k d r delta psi := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hd : 0 ≤ (d : ℝ) * ((d : ℝ) - 1) := by
    cases d with
    | zero => norm_num
    | succ d =>
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) d, sq_nonneg (d : ℝ)]
  have hn : 0 ≤ (k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r + (d : ℝ) ^ 2 - d - 2 * delta := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by positivity) (sub_nonneg.mpr hrR)]
  unfold previousScale
  exact add_pos_of_pos_of_nonneg (by positivity)
    (mul_nonneg (div_nonneg hn (by positivity)) hpsi)

/-- After the quotient cancellation the prime gap is independent of s. -/
theorem primeGap_eq {k d r s : ℕ} (hds : d ≤ 2 * s) (hdr : d ≤ r) (delta : ℝ) :
    primeGap k d r s delta =
      ((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r - 2 * r * d +
        (d : ℝ) ^ 2 - d - 2 * delta) / 2 := by
  rw [primeGap, conditioningExponent_cast hds hdr]
  unfold sourceExponent
  ring

/-- The original conditioning step has precisely the published updated
defect, with the source moment's quotient power still coupled to its prime. -/
theorem next_exponent (k r s : ℕ) (delta phi : ℝ) :
    sourceExponent k s delta + k + phi * primeGap k 0 r s delta =
      sourceExponent k (s + k) (nextDefect k r delta phi) := by
  rw [primeGap_eq (by omega) (by omega)]
  unfold sourceExponent nextDefect
  push_cast
  ring

/-- The exact remainder when Ford's original scale is used in the
shrinking-tuple step. It has the sign of the published depth constraint. -/
theorem scale_balance {k d r s : ℕ} (hds : d ≤ 2 * s) (hdr : d ≤ r)
    (hdk : d < k) (hr : 0 < r) (delta psi : ℝ) :
    1 / 2 - r * previousScale k d r delta psi +
        primeGap k d r s delta / (2 * ((k : ℝ) - d)) * psi =
      (d : ℝ) * ((d : ℝ) * ((d : ℝ) - 1) +
        ((k : ℝ) - r) * ((k : ℝ) - r + 1) - 2 * delta) * psi /
          (4 * k * ((k : ℝ) - d)) := by
  rw [primeGap_eq hds hdr]
  unfold previousScale
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hkd : (k : ℝ) - d ≠ 0 := by
    have h : (d : ℝ) < k := by exact_mod_cast hdk
    linarith
  field_simp [hr0, hk0, hkd]
  ring

/-- The actual exponent remainder is nonpositive under Ford's depth
restriction. No unproved cancellation or omitted depth term is used. -/
theorem scale_balance_nonpos {k d r s : ℕ} (hds : d ≤ 2 * s) (hdr : d ≤ r)
    (hdk : d < k) (hr : 0 < r) {delta psi : ℝ} (hpsi : 0 ≤ psi)
    (hdepth : (d : ℝ) * ((d : ℝ) - 1) ≤
      2 * delta - ((k : ℝ) - r) * ((k : ℝ) - r + 1)) :
    1 / 2 - r * previousScale k d r delta psi +
      primeGap k d r s delta / (2 * ((k : ℝ) - d)) * psi ≤ 0 := by
  rw [scale_balance hds hdr hdk hr]
  apply div_nonpos_of_nonpos_of_nonneg
  · exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)) hpsi
  · have hdkR : (d : ℝ) < k := by exact_mod_cast hdk
    positivity

/-- Every preceding scale remains at most the diagonal scale 1/r,
using the same depth condition as the original published iteration. -/
theorem previousScale_le {k d r : ℕ} (hk : 0 < k) (hr : 0 < r)
    {delta psi : ℝ} (hpsi : 0 ≤ psi) (hpsiR : psi ≤ 1 / (r : ℝ))
    (hdepth : (d : ℝ) * ((d : ℝ) - 1) ≤
      2 * delta - ((k : ℝ) - r) * ((k : ℝ) - r + 1)) :
    previousScale k d r delta psi ≤ 1 / (r : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hcoef : ((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r + (d : ℝ) ^ 2 - d - 2 * delta) /
      (4 * k * r) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith only [hdepth]
  calc
    _ ≤ 1 / (2 * (r : ℝ)) + (1 / 2) * psi := by
      unfold previousScale
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef hpsi)
    _ ≤ 1 / (2 * (r : ℝ)) + (1 / 2) * (1 / (r : ℝ)) := by gcongr
    _ = _ := by field_simp; ring

end
end RiemannGaussian.VinogradovFordScales
