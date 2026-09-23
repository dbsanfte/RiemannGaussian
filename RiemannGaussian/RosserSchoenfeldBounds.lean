/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.RosserSchoenfeldAnchor
import RiemannGaussian.RosserSchoenfeldComparison

/-!
# Explicit bounds for the Rosser--Schoenfeld comparison integral

Section 7, Lemmas 2, 3 and 5 are proved at their stated constants and
starting points. Rational sub- and supersolutions certify the finite
integrals directly. The anchor is checked in `RosserSchoenfeldAnchor`.
These are unconditional bounds for the literal comparison functions.
Transferring them to prime counts still requires the source's theta bounds.
-/

namespace RiemannGaussian.RosserSchoenfeldBounds
noncomputable section
open Real RosserSchoenfeldAnchor RosserSchoenfeldComparison

private def quartic (a x : ℝ) : ℝ :=
  x / log x + (1 + a) * x / log x ^ 2 + (2 + a) * x / log x ^ 3 +
    18 * x / log x ^ 4

private def cubic (x : ℝ) : ℝ :=
  x / log x + (53 / 100) * x / log x ^ 2 + (153 / 100) * x / log x ^ 3

private theorem log_lower {x : ℝ} (hx : 1451 ≤ x) : 36 / 5 ≤ log x :=
  log_anchor_lower.trans (Real.log_le_log (by norm_num) hx)

private theorem quartic_hasDerivAt (a : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (quartic a)
      (1 / log x + a / log x ^ 2 - a / log x ^ 3 +
        ((12 - 3 * a) * log x - 72) / log x ^ 5) x := by
  have hl : log x ≠ 0 := (log_pos hx).ne'
  have hd := (((logTerm_hasDerivAt 0 hx).add
    ((logTerm_hasDerivAt 1 hx).const_mul (1 + a))).add
      ((logTerm_hasDerivAt 2 hx).const_mul (2 + a))).add
        ((logTerm_hasDerivAt 3 hx).const_mul 18)
  convert! hd using 1
  · ext t
    simp only [quartic, Pi.add_apply, Nat.reduceAdd, pow_one]
    ring
  · norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd]
    field_simp
    ring

private theorem cubic_hasDerivAt {x : ℝ} (hx : 1 < x) :
    HasDerivAt cubic
      (1 / log x - (47 / 100) / log x ^ 2 + (47 / 100) / log x ^ 3 -
        (459 / 100) / log x ^ 4) x := by
  have hl : log x ≠ 0 := (log_pos hx).ne'
  have hd := ((logTerm_hasDerivAt 0 hx).add
    ((logTerm_hasDerivAt 1 hx).const_mul (53 / 100))).add
      ((logTerm_hasDerivAt 2 hx).const_mul (153 / 100))
  convert! hd using 1
  · ext t
    simp only [cubic, Pi.add_apply, Nat.reduceAdd, pow_one]
    ring
  · norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd]
    field_simp
    ring

private theorem comparison_anchor_lt_quartic {a : ℝ} (ha : 31 / 100 ≤ a) :
    comparison a 1451 < quartic a 1451 := by
  have ht0 : 0 < log (1451 : ℝ) := log_pos (by norm_num)
  have ht := log_anchor_upper
  have hh : (230 : ℝ) < 1360 / log 1451 + 1451 / log 1451 ^ 2 +
      1451 * (2 + a) / log 1451 ^ 3 + (18 * 1451) / log 1451 ^ 4 := by
    calc
      (230 : ℝ) < 1360 / (73 / 10) + 1451 / (73 / 10) ^ 2 +
          1451 * (2 + 31 / 100) / (73 / 10) ^ 3 +
            (18 * 1451) / (73 / 10) ^ 4 := by norm_num
      _ ≤ _ := by gcongr
  have htheta : 1360 / log (1451 : ℝ) < Chebyshev.theta 1451 / log 1451 :=
    (div_lt_div_iff_of_pos_right ht0).mpr theta_anchor_lower
  have he : quartic a 1451 - comparison a 1451 =
      Chebyshev.theta 1451 / log 1451 + 1451 / log 1451 ^ 2 +
        1451 * (2 + a) / log 1451 ^ 3 + (18 * 1451) / log 1451 ^ 4 - 230 := by
    simp only [quartic, comparison, primeCounting_anchor, Nat.cast_ofNat,
      intervalIntegral.integral_same, add_zero]
    field_simp
    ring
  linarith

private theorem cubic_anchor_lt_comparison : cubic 1451 < comparison (-47 / 100) 1451 := by
  have ht0 : 0 < log (1451 : ℝ) := log_pos (by norm_num)
  have ht := log_anchor_lower
  have hh : 1410 / log (1451 : ℝ) + 1451 / log 1451 ^ 2 +
      (153 / 100) * 1451 / log 1451 ^ 3 < 230 := by
    calc
      _ ≤ (1410 : ℝ) / (36 / 5) + 1451 / (36 / 5) ^ 2 +
          (153 / 100) * 1451 / (36 / 5) ^ 3 := by gcongr
      _ < _ := by norm_num
  have htheta : Chebyshev.theta 1451 / log 1451 < 1410 / log (1451 : ℝ) :=
    (div_lt_div_iff_of_pos_right ht0).mpr theta_anchor_upper
  have he : comparison (-47 / 100) 1451 - cubic 1451 =
      230 - (Chebyshev.theta 1451 / log 1451 + 1451 / log 1451 ^ 2 +
        (153 / 100) * 1451 / log 1451 ^ 3) := by
    simp only [cubic, comparison, primeCounting_anchor, Nat.cast_ofNat,
      intervalIntegral.integral_same, add_zero]
    field_simp
    ring
  linarith

private theorem comparison_lt_quartic {a x : ℝ}
    (ha : 31 / 100 ≤ a) (ha' : a ≤ 47 / 100) (hx : 1451 ≤ x) :
    comparison a x < quartic a x := by
  have hd (t : ℝ) (ht : 1451 ≤ t) :=
    (quartic_hasDerivAt a (show 1 < t by linarith)).sub
      (comparison_hasDerivAt a (show 1 < t by linarith))
  have hm : MonotoneOn (fun t => quartic a t - comparison a t) (Set.Ici 1451) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv (quartic a - comparison a) t
      rw [(hd t (interior_subset ht)).deriv]
      have hl := log_lower (interior_subset ht)
      have hpos : 0 ≤ (12 - 3 * a) * log t - 72 := by
        have hh := mul_nonneg (show 0 ≤ 47 / 100 - a by linarith)
          (show 0 ≤ log t by linarith)
        nlinarith
      have hf := div_nonneg hpos (pow_nonneg (show 0 ≤ log t by linarith) 5)
      linarith
  have h := hm (show (1451 : ℝ) ∈ Set.Ici 1451 by simp only [Set.mem_Ici, le_refl]) hx hx
  have h0 := comparison_anchor_lt_quartic ha
  linarith

private theorem cubic_lt_comparison {x : ℝ} (hx : 1451 ≤ x) :
    cubic x < comparison (-47 / 100) x := by
  have hd (t : ℝ) (ht : 1451 ≤ t) :=
    (comparison_hasDerivAt (-47 / 100) (show 1 < t by linarith)).sub
      (cubic_hasDerivAt (show 1 < t by linarith))
  have hm : MonotoneOn (fun t => comparison (-47 / 100) t - cubic t) (Set.Ici 1451) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _)
    · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      change 0 ≤ deriv (comparison (-47 / 100) - cubic) t
      rw [(hd t (interior_subset ht)).deriv]
      have hh : 0 ≤ (459 / 100 : ℝ) / log t ^ 4 := by positivity
      convert! hh using 1
      ring
  have h := hm (show (1451 : ℝ) ∈ Set.Ici 1451 by simp only [Set.mem_Ici, le_refl]) hx hx
  linarith [cubic_anchor_lt_comparison]

private theorem quartic_le_upper {a x : ℝ} (hx : 1 < x)
    (hgap : 18 + (2 + a) * log x ≤ (1 / 2 - a) * log x ^ 2) :
    quartic a x ≤ upper x := by
  have ht : 0 < log x := log_pos hx
  have he : upper x - quartic a x =
      x * ((1 / 2 - a) * log x ^ 2 - (2 + a) * log x - 18) / log x ^ 4 := by
    unfold upper quartic
    field_simp
    ring
  rw [← sub_nonneg, he]
  exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (pow_nonneg ht.le _)

private theorem lower_le_cubic {x : ℝ} (hx : 1451 ≤ x) : lower x ≤ cubic x := by
  have ht := log_lower hx
  have ht0 : 0 < log x := by linarith
  have ht1 : 0 < log x - 1 / 2 := by linarith
  have hp : 0 ≤ (3 / 100) * log x ^ 2 + (253 / 200) * log x - 153 / 200 := by
    nlinarith [sq_nonneg (log x)]
  have he : cubic x - lower x =
      x * ((3 / 100) * log x ^ 2 + (253 / 200) * log x - 153 / 200) /
        (log x ^ 3 * (log x - 1 / 2)) := by
    unfold lower cubic
    ring_nf
    field_simp [show -1 + log x * 2 ≠ 0 by linarith]
    ring
  rw [← sub_nonneg, he]
  exact div_nonneg (mul_nonneg (by linarith) hp) (mul_nonneg (pow_nonneg ht0.le _) ht1.le)

/-- Rosser--Schoenfeld Section 7, Lemma 2, at its stated finite starting point. -/
theorem comparison_31_lt_upper {x : ℝ} (hx : 10 ^ 8 ≤ x) :
    comparison (31 / 100) x < upper x := by
  have ht : 18 ≤ log x := log_ten_pow_eight_lower.trans (log_le_log (by positivity) hx)
  apply (comparison_lt_quartic (by norm_num) (by norm_num) (by norm_num at hx ⊢; linarith)).trans_le
  apply quartic_le_upper (by norm_num at hx ⊢; linarith)
  nlinarith [sq_nonneg (log x - 18)]

/-- Rosser--Schoenfeld Section 7, Lemma 3, at its stated exponential starting point. -/
theorem comparison_47_lt_upper {x : ℝ} (hx : exp 100 ≤ x) :
    comparison (47 / 100) x < upper x := by
  have hx0 : 0 < x := (exp_pos 100).trans_le hx
  have ht : 100 ≤ log x := (le_log_iff_exp_le hx0).mpr hx
  have hanchor : 1451 ≤ x := by
    apply (log_le_log_iff (by norm_num) hx0).mp
    exact log_anchor_upper.trans (by linarith)
  apply (comparison_lt_quartic (by norm_num) (by norm_num) hanchor).trans_le
  apply quartic_le_upper (by linarith)
  nlinarith [sq_nonneg (log x - 100)]

/-- The lower comparison in Section 7, Lemma 5, holds already from its anchor. -/
theorem lower_lt_comparison_neg47 {x : ℝ} (hx : 1451 ≤ x) :
    lower x < comparison (-47 / 100) x :=
  (lower_le_cubic hx).trans_lt (cubic_lt_comparison hx)

/-- In particular, the source's original Lemma 5 starting point is retained. -/
theorem lower_lt_comparison_neg47_published {x : ℝ} (hx : 10 ^ 8 ≤ x) :
    lower x < comparison (-47 / 100) x := by
  apply lower_lt_comparison_neg47
  norm_num at hx ⊢
  linarith

end
end RiemannGaussian.RosserSchoenfeldBounds
