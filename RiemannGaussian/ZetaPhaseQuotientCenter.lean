/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaPhaseContactFactorization
import Mathlib.RingTheory.Polynomial.Bernstein

/-!
# A positive rational center for the exact contact quotient

Two exact Bernstein expansions give a positive rational lower bound on
both halves of the cosine interval. This is a bound for the explicitly
defined central polynomial; transferring it to the exact quotient also
requires a coefficient-error estimate.
-/

open scoped Classical Polynomial
open Polynomial

namespace RiemannGaussian

/-- Rational coefficients of the proposed degree-sixteen quotient center. -/
def phaseContactQuotientCenterQ (k : ℕ) : ℚ :=
  match k with
  | 0 => 9837955463417829473 / 50000000000000000000
  | 1 => -77272186105609517249 / 100000000000000000000
  | 2 => 173887481690603069829 / 100000000000000000000
  | 3 => -278140152876502664141 / 100000000000000000000
  | 4 => 66667993996966824007 / 20000000000000000000
  | 5 => -13998303712883559327 / 4000000000000000000
  | 6 => 145097379768049658721 / 25000000000000000000
  | 7 => -157252832193526220641 / 12500000000000000000
  | 8 => 1443798840209643151993 / 100000000000000000000
  | 9 => 793884495352572726369 / 100000000000000000000
  | 10 => -2229897866581040998463 / 50000000000000000000
  | 11 => 528836654828854240559 / 12500000000000000000
  | 12 => 224651979657251797337 / 12500000000000000000
  | 13 => -1806339241322249366873 / 25000000000000000000
  | 14 => 3296465177601674399083 / 50000000000000000000
  | 15 => -2788051246048719809743 / 100000000000000000000
  | 16 => 471857521664651285617 / 100000000000000000000
  | _ => 0

/-- Exact Bernstein coefficients of the rational center on either half
of the cosine interval; true selects the negative half. -/
def phaseContactQuotientBernsteinQ (negative : Bool) (k : ℕ) : ℚ :=
  match negative, k with
  | false, 0 => 9837955463417829473 / 50000000000000000000
  | false, 1 => 237542388723761025887 / 1600000000000000000000
  | false, 2 => 229319000221123230769 / 2000000000000000000000
  | false, 3 => 63265189609136375151 / 700000000000000000000
  | false, 4 => 507407385585528760541 / 7000000000000000000000
  | false, 5 => 4286346392044899550541 / 72800000000000000000000
  | false, 6 => 38760899293596759237593 / 800800000000000000000000
  | false, 7 => 369845255255477074917 / 9152000000000000000000
  | false, 8 => 10924898102743169528449 / 321750000000000000000000
  | false, 9 => 8140172667532780008963 / 286000000000000000000000
  | false, 10 => 19770391837796415122693 / 800800000000000000000000
  | false, 11 => 608049749260447943957 / 29120000000000000000000
  | false, 12 => 3318629568565004273527 / 182000000000000000000000
  | false, 13 => 126353026456893646009 / 8000000000000000000000
  | false, 14 => 82967289971041827461 / 6000000000000000000000
  | false, 15 => 3889566386428011317 / 320000000000000000000
  | false, 16 => 1076636141325545153 / 100000000000000000000
  | true, 0 => 9837955463417829473 / 50000000000000000000
  | true, 1 => 78417352186996012077 / 320000000000000000000
  | true, 2 => 307839965374585408507 / 1000000000000000000000
  | true, 3 => 5461163639165478490663 / 14000000000000000000000
  | true, 4 => 3490074052158364528397 / 7000000000000000000000
  | true, 5 => 46793487575826995494227 / 72800000000000000000000
  | true, 6 => 669652883531333001353589 / 800800000000000000000000
  | true, 7 => 1258477038963010919428251 / 1144000000000000000000000
  | true, 8 => 86011627025520098310337 / 58500000000000000000000
  | true, 9 => 575398151034206859223593 / 286000000000000000000000
  | true, 10 => 2271436218727878268943133 / 800800000000000000000000
  | true, 11 => 1787728239681004696165297 / 436800000000000000000000
  | true, 12 => 1062126990154016955702133 / 182000000000000000000000
  | true, 13 => 431397074569332270696273 / 56000000000000000000000
  | true, 14 => 14281381534883080116211 / 1500000000000000000000
  | true, 15 => 35419661230430295254427 / 1600000000000000000000
  | true, 16 => 13905522769554768657327 / 100000000000000000000
  | _, _ => 0

/-- All central Bernstein coefficients have a strict common margin. -/
theorem phaseContactQuotientBernsteinQ_lower (negative : Bool) (i : Fin 17) :
    (1 / 200 : ℚ) ≤ phaseContactQuotientBernsteinQ negative i.val := by
  cases negative <;> fin_cases i <;> norm_num [phaseContactQuotientBernsteinQ]

noncomputable section

/-- The central polynomial with the rational coefficients above. -/
def phaseContactQuotientCenter : ℝ[X] :=
  ∑ k : Fin 17, C (phaseContactQuotientCenterQ k.val : ℝ) * X ^ k.val

set_option maxHeartbeats 4000000 in
/-- Exact Bernstein expansion on the positive half of the cosine interval. -/
theorem phaseContactQuotientCenter_eval_bernstein (x : ℝ) :
    phaseContactQuotientCenter.eval x =
      ∑ i : Fin 17, (phaseContactQuotientBernsteinQ false i.val : ℝ) *
        (bernsteinPolynomial ℝ 16 i.val).eval x := by
  simp only [phaseContactQuotientCenter, Polynomial.eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ (phaseContactQuotientCenterQ k : ℝ) * x ^ k) 17,
    Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ (phaseContactQuotientBernsteinQ false k : ℝ) *
      (bernsteinPolynomial ℝ 16 k).eval x) 17]
  norm_num [phaseContactQuotientCenterQ, phaseContactQuotientBernsteinQ,
    Finset.sum_range_succ, bernsteinPolynomial, Nat.choose]
  ring

set_option maxHeartbeats 4000000 in
/-- The same polynomial has a second exact Bernstein expansion on the
negative half, with the reflection kept explicitly. -/
theorem phaseContactQuotientCenter_eval_neg_bernstein (x : ℝ) :
    phaseContactQuotientCenter.eval (-x) =
      ∑ i : Fin 17, (phaseContactQuotientBernsteinQ true i.val : ℝ) *
        (bernsteinPolynomial ℝ 16 i.val).eval x := by
  simp only [phaseContactQuotientCenter, Polynomial.eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ (phaseContactQuotientCenterQ k : ℝ) * (-x) ^ k) 17,
    Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ (phaseContactQuotientBernsteinQ true k : ℝ) *
      (bernsteinPolynomial ℝ 16 k).eval x) 17]
  norm_num [phaseContactQuotientCenterQ, phaseContactQuotientBernsteinQ,
    Finset.sum_range_succ, bernsteinPolynomial, Nat.choose]
  ring

private theorem bernstein_lower (negative : Bool) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 / 200 : ℝ) ≤ ∑ i : Fin 17, (phaseContactQuotientBernsteinQ negative i.val : ℝ) *
      (bernsteinPolynomial ℝ 16 i.val).eval x := by
  have hb (i : Fin 17) : 0 ≤ (bernsteinPolynomial ℝ 16 i.val).eval x := by
    simp only [bernsteinPolynomial, eval_mul, eval_natCast, eval_pow, eval_X, eval_sub, eval_one]
    positivity
  have hs : (∑ i : Fin 17, (bernsteinPolynomial ℝ 16 i.val).eval x) = 1 := by
    have h := congrArg (fun p : ℝ[X] ↦ p.eval x) (bernsteinPolynomial.sum ℝ 16)
    simpa only [Polynomial.eval_finsetSum, eval_one, ← Fin.sum_univ_eq_sum_range] using h
  calc
    _ = ∑ i : Fin 17, (1 / 200 : ℝ) * (bernsteinPolynomial ℝ 16 i.val).eval x := by
      rw [← Finset.mul_sum, hs, mul_one]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (hb i)
      have h := (Rat.cast_le (K := ℝ)).mpr (phaseContactQuotientBernsteinQ_lower negative i)
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
      exact h

/-- The rational central polynomial is uniformly positive on the whole
cosine interval, with a kernel-checked rational margin. -/
theorem phaseContactQuotientCenter_lower {x : ℝ} (hx : |x| ≤ 1) :
    (1 / 200 : ℝ) ≤ phaseContactQuotientCenter.eval x := by
  by_cases hx0 : 0 ≤ x
  · rw [phaseContactQuotientCenter_eval_bernstein]
    exact bernstein_lower false hx0 (abs_le.mp hx).2
  · have hx' : 0 ≤ -x := by linarith
    have hx1 : -x ≤ 1 := by linarith [(abs_le.mp hx).1]
    have h := bernstein_lower true hx' hx1
    rw [← phaseContactQuotientCenter_eval_neg_bernstein, neg_neg] at h
    exact h

end

end RiemannGaussian
