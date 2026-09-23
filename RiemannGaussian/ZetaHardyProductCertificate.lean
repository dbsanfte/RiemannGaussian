/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaHardyProduct
import RiemannGaussian.CertifiedArctan
import RiemannGaussian.ZetaEulerMaclaurinCertificate

/-!
# Certified Hardy signs using one angle and an exact rational product

The two hundred Gamma shifts are evaluated by rational arithmetic. Only
one arctangent bracket and two logarithms enter the remaining rotation.
The positive coordinate normalization keeps its norm at most one, so the
full Euler--Maclaurin error remains valid without amplification.
-/

namespace RiemannGaussian.ZetaHardyProductCertificate
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaHardyProduct ZetaHardyPhase
open ZetaEulerMaclaurinEnclosure ZetaEulerMaclaurinCertificate

/-- Exact real and imaginary coordinates of the finite Gamma-shift product. -/
def productRat : ℕ → ℚ → ℚ × ℚ
  | 0, _ => (1, 0)
  | n + 1, T =>
    let P := productRat n T
    (P.1 * (1 / 4 + n) + P.2 * (T / 2), P.2 * (1 / 4 + n) - P.1 * (T / 2))

/-- The rational recurrence evaluates the complete complex product exactly. -/
theorem productRat_eq (M : ℕ) (T : ℚ) :
    ((productRat M T).1 : ℂ) + ((productRat M T).2 : ℂ) * Complex.I =
      shiftProduct M (T : ℝ) := by
  induction M with
  | zero => simp [productRat, shiftProduct]
  | succ M ih =>
    have hstep : shiftProduct (M + 1) (T : ℝ) = shiftProduct M (T : ℝ) * factor M (T : ℝ) := by
      simp only [shiftProduct, Finset.prod_range_succ]
    rw [hstep, ← ih]
    apply Complex.ext
    · simp [productRat, factor]
    · simp [productRat, factor]
      ring

/-- Rational coordinate-sum normalization of the complete product. -/
def rationalScale (M : ℕ) (T : ℚ) : ℚ := |(productRat M T).1| + |(productRat M T).2|

/-- The computable scale is the actual positive normalization. -/
theorem rationalScale_eq (M : ℕ) (T : ℚ) : (rationalScale M T : ℝ) = scale M (T : ℝ) := by
  rw [scale, ← productRat_eq]
  simp [rationalScale]

/-- The rational denominator cannot vanish, at any rational sample height. -/
theorem rationalScale_pos (M : ℕ) (T : ℚ) : 0 < rationalScale M T := by
  have hh := scale_pos M (T : ℝ)
  rw [← rationalScale_eq] at hh
  exact_mod_cast hh

/-- The normalized exact product, outward rounded only after all factors. -/
def productBox (cfg : DyadicConfig) (T : ℚ) : Box :=
  rational cfg.precision ((productRat 200 T).1 / rationalScale 200 T)
    ((productRat 200 T).2 / rationalScale 200 T)

/-- Rational evaluation encloses the exact normalized Gamma product. -/
theorem mem_productBox {cfg : DyadicConfig} (hp : cfg.precision ≤ 0) (T : ℚ) :
    Mem (((1 / scale 200 (T : ℝ) : ℝ) : ℂ) * shiftProduct 200 (T : ℝ)) (productBox cfg T) := by
  have hh := mem_rational hp ((productRat 200 T).1 / rationalScale 200 T)
    ((productRat 200 T).2 / rationalScale 200 T)
  convert hh using 1
  · rw [← rationalScale_eq, ← productRat_eq]
    push_cast
    ring
  · rfl

/-- The one remaining arctangent argument after the shift-two-hundred product. -/
def angleArgument (T : ℚ) : ℚ := 2 * T / 799

/-- Environment consisting of one proposed angle bracket and proved pi bounds. -/
def phaseEnv (cfg : DyadicConfig) (A : IntervalRat) : IntervalDyadicEnv := fun i =>
  IntervalDyadic.ofIntervalRat (if i = 0 then A else piBounds) cfg.precision

private noncomputable def phaseRealEnv (T : ℚ) : ℕ → ℝ := fun i =>
  if i = 0 then Real.arctan (angleArgument T) else Real.pi

/-- The exact single-phase expression, with both logarithms retained. -/
def phaseExpression (T : ℚ) : Expr :=
  .add (.add (.add (.mul (.const (799 / 4)) (.var 0))
    (.mul (.const (T / 4)) (.log (.const ((799 / 4) ^ 2 + (T / 2) ^ 2)))))
    (.const (-T / 2))) (.neg (.mul (.const (T / 2)) (.log (.var 1))))

private theorem phaseExpression_eq (T : ℚ) :
    Expr.eval (phaseRealEnv T) (phaseExpression T) = leadingPhase 200 (T : ℝ) := by
  rw [leadingPhase, GammaPhaseApproximation.primitive_eq_real (by norm_num)]
  norm_num [phaseExpression, phaseRealEnv, Expr.eval, angleArgument]
  ring_nf

private theorem phaseEnv_mem {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {T : ℚ} {A : IntervalRat} (hc : CertifiedArctan.check cfg (angleArgument T) A.lo A.hi = true) :
    envMemDyadic (phaseRealEnv T) (phaseEnv cfg A) := by
  intro i
  apply IntervalDyadic.mem_ofIntervalRat (prec := cfg.precision) (hprec := hp)
  by_cases hi : i = 0
  · simp only [phaseRealEnv, hi, if_true]
    exact CertifiedArctan.bounds_of_check hc
  · simp only [phaseRealEnv, hi, if_false]
    exact ⟨Real.pi_gt_d20.le, Real.pi_lt_d20.le⟩

/-- Evaluate the bounded Hardy rotation. The angle bracket is a checked input,
not an assumed transcendental value. Evaluation errors propagate unchanged. -/
def rotation (cfg : DyadicConfig) (T : ℚ) (A : IntervalRat) : EvalResult Box :=
  match evalIntervalDyadicChecked (phaseExpression T) (phaseEnv cfg A) cfg with
  | .error err => .error err
  | .ok B =>
    match CertifiedComplexInterval.exp cfg ⟨(rational cfg.precision 0 0).re, B⟩ with
    | .error err => .error err
    | .ok E => .ok (mul cfg.precision (productBox cfg T) E)

/-- The complete product rotation encloses the actual bounded weight. -/
theorem mem_rotation {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {T : ℚ} {A : IntervalRat} {B : Box}
    (ha : CertifiedArctan.check cfg (angleArgument T) A.lo A.hi = true)
    (he : rotation cfg T A = .ok B) : Mem (normalizedWeight 200 (T : ℝ)) B := by
  cases hP : evalIntervalDyadicChecked (phaseExpression T) (phaseEnv cfg A) cfg with
  | error err => simp [rotation, hP] at he
  | ok P =>
    cases hE : CertifiedComplexInterval.exp cfg ⟨(rational cfg.precision 0 0).re, P⟩ with
    | error err => simp [rotation, hP, hE] at he
    | ok E =>
      have hh := evalIntervalDyadicChecked_correct (phaseExpression T) (phaseRealEnv T)
        (phaseEnv cfg A) (phaseEnv_mem hp ha) cfg hp P hP
      rw [phaseExpression_eq] at hh
      have harg : Mem (Complex.I * (leadingPhase 200 (T : ℝ) : ℂ))
          ⟨(rational cfg.precision 0 0).re, P⟩ := by
        constructor
        · simpa using (mem_rational hp 0 0).1
        · simpa using hh
      have hrot := mem_exp hp harg hE
      have hprod := mem_mul (mem_productBox hp T) hrot cfg.precision
      simp only [rotation, hP, hE, Except.ok.injEq] at he
      subst B
      simpa only [normalizedWeight, weight, mul_assoc] using hprod

/-- Exact rational sample on the critical line, outward rounded by the evaluator. -/
def sampleInput (cfg : DyadicConfig) (T : ℚ) : Box := rational cfg.precision (1 / 2) T

private theorem mem_sampleInput {cfg : DyadicConfig} (hp : cfg.precision ≤ 0) (T : ℚ) :
    Mem (point (T : ℝ)) (sampleInput cfg T) := by
  simpa only [point, sampleInput, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Complex.ofReal_ratCast]
    using mem_rational hp (1 / 2) T

/-- The complete signed approximation, retaining both oscillatory coordinates
until multiplication by the bounded phase weight. -/
def signedEvaluation (cfg : DyadicConfig) (N : ℕ) (T : ℚ) (A : IntervalRat) : EvalResult Box :=
  match rotation cfg T A with
  | .error err => .error err
  | .ok W =>
    match evaluate cfg N 18 (sampleInput cfg T) with
    | .error err => .error err
    | .ok Z => .ok (mul cfg.precision W Z)

/-- Every successful signed evaluation encloses the literal finite weighted
zeta approximation, before paying the analytic error. -/
theorem mem_signedEvaluation {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {N : ℕ} {T : ℚ} {A : IntervalRat} {B : Box}
    (ha : CertifiedArctan.check cfg (angleArgument T) A.lo A.hi = true)
    (he : signedEvaluation cfg N T A = .ok B) :
    Mem (normalizedWeight 200 (T : ℝ) * ZetaEulerMaclaurin.approximation N (point (T : ℝ)) 18) B := by
  cases hW : rotation cfg T A with
  | error err => simp [signedEvaluation, hW] at he
  | ok W =>
    cases hZ : evaluate cfg N 18 (sampleInput cfg T) with
    | error err => simp [signedEvaluation, hW, hZ] at he
    | ok Z =>
      simp only [signedEvaluation, hW, hZ, Except.ok.injEq] at he
      subst B
      exact mem_mul (mem_rotation hp ha hW) (mem_evaluate hp (mem_sampleInput hp T) N 18 hZ) _

/-- Check an actual Hardy sign, including all analytic domain conditions,
the height restriction, the angle bracket and the zeta truncation error. -/
def signCheck (cfg : DyadicConfig) (N : ℕ) (T : ℚ) (A : IntervalRat) (positive : Bool) : Bool :=
  decide (|T| ≤ 22000) && admissible cfg N (sampleInput cfg T) &&
    CertifiedArctan.check cfg (angleArgument T) A.lo A.hi &&
    match signedEvaluation cfg N T A with
    | .error _ => false
    | .ok B => decide (if positive then errorAllowance ≤ B.re.lo.toRat
      else B.re.hi.toRat ≤ -errorAllowance)

/-- A kernel-checked signed sample gives the sign of the actual Hardy function.
Neither numerical endpoint values nor transcendental brackets are assumed. -/
theorem hardy_sign_of_check {cfg : DyadicConfig} {N : ℕ} {T : ℚ}
    {A : IntervalRat} {positive : Bool} (hc : signCheck cfg N T A positive = true) :
    if positive then 0 < hardy (T : ℝ) else hardy (T : ℝ) < 0 := by
  unfold signCheck at hc
  obtain ⟨⟨⟨hT, hd⟩, ha⟩, hb⟩ := Bool.and_eq_true_iff.mp hc |>.imp_left
    (fun h => Bool.and_eq_true_iff.mp h |>.imp_left Bool.and_eq_true_iff.mp)
  simp only [decide_eq_true_eq] at hT
  have hT' : |(T : ℝ)| ≤ 22000 := by exact_mod_cast hT
  have hp : cfg.precision ≤ 0 := by
    exact (of_decide_eq_true hd).1
  have he := (error_of_admissible hd (mem_sampleInput hp T)).2
  have herr := abs_lt.mp (normalized_error_lt he)
  cases hB : signedEvaluation cfg N T A with
  | error err => simp only [hB, Bool.false_eq_true] at hb
  | ok B =>
    simp only [hB, decide_eq_true_eq] at hb
    have hv := (mem_signedEvaluation hp ha hB).1
    cases positive with
    | true =>
      apply (normalizedValue_pos_iff hT').mp
      have hh : (errorAllowance : ℝ) ≤ B.re.lo.toRat := by exact_mod_cast hb
      linarith [hv.1, herr.1]
    | false =>
      apply (normalizedValue_neg_iff hT').mp
      have hh : (B.re.hi.toRat : ℝ) ≤ -(errorAllowance : ℝ) := by exact_mod_cast hb
      linarith [hv.2, herr.2]

end RiemannGaussian.ZetaHardyProductCertificate
