/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockBatchCertificate
import RiemannGaussian.ZetaHardyProductCertificate

/-!
# Cached batches feed actual Hardy signs

The sound prepared batch is reused at each sample. The original bounded
Gamma weight, angle check, and complete analytic error remain in the test.
Successful signs feed the existing complete-window zero-count theorem.
-/

namespace RiemannGaussian.ZetaBlockBatchHardy
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaHardyProduct
open ZetaHardyPhase ZetaHardyProductCertificate ZetaBlockBatchCertificate

private theorem mem_input {cfg : DyadicConfig} (hp : cfg.precision ≤ 0) (T : ℚ) :
    Mem (point (T : ℝ)) (sampleInput cfg T) := by
  simpa only [point, sampleInput, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Complex.ofReal_ratCast]
    using mem_rational hp (1 / 2) T

/-- Rotate the complete cached approximation using the exact bounded Gamma weight. -/
def signedEvaluation (cfg : DyadicConfig) (N : ℕ) (B : Batch) (D : Box) (j : ℕ)
    (T : ℚ) (A : IntervalRat) : EvalResult Box :=
  match rotation cfg T A with
  | .error err => .error err
  | .ok W =>
    match evaluate cfg N B (sampleInput cfg T) D j with
    | .error err => .error err
    | .ok Z => .ok (mul cfg.precision W Z)

theorem mem_signedEvaluation {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s d q : ℂ} {H : ℕ} {Ks : List ℕ} {B : Batch}
    (hB : Sound cfg.precision s d q H Ks B) (j : ℕ) {D Z : Box} {T : ℚ} {A : IntervalRat}
    (hpoint : point (T : ℝ) = s + (d + j * q)) (hd : Mem (d + j * q) D)
    (ha : CertifiedArctan.check cfg (angleArgument T) A.lo A.hi = true)
    (he : signedEvaluation cfg (H + Ks.sum) B D j T A = .ok Z) :
    Mem (normalizedWeight 200 (T : ℝ) * ZetaBlockBatch.approximation s (d + j * q) H Ks) Z := by
  cases hW : rotation cfg T A with
  | error err => simp only [signedEvaluation, hW, reduceCtorEq] at he
  | ok W =>
    cases hZ : evaluate cfg (H + Ks.sum) B (sampleInput cfg T) D j with
    | error err => simp only [signedEvaluation, hW, hZ, reduceCtorEq] at he
    | ok Z0 =>
      simp only [signedEvaluation, hW, hZ, Except.ok.injEq] at he
      subst Z
      exact mem_mul (mem_rotation hp ha hW)
        (mem_evaluate hp hB j (by simpa only [← hpoint] using mem_input hp T) hd hZ) _

/-- Check actual sample geometry, shift radius, angle bracket, and the signed margin. -/
def signCheck (cfg : DyadicConfig) (H : ℕ) (Ks : List ℕ) (B : Batch) (S D : Box) (j : ℕ)
    (T : ℚ) (A : IntervalRat) (positive : Bool) : Bool :=
  decide (|T| ≤ 22000) && admissible cfg H Ks S (sampleInput cfg T) D &&
    CertifiedArctan.check cfg (angleArgument T) A.lo A.hi &&
    match signedEvaluation cfg (H + Ks.sum) B D j T A with
    | .error _ => false
    | .ok Z => decide (if positive then ZetaBlockCertificate.errorAllowance ≤ Z.re.lo.toRat
      else Z.re.hi.toRat ≤ -ZetaBlockCertificate.errorAllowance)

/-- A successful cached sample proves the sign of actual Hardy Z. -/
theorem hardy_sign_of_check {cfg : DyadicConfig} {H : ℕ} {Ks : List ℕ} {B : Batch}
    {s d q : ℂ} (hB : Sound cfg.precision s d q H Ks B) (j : ℕ) {S D : Box}
    {T : ℚ} {A : IntervalRat} {positive : Bool}
    (hpoint : point (T : ℝ) = s + (d + j * q)) (hs : Mem s S) (hd : Mem (d + j * q) D)
    (hc : signCheck cfg H Ks B S D j T A positive = true) :
    if positive then 0 < hardy (T : ℝ) else hardy (T : ℝ) < 0 := by
  unfold signCheck at hc
  obtain ⟨⟨⟨hT, hdom⟩, ha⟩, hb⟩ := Bool.and_eq_true_iff.mp hc |>.imp_left
    (fun h => Bool.and_eq_true_iff.mp h |>.imp_left Bool.and_eq_true_iff.mp)
  have hT' : |(T : ℝ)| ≤ 22000 := by exact_mod_cast of_decide_eq_true hT
  have hp : cfg.precision ≤ 0 :=
    (of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hdom).1).1).1
  have herr := (error_of_admissible hdom hs
    (by simpa only [← hpoint] using mem_input hp T) hd).2.2
  rw [← hpoint] at herr
  have herror := abs_lt.mp (normalized_error_lt herr)
  cases hZ : signedEvaluation cfg (H + Ks.sum) B D j T A with
  | error err => simp only [hZ, Bool.false_eq_true] at hb
  | ok Z =>
    simp only [hZ, decide_eq_true_eq] at hb
    have hv := (mem_signedEvaluation hp hB j hpoint hd ha hZ).1
    cases positive with
    | true =>
      apply (normalizedValue_pos_iff hT').mp
      have hh : (ZetaBlockCertificate.errorAllowance : ℝ) ≤ Z.re.lo.toRat := by exact_mod_cast hb
      linarith [hv.1, herror.1]
    | false =>
      apply (normalizedValue_neg_iff hT').mp
      have hh : (Z.re.hi.toRat : ℝ) ≤ -(ZetaBlockCertificate.errorAllowance : ℝ) := by exact_mod_cast hb
      linarith [hv.2, herror.2]

end RiemannGaussian.ZetaBlockBatchHardy
