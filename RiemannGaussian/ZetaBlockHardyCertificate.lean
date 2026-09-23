/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockCertificate
import RiemannGaussian.ZetaHardyProductCertificate

/-!
# Accelerated certificates feeding the actual Hardy sign/count chain

The block approximation's full error is paid after multiplication by the
proved bounded Gamma-phase weight. No phase error, omitted term or numerical
table is introduced as an extra analytic hypothesis.
-/

namespace RiemannGaussian.ZetaBlockHardyCertificate
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaHardyProduct
open ZetaHardyPhase ZetaHardyProductCertificate ZetaBlockCertificate

private theorem mem_input {cfg : DyadicConfig} (hp : cfg.precision ≤ 0) (T : ℚ) :
    Mem (point (T : ℝ)) (sampleInput cfg T) := by
  simpa only [point, sampleInput, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Complex.ofReal_ratCast]
    using mem_rational hp (1 / 2) T

/-- Multiply the complete accelerated approximation by the exact bounded weight. -/
def signedEvaluation (cfg : DyadicConfig) (H : ℕ) (Ks : List ℕ) (T : ℚ) (A : IntervalRat) :
    EvalResult Box :=
  match rotation cfg T A with
  | .error err => .error err
  | .ok W =>
    match evaluate cfg H Ks (sampleInput cfg T) with
    | .error err => .error err
    | .ok Z => .ok (mul cfg.precision W Z)

theorem mem_signedEvaluation {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {H : ℕ} {Ks : List ℕ} {T : ℚ} {A : IntervalRat} {B : Box}
    (ha : CertifiedArctan.check cfg (angleArgument T) A.lo A.hi = true)
    (he : signedEvaluation cfg H Ks T A = .ok B) :
    Mem (normalizedWeight 200 (T : ℝ) *
      ZetaBlockApproximation.approximation (point (T : ℝ)) H Ks) B := by
  cases hW : rotation cfg T A with
  | error err => simp [signedEvaluation, hW] at he
  | ok W =>
    cases hZ : evaluate cfg H Ks (sampleInput cfg T) with
    | error err => simp [signedEvaluation, hW, hZ] at he
    | ok Z =>
      simp only [signedEvaluation, hW, hZ, Except.ok.injEq] at he
      subst B
      exact mem_mul (mem_rotation hp ha hW)
        (mem_evaluate hp (by norm_num [point]) (mem_input hp T) H Ks hZ) _

/-- Check geometry, partition validity, the phase bracket and the full signed margin. -/
def signCheck (cfg : DyadicConfig) (H : ℕ) (Ks : List ℕ) (T : ℚ) (A : IntervalRat)
    (positive : Bool) : Bool :=
  decide (|T| ≤ 22000) && admissible cfg H Ks (sampleInput cfg T) &&
    CertifiedArctan.check cfg (angleArgument T) A.lo A.hi &&
    match signedEvaluation cfg H Ks T A with
    | .error _ => false
    | .ok B => decide (if positive then errorAllowance ≤ B.re.lo.toRat
      else B.re.hi.toRat ≤ -errorAllowance)

/-- A successful accelerated check proves the sign of actual Hardy Z and
can be used directly in the existing complete-window matching theorem. -/
theorem hardy_sign_of_check {cfg : DyadicConfig} {H : ℕ} {Ks : List ℕ} {T : ℚ}
    {A : IntervalRat} {positive : Bool} (hc : signCheck cfg H Ks T A positive = true) :
    if positive then 0 < hardy (T : ℝ) else hardy (T : ℝ) < 0 := by
  unfold signCheck at hc
  obtain ⟨⟨⟨hT, hd⟩, ha⟩, hb⟩ := Bool.and_eq_true_iff.mp hc |>.imp_left
    (fun h => Bool.and_eq_true_iff.mp h |>.imp_left Bool.and_eq_true_iff.mp)
  simp only [decide_eq_true_eq] at hT
  have hT' : |(T : ℝ)| ≤ 22000 := by exact_mod_cast hT
  have hp : cfg.precision ≤ 0 :=
    (of_decide_eq_true (Bool.and_eq_true_iff.mp hd).1).1
  have he := (error_of_admissible hd (mem_input hp T)).2.2
  have herr := abs_lt.mp (normalized_error_lt he)
  cases hB : signedEvaluation cfg H Ks T A with
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

end RiemannGaussian.ZetaBlockHardyCertificate
