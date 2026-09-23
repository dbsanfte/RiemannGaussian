/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockCertificate

/-!
# Kernel-checked block validation at height 22000

These small checks exercise direct and compressed polynomial blocks. The
conclusions concern the original finite Dirichlet sums, after paying the
proved polynomial error. They are not a complete low-zero verification.
-/

namespace RiemannGaussian.ZetaBlockValidation
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval
open ZetaBlockCertificate ZetaBlockEnclosure

private def cfg : DyadicConfig := {precision := -48, taylorDepth := 24}

private def input : Box := rational cfg.precision (1 / 2) 22000

private def checkedBlock (K : ℕ) : Bool :=
  match blockBox cfg input (lookup cfg.precision (coefficients cfg.precision input)) 6000 K with
  | .error _ => false
  | .ok B => decide (B.re.hi.toRat ≤ -(9 / 1000 : ℚ) - 1 / 1000000000)

private theorem checked_direct : checkedBlock 18 = true := by decide +kernel

private theorem checked_compressed : checkedBlock 20 = true := by decide +kernel

private theorem original_sum_bound {K : ℕ} (hK : K ≤ 20) (hc : checkedBlock K = true) :
    (∑ k ∈ Finset.range K, (6000 + k : ℂ) ^ (-(1 / 2 + 22000 * Complex.I))).re < -(9 / 1000) := by
  let s : ℂ := 1 / 2 + 22000 * Complex.I
  have hs : Mem s input := by
    simpa [s, input] using mem_rational (show cfg.precision ≤ 0 by decide) (1 / 2) 22000
  have hs0 : 0 < s.re := by norm_num [s]
  have hnorm : ‖s‖ ≤ 22500 := by
    have hh := Complex.norm_le_abs_re_add_abs_im s
    norm_num [s] at hh
    linarith
  have herr := ZetaBlockApproximation.norm_block_error_le hs0.le hnorm
    (v := 6000) (K := K) (by norm_num) (fun k hk => by omega)
  have hr := (Complex.re_le_norm _).trans herr
  simp only [Complex.sub_re] at hr
  cases he : blockBox cfg input (lookup cfg.precision (coefficients cfg.precision input)) 6000 K with
  | error err => simp [checkedBlock, he] at hc
  | ok B =>
    simp only [checkedBlock, he, decide_eq_true_eq] at hc
    have hb := (mem_blockBox (show cfg.precision ≤ 0 by decide) hs0 hs
      (fun j hj => mem_coefficients (show cfg.precision ≤ 0 by decide) hs hj)
      (by norm_num : 0 < (6000 : ℕ)) he).1.2
    have hcast : (B.re.hi.toRat : ℝ) ≤ -(9 / 1000 : ℝ) - 1 / 1000000000 := by
      simpa only [Rat.cast_sub, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
        (Rat.cast_le (K := ℝ)).mpr hc
    have hKR : (K : ℝ) ≤ 20 := by exact_mod_cast hK
    change (∑ k ∈ Finset.range K, (6000 + k : ℂ) ^ (-s)).re < _
    linarith

/-- The original eighteen-term sum is strictly negative, certified through
the direct polynomial fallback and its analytic error. -/
theorem direct_sum_negative :
    (∑ k ∈ Finset.range 18, (6000 + k : ℂ) ^ (-(1 / 2 + 22000 * Complex.I))).re < -(9 / 1000) :=
  original_sum_bound (by norm_num) checked_direct

/-- The original twenty-term sum is strictly negative, certified through
the geometric-moment evaluator and its analytic error. -/
theorem compressed_sum_negative :
    (∑ k ∈ Finset.range 20, (6000 + k : ℂ) ^ (-(1 / 2 + 22000 * Complex.I))).re < -(9 / 1000) :=
  original_sum_bound le_rfl checked_compressed

end RiemannGaussian.ZetaBlockValidation
