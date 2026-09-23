/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockEnclosure
import RiemannGaussian.ZetaEulerMaclaurinCertificate

/-!
# Soundness of the accelerated zeta evaluator

Successful computations enclose the literal shared-polynomial approximation.
The separately proved analytic error is paid in the final zeta bound.
Partition validity and the original Euler--Maclaurin domain are checked,
not assumed as facts about an unverified zero table.
-/

namespace RiemannGaussian.ZetaBlockCertificate
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval
open ZetaBlockEnclosure ZetaEulerMaclaurinEnclosure

private def rat (prec : ℤ) (a : ℚ) : Box := rational prec a 0

private theorem mem_rat {prec : ℤ} (hp : prec ≤ 0) (a : ℚ) :
    Mem (a : ℂ) (rat prec a) := by
  simpa only [rat, Rat.cast_zero, zero_mul, add_zero] using mem_rational hp a 0

/-- Evaluate one block, using the shared coefficient table. -/
def blockBox (cfg : DyadicConfig) (A : Box) (C : ℕ → Box) (v K : ℕ) : EvalResult Box :=
  match natPower cfg v (neg A) with
  | .error err => .error err
  | .ok P =>
      match CertifiedComplexInterval.exp cfg (mul cfg.precision (neg A) (rat cfg.precision (1 / (v : ℚ)))) with
      | .error err => .error err
      | .ok Q => .ok (mul cfg.precision P (polynomialBlock cfg C Q (300 / (v : ℚ)) K))

theorem mem_blockBox {cfg : DyadicConfig} (hp : cfg.precision ≤ 0) {s : ℂ}
    (hs0 : 0 < s.re) {A B : Box} (hs : Mem s A) {C : ℕ → Box}
    (hc : ∀ j < 19, Mem (ZetaBlockTaylor.coefficient s j) (C j))
    {v K : ℕ} (hv : 0 < v) (he : blockBox cfg A C v K = .ok B) :
    Mem (ZetaBlockApproximation.block s v K) B := by
  have hq : Complex.exp (-s / v) ≠ 1 := by
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv
    have hn : ‖Complex.exp (-s / v)‖ < 1 := by
      rw [Complex.norm_exp, Real.exp_lt_one_iff]
      rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.neg_re]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hs0) hvR
    intro hh
    rw [hh, norm_one] at hn
    exact (lt_self_iff_false 1).mp hn
  cases hP : natPower cfg v (neg A) with
  | error err => simp [blockBox, hP] at he
  | ok P =>
    cases hQ : CertifiedComplexInterval.exp cfg
        (mul cfg.precision (neg A) (rat cfg.precision (1 / (v : ℚ)))) with
    | error err => simp only [blockBox, hP, hQ, reduceCtorEq] at he
    | ok Q =>
      simp only [blockBox, hP, hQ, Except.ok.injEq] at he
      subst B
      have hin : Mem (-s / v) (mul cfg.precision (neg A) (rat cfg.precision (1 / (v : ℚ)))) := by
        simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, div_eq_mul_inv, Rat.cast_inv, one_mul]
          using mem_mul (mem_neg hs) (mem_rat hp (1 / (v : ℚ))) cfg.precision
      have hm := mem_polynomialBlock hp hq (mem_exp hp hin hQ) hc (300 / (v : ℚ)) K
      rw [ZetaBlockMoments.sum_polynomial_eq_moments] at hm
      rw [ZetaBlockMoments.block_eq_moments]
      exact mem_mul (mem_natPower hp hv (mem_neg hs) hP)
        (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using hm) cfg.precision

/-- Sum a literal consecutive list of blocks. -/
def partitionBox (cfg : DyadicConfig) (A : Box) (C : ℕ → Box) : ℕ → List ℕ → EvalResult Box
  | _, [] => .ok (rat cfg.precision 0)
  | v, K :: Ks =>
      match blockBox cfg A C v K with
      | .error err => .error err
      | .ok B =>
          match partitionBox cfg A C (v + K) Ks with
          | .error err => .error err
          | .ok P => .ok (add cfg.precision B P)

theorem mem_partitionBox {cfg : DyadicConfig} (hp : cfg.precision ≤ 0) {s : ℂ}
    (hs0 : 0 < s.re) {A : Box} (hs : Mem s A) {C : ℕ → Box}
    (hc : ∀ j < 19, Mem (ZetaBlockTaylor.coefficient s j) (C j))
    (Ks : List ℕ) {v : ℕ} (hv : 0 < v) {B : Box}
    (he : partitionBox cfg A C v Ks = .ok B) :
    Mem (ZetaBlockApproximation.partition s v Ks) B := by
  induction Ks generalizing v B with
  | nil =>
    simp only [partitionBox, Except.ok.injEq] at he
    subst B
    simpa only [ZetaBlockApproximation.partition, Rat.cast_zero] using mem_rat hp 0
  | cons K Ks ih =>
    cases hB : blockBox cfg A C v K with
    | error err => simp [partitionBox, hB] at he
    | ok B0 =>
      cases hP : partitionBox cfg A C (v + K) Ks with
      | error err => simp [partitionBox, hB, hP] at he
      | ok P =>
        simp only [partitionBox, hB, hP, Except.ok.injEq] at he
        subst B
        exact mem_add (mem_blockBox hp hs0 hs hc hv hB) (ih (by omega) hP) cfg.precision

/-- The entire accelerated evaluator, preserving the original correction. -/
def evaluate (cfg : DyadicConfig) (H : ℕ) (Ks : List ℕ) (A : Box) : EvalResult Box :=
  let C := coefficients cfg.precision A
  let N := H + Ks.sum
  match prefixBox cfg A H with
  | .error err => .error err
  | .ok P =>
    match partitionBox cfg A (lookup cfg.precision C) (H + 1) Ks with
    | .error err => .error err
    | .ok B =>
      match natPower cfg (N + 1) (neg A) with
      | .error err => .error err
      | .ok Q =>
        match inv cfg (add cfg.precision A (rat cfg.precision (-1))) with
        | .error err => .error err
        | .ok U => .ok (add cfg.precision (add cfg.precision P B) (mul cfg.precision Q
          (add cfg.precision
            (add cfg.precision (mul cfg.precision (rat cfg.precision (N + 1)) U)
              (rat cfg.precision (1 / 2)))
            (correctionBox cfg.precision N A 19))))

theorem mem_evaluate {cfg : DyadicConfig} (hp : cfg.precision ≤ 0) {s : ℂ}
    (hs0 : 0 < s.re) {A B : Box} (hs : Mem s A) (H : ℕ) (Ks : List ℕ)
    (he : evaluate cfg H Ks A = .ok B) : Mem (ZetaBlockApproximation.approximation s H Ks) B := by
  let C := coefficients cfg.precision A
  let N := H + Ks.sum
  cases hP : prefixBox cfg A H with
  | error err => simp [evaluate, hP] at he
  | ok P =>
    cases hB : partitionBox cfg A (lookup cfg.precision C) (H + 1) Ks with
    | error err =>
      dsimp only [C] at hB
      simp only [evaluate, hP, hB, reduceCtorEq] at he
    | ok B0 =>
      dsimp only [C] at hB
      cases hQ : natPower cfg (N + 1) (neg A) with
      | error err =>
        dsimp only [N] at hQ
        simp only [evaluate, hP, hB, hQ, reduceCtorEq] at he
      | ok Q =>
        dsimp only [N] at hQ
        cases hU : inv cfg (add cfg.precision A (rat cfg.precision (-1))) with
        | error err => simp only [evaluate, hP, hB, hQ, hU, reduceCtorEq] at he
        | ok U =>
          simp only [evaluate, hP, hB, hQ, hU, Except.ok.injEq] at he
          subst B
          have hu : Mem (s - 1)⁻¹ U := mem_inv hp
            (by simpa [sub_eq_add_neg] using mem_add hs (mem_rat hp (-1)) cfg.precision) hU
          have hm := mem_add (mem_add (mem_prefix hp hs H hP)
            (mem_partitionBox hp hs0 hs (fun j hj => mem_coefficients hp hs hj)
              Ks (Nat.succ_pos H) hB) cfg.precision)
            (mem_mul (mem_natPower hp (Nat.succ_pos N) (mem_neg hs) hQ)
              (mem_add (mem_add (mem_mul (mem_rat hp (N + 1)) hu cfg.precision)
                (mem_rat hp (1 / 2)) cfg.precision)
                (mem_correctionBox hp hs N 19) cfg.precision) cfg.precision) cfg.precision
          rw [ZetaBlockApproximation.approximation, approximation_factored,
            add_sub_cancel_left, ZetaBlockApproximation.prefixValue]
          simpa only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_div,
            Rat.cast_ofNat, div_eq_mul_inv, Rat.cast_mul, Rat.cast_inv, Nat.cast_succ, N] using hm

/-- Check the literal width list using integer arithmetic. -/
def validCheck : ℕ → List ℕ → Bool
  | _, [] => true
  | v, K :: Ks => decide (300 * (K - 1) ≤ v) && validCheck (v + K) Ks

theorem valid_of_check (v : ℕ) (Ks : List ℕ) (hc : validCheck v Ks = true) :
    ZetaBlockApproximation.Valid v Ks := by
  induction Ks generalizing v with
  | nil => trivial
  | cons K Ks ih =>
    obtain ⟨hK, hr⟩ := Bool.and_eq_true_iff.mp hc
    have hh := of_decide_eq_true hK
    exact ⟨fun k hk => (Nat.mul_le_mul_left 300 (by omega : k ≤ K - 1)).trans hh,
      ih (v + K) hr⟩

/-- A bounded construction of consecutive widths; its output is checked
separately for validity and total coverage. -/
def widths (N : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | steps + 1, v =>
      if v ≤ N then
        let K := min (N + 1 - v) ((v + 299) / 300)
        K :: widths N steps (v + K)
      else []

/-- Total error allowance: block approximation plus the original analytic tail. -/
def errorAllowance : ℚ := 1 / 1000000000

/-- Check the original analytic domain and every actual block width. -/
def admissible (cfg : DyadicConfig) (H : ℕ) (Ks : List ℕ) (A : Box) : Bool :=
  ZetaEulerMaclaurinCertificate.admissible cfg (H + Ks.sum) A && validCheck (H + 1) Ks

/-- The executable domain check pays the complete approximation error. -/
theorem error_of_admissible {cfg : DyadicConfig} {H : ℕ} {Ks : List ℕ} {A : Box}
    (ha : admissible cfg H Ks A = true) {s : ℂ} (hs : Mem s A) :
    cfg.precision ≤ 0 ∧ 0 < s.re ∧
      ‖riemannZeta s - ZetaBlockApproximation.approximation s H Ks‖ < (errorAllowance : ℝ) := by
  obtain ⟨hd, hv⟩ := Bool.and_eq_true_iff.mp ha
  have he := (ZetaEulerMaclaurinCertificate.error_of_admissible hd hs).2
  have hd' := of_decide_eq_true hd
  obtain ⟨hp, hN, hsig, hnorm, _hne⟩ := hd'
  have hsig' : (1 / 2 : ℝ) ≤ s.re := by
    have hh : (1 / 2 : ℝ) ≤ (A.re.lo.toRat : ℝ) := by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr hsig
    exact hh.trans hs.1.1
  have hN' : (H + Ks.sum : ℝ) ≤ 22020 := by exact_mod_cast hN
  have hnorm' : ‖s‖ + 20 ≤ (H + Ks.sum + 1 : ℝ) := by
    have hh : (ZetaEulerMaclaurinCertificate.magnitude A.re : ℝ) +
        (ZetaEulerMaclaurinCertificate.magnitude A.im : ℝ) + 20 ≤ (H + Ks.sum + 1 : ℝ) := by
      exact_mod_cast hnorm
    have hn := (Complex.norm_le_abs_re_add_abs_im s).trans
      (add_le_add (ZetaEulerMaclaurinCertificate.abs_le_magnitude hs.1)
        (ZetaEulerMaclaurinCertificate.abs_le_magnitude hs.2))
    linarith
  have hpref := ZetaBlockApproximation.norm_prefix_error_le (by linarith : 0 ≤ s.re)
    (by linarith : ‖s‖ ≤ 22500) H Ks (valid_of_check _ _ hv)
  have hsize : (Ks.sum : ℝ) ≤ 22020 := by
    have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg H
    linarith
  refine ⟨hp, by linarith, ?_⟩
  have hid : riemannZeta s - ZetaBlockApproximation.approximation s H Ks =
      (riemannZeta s - ZetaEulerMaclaurin.approximation (H + Ks.sum) s 18) +
      (ZetaEulerCell.partialSum (H + Ks.sum) s - ZetaBlockApproximation.prefixValue s H Ks) := by
    unfold ZetaBlockApproximation.approximation
    ring
  rw [hid]
  apply (norm_add_le _ _).trans_lt
  norm_num only [ZetaEulerMaclaurinCertificate.errorAllowance, Rat.cast_div,
    Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] at he
  norm_num only [errorAllowance, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  linarith

/-- Successful accelerated evaluation gives bounds on both coordinates of
actual zeta, including the full analytic and polynomial errors. -/
theorem coordinate_bounds {cfg : DyadicConfig} {H : ℕ} {Ks : List ℕ} {A B : Box}
    (ha : admissible cfg H Ks A = true) (he : evaluate cfg H Ks A = .ok B)
    {s : ℂ} (hs : Mem s A) :
    (B.re.lo.toRat : ℝ) - errorAllowance < (riemannZeta s).re ∧
    (riemannZeta s).re < (B.re.hi.toRat : ℝ) + errorAllowance ∧
    (B.im.lo.toRat : ℝ) - errorAllowance < (riemannZeta s).im ∧
    (riemannZeta s).im < (B.im.hi.toRat : ℝ) + errorAllowance := by
  obtain ⟨hp, hs0, herr⟩ := error_of_admissible ha hs
  have hb := mem_evaluate hp hs0 hs H Ks he
  have hr := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt herr)
  have hi := abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt herr)
  simp only [Complex.sub_re, Complex.sub_im] at hr hi
  obtain ⟨⟨hlr, hur⟩, ⟨hli, hui⟩⟩ := hb
  exact ⟨by linarith [hr.1], by linarith [hr.2], by linarith [hi.1], by linarith [hi.2]⟩

/-- Separation by the total error allowance in a signed coordinate. -/
def separated (B : Box) : Bool := decide
  (B.re.hi.toRat ≤ -errorAllowance ∨ errorAllowance ≤ B.re.lo.toRat ∨
    B.im.hi.toRat ≤ -errorAllowance ∨ errorAllowance ≤ B.im.lo.toRat)

/-- A completely checked zero-exclusion test for the accelerated evaluator. -/
def check (cfg : DyadicConfig) (H : ℕ) (Ks : List ℕ) (A : Box) : Bool :=
  admissible cfg H Ks A && match evaluate cfg H Ks A with
    | .error _ => false
    | .ok B => separated B

theorem nonzero_of_check {cfg : DyadicConfig} {H : ℕ} {Ks : List ℕ} {A : Box}
    (hc : check cfg H Ks A = true) {s : ℂ} (hs : Mem s A) : riemannZeta s ≠ 0 := by
  obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hc
  cases he : evaluate cfg H Ks A with
  | error err => simp only [he, Bool.false_eq_true] at hb
  | ok B =>
    simp only [he, separated, decide_eq_true_eq] at hb
    obtain ⟨hlr, hur, hli, hui⟩ := coordinate_bounds ha he hs
    intro hz
    rw [hz] at hlr hur hli hui
    rcases hb with h | h | h | h
    · have hh : (B.re.hi.toRat : ℝ) ≤ -(errorAllowance : ℝ) := by exact_mod_cast h
      norm_num at hur
      linarith
    · have hh : (errorAllowance : ℝ) ≤ (B.re.lo.toRat : ℝ) := by exact_mod_cast h
      norm_num at hlr
      linarith
    · have hh : (B.im.hi.toRat : ℝ) ≤ -(errorAllowance : ℝ) := by exact_mod_cast h
      norm_num at hui
      linarith
    · have hh : (errorAllowance : ℝ) ≤ (B.im.lo.toRat : ℝ) := by exact_mod_cast h
      norm_num at hli
      linarith

end RiemannGaussian.ZetaBlockCertificate
