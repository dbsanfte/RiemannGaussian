/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockBatchPrefix

/-!
# Sound zeta evaluation from a cached batch

Preparation is checked once and its soundness is reusable at every sample.
The evaluator pays both polynomial errors and the original analytic tail.
Every sample still checks its actual geometry and its full shift radius.
-/

namespace RiemannGaussian.ZetaBlockBatchCertificate
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaBlockEnclosure
open ZetaBlockBatchEnclosure ZetaEulerMaclaurinEnclosure

private def rat (prec : ℤ) (a : ℚ) : Box := rational prec a 0

private theorem mem_rat {prec : ℤ} (hp : prec ≤ 0) (a : ℚ) :
    Mem (a : ℂ) (rat prec a) := by
  simpa only [rat, Rat.cast_zero, zero_mul, add_zero] using mem_rational hp a 0

/-- Cached exact early terms and complete consecutive block packets. -/
structure Batch where
  /-- Exact early-term values and their phase increments. -/
  head : List (Box × Box)
  /-- Reusable center amplitudes and block phase increments. -/
  blocks : List ZetaBlockBatchPacket.Packet

/-- Mathematical meaning of the complete stored batch. -/
def Sound (prec : ℤ) (s d q : ℂ) (H : ℕ) (Ks : List ℕ) (B : Batch) : Prop :=
  ZetaBlockBatchPrefix.Sound (s + d) q H B.head ∧
    ZetaBlockBatchPacket.SoundList prec s d q (H + 1) Ks B.blocks

/-- Materialize all shared data once, before evaluating any sample. -/
def prepare (cfg : DyadicConfig) (H : ℕ) (Ks : List ℕ) (A D Q : Box) : EvalResult Batch :=
  let C := coefficients cfg.precision A
  match ZetaBlockBatchPrefix.prepare cfg (add cfg.precision A D) Q H with
  | .error err => .error err
  | .ok P =>
      match ZetaBlockBatchPacket.prepareList cfg A D Q (lookup cfg.precision C) (H + 1) Ks with
      | .error err => .error err
      | .ok Ps => .ok ⟨P, Ps⟩

theorem sound_prepare {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s d q : ℂ} (hs0 : 0 < s.re) {A D Q : Box}
    (hs : Mem s A) (hd : Mem d D) (hq : Mem q Q) (H : ℕ) (Ks : List ℕ) {B : Batch}
    (he : prepare cfg H Ks A D Q = .ok B) : Sound cfg.precision s d q H Ks B := by
  cases hP : ZetaBlockBatchPrefix.prepare cfg (add cfg.precision A D) Q H with
  | error err => simp only [prepare, hP, reduceCtorEq] at he
  | ok P =>
    cases hPs : ZetaBlockBatchPacket.prepareList cfg A D Q
        (lookup cfg.precision (coefficients cfg.precision A)) (H + 1) Ks with
    | error err => simp only [prepare, hP, hPs, reduceCtorEq] at he
    | ok Ps =>
      simp only [prepare, hP, hPs, Except.ok.injEq] at he
      subst B
      exact ⟨ZetaBlockBatchPrefix.sound_prepare hp (mem_add hs hd cfg.precision) hq H hP,
        ZetaBlockBatchPacket.sound_prepareList hp hs0 hs hd hq
          (fun l hl => mem_coefficients hp hs hl) Ks (Nat.succ_pos H) hPs⟩

/-- Evaluate one shifted sample from the cache and the full analytic correction. -/
def evaluate (cfg : DyadicConfig) (N : ℕ) (B : Batch) (A D : Box) (j : ℕ) : EvalResult Box :=
  let C := shiftCoefficients cfg.precision D
  let P := add cfg.precision (ZetaBlockBatchPrefix.evaluate cfg.precision j B.head)
    (ZetaBlockBatchPacket.evaluateList cfg.precision (lookup cfg.precision C) j B.blocks)
  match natPower cfg (N + 1) (neg A) with
  | .error err => .error err
  | .ok Q =>
    match inv cfg (add cfg.precision A (rat cfg.precision (-1))) with
    | .error err => .error err
    | .ok U => .ok (add cfg.precision P (mul cfg.precision Q
        (add cfg.precision
          (add cfg.precision (mul cfg.precision (rat cfg.precision (N + 1)) U)
            (rat cfg.precision (1 / 2)))
          (correctionBox cfg.precision N A 19))))

theorem mem_evaluate {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s d q : ℂ} {H : ℕ} {Ks : List ℕ} {B : Batch}
    (hB : Sound cfg.precision s d q H Ks B) (j : ℕ) {A D Z : Box}
    (hs : Mem (s + (d + j * q)) A) (hd : Mem (d + j * q) D)
    (he : evaluate cfg (H + Ks.sum) B A D j = .ok Z) :
    Mem (ZetaBlockBatch.approximation s (d + j * q) H Ks) Z := by
  cases hQ : natPower cfg (H + Ks.sum + 1) (neg A) with
  | error err => simp only [evaluate, hQ, reduceCtorEq] at he
  | ok Q =>
    cases hU : inv cfg (add cfg.precision A (rat cfg.precision (-1))) with
    | error err => simp only [evaluate, hQ, hU, reduceCtorEq] at he
    | ok U =>
      simp only [evaluate, hQ, hU, Except.ok.injEq] at he
      subst Z
      have hu : Mem (s + (d + j * q) - 1)⁻¹ U := mem_inv hp
        (by simpa [sub_eq_add_neg] using mem_add hs (mem_rat hp (-1)) cfg.precision) hU
      have hhead := ZetaBlockBatchPrefix.mem_evaluate hp H hB.1 j
      rw [add_assoc] at hhead
      have hblocks := ZetaBlockBatchPacket.mem_evaluateList hp Ks (Nat.succ_pos H) hB.2 j
        (fun l hl => mem_shiftCoefficients hp hd hl)
      have hm := mem_add (mem_add hhead hblocks cfg.precision)
        (mem_mul (mem_natPower hp (Nat.succ_pos (H + Ks.sum)) (mem_neg hs) hQ)
          (mem_add (mem_add (mem_mul (mem_rat hp (H + Ks.sum + 1)) hu cfg.precision)
            (mem_rat hp (1 / 2)) cfg.precision)
            (mem_correctionBox hp hs (H + Ks.sum) 19) cfg.precision) cfg.precision) cfg.precision
      rw [ZetaBlockBatch.approximation, approximation_factored,
        add_sub_cancel_left, ZetaBlockBatch.prefixValue]
      simpa only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_div,
        Rat.cast_ofNat, div_eq_mul_inv, Rat.cast_mul, Rat.cast_inv, Nat.cast_succ,
        Nat.cast_add] using hm

/-- Check center size, a purely imaginary shift of radius 64, the actual sample
domain and every literal block width. -/
def admissible (cfg : DyadicConfig) (H : ℕ) (Ks : List ℕ) (S A D : Box) : Bool :=
  ZetaEulerMaclaurinCertificate.admissible cfg (H + Ks.sum) A &&
    ZetaBlockCertificate.validCheck (H + 1) Ks && decide
      ((1 / 2 : ℚ) ≤ S.re.lo.toRat ∧
        ZetaEulerMaclaurinCertificate.magnitude S.re +
          ZetaEulerMaclaurinCertificate.magnitude S.im ≤ 22500 ∧
        D.re.lo.toRat = 0 ∧ D.re.hi.toRat = 0 ∧
        ZetaEulerMaclaurinCertificate.magnitude D.im ≤ 64)

/-- The cache does not weaken any analytic condition or error allowance. -/
theorem error_of_admissible {cfg : DyadicConfig} {H : ℕ} {Ks : List ℕ} {S A D : Box}
    (ha : admissible cfg H Ks S A D = true) {s d : ℂ}
    (hs : Mem s S) (ht : Mem (s + d) A) (hd : Mem d D) :
    cfg.precision ≤ 0 ∧ 0 < s.re ∧
      ‖riemannZeta (s + d) - ZetaBlockBatch.approximation s d H Ks‖ <
        (ZetaBlockCertificate.errorAllowance : ℝ) := by
  obtain ⟨hleft, hcenter⟩ := Bool.and_eq_true_iff.mp ha
  obtain ⟨hdom, hvalid⟩ := Bool.and_eq_true_iff.mp hleft
  obtain ⟨hsig, hnorm, hdlo, hdhi, hdnorm⟩ := of_decide_eq_true hcenter
  obtain ⟨hp, herr⟩ := ZetaEulerMaclaurinCertificate.error_of_admissible hdom ht
  have hN : H + Ks.sum ≤ 22020 := (of_decide_eq_true hdom).2.1
  have hs0 : 1 / 2 ≤ s.re := by
    have hh : (1 / 2 : ℝ) ≤ S.re.lo.toRat := by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_le (K := ℝ)).mpr hsig
    exact hh.trans hs.1.1
  have hn : ‖s‖ ≤ 22500 := by
    have hh : (ZetaEulerMaclaurinCertificate.magnitude S.re : ℝ) +
        (ZetaEulerMaclaurinCertificate.magnitude S.im : ℝ) ≤ 22500 := by exact_mod_cast hnorm
    exact ((Complex.norm_le_abs_re_add_abs_im s).trans
      (add_le_add (ZetaEulerMaclaurinCertificate.abs_le_magnitude hs.1)
        (ZetaEulerMaclaurinCertificate.abs_le_magnitude hs.2))).trans hh
  have hd0 : d.re = 0 := by
    have hlo : (D.re.lo.toRat : ℝ) = 0 := by exact_mod_cast hdlo
    have hhi : (D.re.hi.toRat : ℝ) = 0 := by exact_mod_cast hdhi
    linarith [hd.1.1, hd.1.2]
  have hnD : ‖d‖ ≤ 64 := by
    have hh : (ZetaEulerMaclaurinCertificate.magnitude D.im : ℝ) ≤ 64 := by exact_mod_cast hdnorm
    have hh' := Complex.norm_le_abs_re_add_abs_im d
    rw [hd0, abs_zero, zero_add] at hh'
    exact hh'.trans ((ZetaEulerMaclaurinCertificate.abs_le_magnitude hd.2).trans hh)
  have hprefix := ZetaBlockBatch.norm_prefix_error_le (by linarith : 0 ≤ s.re) hn hd0 hnD
    H Ks (ZetaBlockCertificate.valid_of_check _ _ hvalid)
  have hsize : (Ks.sum : ℝ) ≤ 22020 := by exact_mod_cast (by omega : Ks.sum ≤ 22020)
  refine ⟨hp, by linarith, ?_⟩
  have hid : riemannZeta (s + d) - ZetaBlockBatch.approximation s d H Ks =
      (riemannZeta (s + d) - ZetaEulerMaclaurin.approximation (H + Ks.sum) (s + d) 18) +
      (ZetaEulerCell.partialSum (H + Ks.sum) (s + d) - ZetaBlockBatch.prefixValue s d H Ks) := by
    unfold ZetaBlockBatch.approximation
    ring
  rw [hid]
  apply (norm_add_le _ _).trans_lt
  norm_num only [ZetaEulerMaclaurinCertificate.errorAllowance, Rat.cast_div,
    Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] at herr
  norm_num only [ZetaBlockCertificate.errorAllowance, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  linarith

/-- Coordinate bounds apply to actual zeta after paying the complete error. -/
theorem coordinate_bounds {cfg : DyadicConfig} {H : ℕ} {Ks : List ℕ} {S A D Z : Box}
    {s d q : ℂ} {B : Batch} (hB : Sound cfg.precision s d q H Ks B) (j : ℕ)
    (ha : admissible cfg H Ks S A D = true)
    (he : evaluate cfg (H + Ks.sum) B A D j = .ok Z)
    (hs : Mem s S) (ht : Mem (s + (d + j * q)) A) (hd : Mem (d + j * q) D) :
    (Z.re.lo.toRat : ℝ) - ZetaBlockCertificate.errorAllowance < (riemannZeta (s + (d + j * q))).re ∧
    (riemannZeta (s + (d + j * q))).re < (Z.re.hi.toRat : ℝ) + ZetaBlockCertificate.errorAllowance ∧
    (Z.im.lo.toRat : ℝ) - ZetaBlockCertificate.errorAllowance < (riemannZeta (s + (d + j * q))).im ∧
    (riemannZeta (s + (d + j * q))).im < (Z.im.hi.toRat : ℝ) + ZetaBlockCertificate.errorAllowance := by
  obtain ⟨hp, _, herr⟩ := error_of_admissible ha hs ht hd
  have hb := mem_evaluate hp hB j ht hd he
  have hr := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt herr)
  have hi := abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt herr)
  simp only [Complex.sub_re, Complex.sub_im] at hr hi
  obtain ⟨⟨hlr, hur⟩, ⟨hli, hui⟩⟩ := hb
  exact ⟨by linarith [hr.1], by linarith [hr.2], by linarith [hi.1], by linarith [hi.2]⟩

/-- A sample test uses the prepared data but checks its own geometry and margin. -/
def check (cfg : DyadicConfig) (H : ℕ) (Ks : List ℕ) (B : Batch) (S A D : Box) (j : ℕ) : Bool :=
  admissible cfg H Ks S A D && match evaluate cfg (H + Ks.sum) B A D j with
    | .error _ => false
    | .ok Z => ZetaBlockCertificate.separated Z

/-- With a proved cache, every successful sample check proves actual nonvanishing. -/
theorem nonzero_of_check {cfg : DyadicConfig} {H : ℕ} {Ks : List ℕ} {S A D : Box}
    {s d q : ℂ} {B : Batch} (hB : Sound cfg.precision s d q H Ks B) (j : ℕ)
    (hc : check cfg H Ks B S A D j = true)
    (hs : Mem s S) (ht : Mem (s + (d + j * q)) A) (hd : Mem (d + j * q) D) :
    riemannZeta (s + (d + j * q)) ≠ 0 := by
  obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hc
  cases he : evaluate cfg (H + Ks.sum) B A D j with
  | error err => simp only [he, Bool.false_eq_true] at hb
  | ok Z =>
    simp only [he, ZetaBlockCertificate.separated, decide_eq_true_eq] at hb
    obtain ⟨hlr, hur, hli, hui⟩ := coordinate_bounds hB j ha he hs ht hd
    intro hz
    simp only [hz, Complex.zero_re, Complex.zero_im] at hlr hur hli hui
    rcases hb with hb | hb | hb | hb
    · have hh : (Z.re.hi.toRat : ℝ) ≤ -(ZetaBlockCertificate.errorAllowance : ℝ) := by exact_mod_cast hb
      linarith
    · have hh : (ZetaBlockCertificate.errorAllowance : ℝ) ≤ Z.re.lo.toRat := by exact_mod_cast hb
      linarith
    · have hh : (Z.im.hi.toRat : ℝ) ≤ -(ZetaBlockCertificate.errorAllowance : ℝ) := by exact_mod_cast hb
      linarith
    · have hh : (ZetaBlockCertificate.errorAllowance : ℝ) ≤ Z.im.lo.toRat := by exact_mod_cast hb
      linarith

end RiemannGaussian.ZetaBlockBatchCertificate
