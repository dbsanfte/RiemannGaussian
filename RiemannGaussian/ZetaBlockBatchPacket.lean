/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockBatchEnclosure
import RiemannGaussian.ZetaBlockCertificate

/-!
# Certified reusable packets for a lattice of sample heights

The center amplitudes and initial/step phases are evaluated once. Packet
soundness can then be reused for any sample index; the polynomial's analytic
error is handled separately and requires the stated radius restriction.
-/

namespace RiemannGaussian.ZetaBlockBatchPacket
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaBlockEnclosure
open ZetaBlockBatchEnclosure

private def rat (prec : ℤ) (a : ℚ) : Box := rational prec a 0

private theorem mem_rat {prec : ℤ} (hp : prec ≤ 0) (a : ℚ) :
    Mem (a : ℂ) (rat prec a) := by
  simpa only [rat, Rat.cast_zero, zero_mul, add_zero] using mem_rational hp a 0

/-- Store all center amplitudes together with the two phases for a height lattice. -/
structure Packet where
  /-- Thirteen reusable center amplitudes, including the outer center power. -/
  amplitudes : Array Box
  /-- Outer phase at the first height shift. -/
  initial : Box
  /-- Multiplicative phase increment between consecutive sample heights. -/
  step : Box

/-- Literal mathematical meaning of all stored packet fields. -/
def Sound (prec : ℤ) (s d q : ℂ) (v K : ℕ) (P : Packet) : Prop :=
  (∀ j < 13, Mem (ZetaBlockBatch.amplitude s v K j) (lookup prec P.amplitudes j)) ∧
    Mem ((v : ℂ) ^ (-d)) P.initial ∧ Mem ((v : ℂ) ^ (-q)) P.step

/-- Prepare the expensive center data and the two reusable outer phases. -/
def prepare (cfg : DyadicConfig) (A D Q : Box) (C : ℕ → Box) (v K : ℕ) : EvalResult Packet :=
  match natPower cfg v (neg A) with
  | .error err => .error err
  | .ok P =>
    match CertifiedComplexInterval.exp cfg (mul cfg.precision (neg A) (rat cfg.precision (1 / (v : ℚ)))) with
    | .error err => .error err
    | .ok G =>
      match natPower cfg v (neg D) with
      | .error err => .error err
      | .ok V =>
        match natPower cfg v (neg Q) with
        | .error err => .error err
        | .ok W => .ok ⟨(amplitudeTable cfg C G (300 / (v : ℚ)) K).map
          (mul cfg.precision P), V, W⟩

theorem sound_prepare {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s d q : ℂ} (hs0 : 0 < s.re) {A D Q : Box}
    (hs : Mem s A) (hd : Mem d D) (hq : Mem q Q) {C : ℕ → Box}
    (hc : ∀ j < 19, Mem (ZetaBlockTaylor.coefficient s j) (C j))
    {v K : ℕ} (hv : 0 < v) {P : Packet}
    (he : prepare cfg A D Q C v K = .ok P) : Sound cfg.precision s d q v K P := by
  have hg : Complex.exp (-s / v) ≠ 1 := by
    have hvR : (0 : ℝ) < v := by exact_mod_cast hv
    have hn : ‖Complex.exp (-s / v)‖ < 1 := by
      rw [Complex.norm_exp, Real.exp_lt_one_iff]
      rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.neg_re]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hs0) hvR
    intro hh
    rw [hh, norm_one] at hn
    exact (lt_self_iff_false 1).mp hn
  cases hP : natPower cfg v (neg A) with
  | error err => simp [prepare, hP] at he
  | ok P0 =>
    cases hG : CertifiedComplexInterval.exp cfg
        (mul cfg.precision (neg A) (rat cfg.precision (1 / (v : ℚ)))) with
    | error err => simp only [prepare, hP, hG, reduceCtorEq] at he
    | ok G =>
      cases hV : natPower cfg v (neg D) with
      | error err => simp only [prepare, hP, hG, hV, reduceCtorEq] at he
      | ok V =>
        cases hW : natPower cfg v (neg Q) with
        | error err => simp only [prepare, hP, hG, hV, hW, reduceCtorEq] at he
        | ok W =>
          simp only [prepare, hP, hG, hV, hW, Except.ok.injEq] at he
          subst P
          refine ⟨?_, mem_natPower hp hv (mem_neg hd) hV, mem_natPower hp hv (mem_neg hq) hW⟩
          intro j hj
          have hin : Mem (-s / v) (mul cfg.precision (neg A) (rat cfg.precision (1 / (v : ℚ)))) := by
            simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, div_eq_mul_inv,
              Rat.cast_inv, one_mul] using mem_mul (mem_neg hs) (mem_rat hp (1 / (v : ℚ))) cfg.precision
          have hm := mem_amplitudeTable hp hg (mem_exp hp hin hG) hc (300 / (v : ℚ)) K hj
          have hh := mem_mul (mem_natPower hp hv (mem_neg hs) hP) hm cfg.precision
          rw [ZetaBlockBatch.amplitude_eq_sum]
          have hsize : j < (amplitudeTable cfg C G (300 / (v : ℚ)) K).size := by
            simpa only [size_amplitudeTable] using hj
          simpa only [lookup, Array.getD_eq_getD_getElem?, Array.getElem?_map,
            Array.getElem?_eq_getElem hsize, Option.map_some, Option.getD_some,
            Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using hh

/-- Exact lattice law for the original complex powers. -/
theorem power_lattice (v : ℕ) (hv : 0 < v) (d q : ℂ) (j : ℕ) :
    (v : ℂ) ^ (-d) * ((v : ℂ) ^ (-q)) ^ j = (v : ℂ) ^ (-(d + j * q)) := by
  have hvC : (v : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  rw [Complex.cpow_def_of_ne_zero hvC, Complex.cpow_def_of_ne_zero hvC,
    Complex.cpow_def_of_ne_zero hvC, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  ring

/-- Cheap sample evaluation from stored amplitudes and the shared shift coefficients. -/
def evaluate (prec : ℤ) (P : Packet) (D : ℕ → Box) (j : ℕ) : Box :=
  mul prec (phaseAt prec P.initial P.step j)
    (sumBox prec (fun l => mul prec (D l) (lookup prec P.amplitudes l)) 13)

theorem mem_evaluate {prec : ℤ} (hp : prec ≤ 0) {s d q : ℂ} {v K : ℕ}
    (hv : 0 < v) {P : Packet} (hP : Sound prec s d q v K P) (j : ℕ) {D : ℕ → Box}
    (hD : ∀ l < 13, Mem (ZetaBlockShift.coefficient (d + j * q) l) (D l)) :
    Mem (ZetaBlockBatch.block s (d + j * q) v K) (evaluate prec P D j) := by
  rw [ZetaBlockBatch.block_eq_amplitudes]
  apply mem_mul _ (mem_sumBox hp 13 (fun l hl => mem_mul (hD l hl) (hP.1 l hl) prec))
  rw [← power_lattice v hv]
  exact mem_phaseAt hp hP.2.1 hP.2.2 j

/-- The stored packet list matches the full consecutive partition. -/
def SoundList (prec : ℤ) (s d q : ℂ) : ℕ → List ℕ → List Packet → Prop
  | _, [], [] => True
  | v, K :: Ks, P :: Ps => Sound prec s d q v K P ∧ SoundList prec s d q (v + K) Ks Ps
  | _, _, _ => False

/-- Prepare every block once, sharing the center's coefficient table. -/
def prepareList (cfg : DyadicConfig) (A D Q : Box) (C : ℕ → Box) :
    ℕ → List ℕ → EvalResult (List Packet)
  | _, [] => .ok []
  | v, K :: Ks =>
      match prepare cfg A D Q C v K with
      | .error err => .error err
      | .ok P =>
          match prepareList cfg A D Q C (v + K) Ks with
          | .error err => .error err
          | .ok Ps => .ok (P :: Ps)

theorem sound_prepareList {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s d q : ℂ} (hs0 : 0 < s.re) {A D Q : Box}
    (hs : Mem s A) (hd : Mem d D) (hq : Mem q Q) {C : ℕ → Box}
    (hc : ∀ j < 19, Mem (ZetaBlockTaylor.coefficient s j) (C j)) (Ks : List ℕ)
    {v : ℕ} (hv : 0 < v) {Ps : List Packet}
    (he : prepareList cfg A D Q C v Ks = .ok Ps) : SoundList cfg.precision s d q v Ks Ps := by
  induction Ks generalizing v Ps with
  | nil => simp only [prepareList, Except.ok.injEq] at he; subst Ps; trivial
  | cons K Ks ih =>
    cases hP : prepare cfg A D Q C v K with
    | error err => simp [prepareList, hP] at he
    | ok P =>
      cases hPs : prepareList cfg A D Q C (v + K) Ks with
      | error err => simp [prepareList, hP, hPs] at he
      | ok tail =>
        simp only [prepareList, hP, hPs, Except.ok.injEq] at he
        subst Ps
        exact ⟨sound_prepare hp hs0 hs hd hq hc hv hP, ih (by omega) hPs⟩

/-- Evaluate the retained complete list with no center recomputation. -/
def evaluateList (prec : ℤ) (D : ℕ → Box) (j : ℕ) : List Packet → Box
  | [] => rat prec 0
  | P :: Ps => add prec (evaluate prec P D j) (evaluateList prec D j Ps)

theorem mem_evaluateList {prec : ℤ} (hp : prec ≤ 0) {s d q : ℂ} (Ks : List ℕ)
    {v : ℕ} (hv : 0 < v) {Ps : List Packet} (hP : SoundList prec s d q v Ks Ps)
    (j : ℕ) {D : ℕ → Box}
    (hD : ∀ l < 13, Mem (ZetaBlockShift.coefficient (d + j * q) l) (D l)) :
    Mem (ZetaBlockBatch.partition s (d + j * q) v Ks) (evaluateList prec D j Ps) := by
  induction Ks generalizing v Ps with
  | nil =>
    cases Ps with
    | nil => simpa [evaluateList, ZetaBlockBatch.partition] using mem_rat hp 0
    | cons P Ps => exact False.elim hP
  | cons K Ks ih =>
    cases Ps with
    | nil => exact False.elim hP
    | cons P Ps =>
      exact mem_add (mem_evaluate hp hv hP.1 j hD) (ih (by omega) hP.2) prec

end RiemannGaussian.ZetaBlockBatchPacket
