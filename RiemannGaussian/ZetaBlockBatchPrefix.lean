/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockBatchPacket

/-!
# Reusable exact early terms on a height lattice

The early Dirichlet terms have no polynomial approximation. Their stored
initial values and phase increments enclose the exact shifted finite sum.
-/

namespace RiemannGaussian.ZetaBlockBatchPrefix
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval ZetaBlockBatchEnclosure

private def rat (prec : ℤ) (a : ℚ) : Box := rational prec a 0

private theorem mem_rat {prec : ℤ} (hp : prec ≤ 0) (a : ℚ) :
    Mem (a : ℂ) (rat prec a) := by
  simpa only [rat, Rat.cast_zero, zero_mul, add_zero] using mem_rational hp a 0

/-- Each stored pair is the exact initial term and its multiplicative increment. -/
def Sound (s q : ℂ) : ℕ → List (Box × Box) → Prop
  | 0, [] => True
  | H + 1, (P, Q) :: Ps =>
      Mem ((H + 1 : ℂ) ^ (-s)) P ∧ Mem ((H + 1 : ℂ) ^ (-q)) Q ∧ Sound s q H Ps
  | _, _ => False

/-- Prepare a complete initial segment, stored in decreasing index order. -/
def prepare (cfg : DyadicConfig) (A Q : Box) : ℕ → EvalResult (List (Box × Box))
  | 0 => .ok []
  | H + 1 =>
      match prepare cfg A Q H with
      | .error err => .error err
      | .ok Ps =>
        match natPower cfg (H + 1) (neg A) with
        | .error err => .error err
        | .ok P =>
          match natPower cfg (H + 1) (neg Q) with
          | .error err => .error err
          | .ok W => .ok ((P, W) :: Ps)

theorem sound_prepare {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s q : ℂ} {A Q : Box} (hs : Mem s A) (hq : Mem q Q) (H : ℕ) {Ps : List (Box × Box)}
    (he : prepare cfg A Q H = .ok Ps) : Sound s q H Ps := by
  induction H generalizing Ps with
  | zero => simp only [prepare, Except.ok.injEq] at he; subst Ps; trivial
  | succ H ih =>
    cases hPs : prepare cfg A Q H with
    | error err => simp only [prepare, hPs, reduceCtorEq] at he
    | ok tail =>
      cases hP : natPower cfg (H + 1) (neg A) with
      | error err => simp only [prepare, hPs, hP, reduceCtorEq] at he
      | ok P =>
        cases hW : natPower cfg (H + 1) (neg Q) with
        | error err => simp only [prepare, hPs, hP, hW, reduceCtorEq] at he
        | ok W =>
          simp only [prepare, hPs, hP, hW, Except.ok.injEq] at he
          subst Ps
          exact ⟨by simpa only [Nat.cast_succ] using
              mem_natPower hp (Nat.succ_pos H) (mem_neg hs) hP,
            by simpa only [Nat.cast_succ] using
              mem_natPower hp (Nat.succ_pos H) (mem_neg hq) hW, ih hPs⟩

/-- Reuse the exact early terms at any sample index, with phase resets. -/
def evaluate (prec : ℤ) (j : ℕ) : List (Box × Box) → Box
  | [] => rat prec 0
  | (P, Q) :: Ps => add prec (evaluate prec j Ps) (phaseAt prec P Q j)

theorem mem_evaluate {prec : ℤ} (hp : prec ≤ 0) {s q : ℂ} (H : ℕ)
    {Ps : List (Box × Box)} (hP : Sound s q H Ps) (j : ℕ) :
    Mem (ZetaEulerCell.partialSum H (s + j * q)) (evaluate prec j Ps) := by
  induction H generalizing Ps with
  | zero =>
    cases Ps with
    | nil => simpa [evaluate, ZetaEulerCell.partialSum] using mem_rat hp 0
    | cons P Ps => exact False.elim hP
  | succ H ih =>
    cases Ps with
    | nil => exact False.elim hP
    | cons P Ps =>
      have hphase := mem_phaseAt hp hP.1 hP.2.1 j
      have he := ZetaBlockBatchPacket.power_lattice (H + 1) (Nat.succ_pos H) s q j
      simp only [Nat.cast_add, Nat.cast_one] at he
      rw [he] at hphase
      have hh := mem_add (ih hP.2.2) hphase prec
      simpa only [ZetaEulerCell.partialSum, Finset.sum_range_succ, evaluate] using hh

end RiemannGaussian.ZetaBlockBatchPrefix
