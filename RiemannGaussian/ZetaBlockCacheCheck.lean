/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaBlockBatchCertificate

/-!
# Checking supplied cache entries independently

Candidate numerical data is untrusted. Each stored early term is checked
against the sound evaluator, without rebuilding the recursive preparation
of the entire prefix whenever a cache projection is needed.
-/

namespace RiemannGaussian.ZetaBlockCacheCheck
open LeanCert.Core LeanCert.Engine CertifiedComplexInterval

/-- Check that the first computed rectangle is contained in the second one. -/
def contained (A B : Box) : Bool := decide
  (B.re.lo.toRat ≤ A.re.lo.toRat ∧ A.re.hi.toRat ≤ B.re.hi.toRat ∧
    B.im.lo.toRat ≤ A.im.lo.toRat ∧ A.im.hi.toRat ≤ B.im.hi.toRat)

theorem mem_of_contained {z : ℂ} {A B : Box} (hz : Mem z A)
    (hc : contained A B = true) : Mem z B := by
  obtain ⟨hlr, hur, hli, hui⟩ := of_decide_eq_true hc
  exact ⟨⟨((Rat.cast_le (K := ℝ)).mpr hlr).trans hz.1.1,
      hz.1.2.trans ((Rat.cast_le (K := ℝ)).mpr hur)⟩,
    ⟨((Rat.cast_le (K := ℝ)).mpr hli).trans hz.2.1,
      hz.2.2.trans ((Rat.cast_le (K := ℝ)).mpr hui)⟩⟩

/-- Independently verify one stored complex power. -/
def powerCheck (cfg : DyadicConfig) (n : ℕ) (A B : Box) : Bool :=
  match natPower cfg n A with
  | .error _ => false
  | .ok C => contained C B

theorem mem_power_of_check {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {n : ℕ} (hn : 0 < n) {z : ℂ} {A B : Box} (hz : Mem z A)
    (hc : powerCheck cfg n A B = true) : Mem ((n : ℂ) ^ z) B := by
  cases he : natPower cfg n A with
  | error err => simp only [powerCheck, he, Bool.false_eq_true] at hc
  | ok C =>
    simp only [powerCheck, he] at hc
    exact mem_of_contained (mem_natPower hp hn hz he) hc

/-- Verify literal early-term cache data, in the same decreasing order as preparation. -/
def prefixCheck (cfg : DyadicConfig) (A Q : Box) : ℕ → List (Box × Box) → Bool
  | 0, [] => true
  | H + 1, (P, W) :: Ps =>
      powerCheck cfg (H + 1) (neg A) P && powerCheck cfg (H + 1) (neg Q) W &&
        prefixCheck cfg A Q H Ps
  | _, _ => false

/-- Assemble separately checked entries without replaying every numerical
calculation inside one large kernel reduction. The literal checker and
its full-length requirement are unchanged. -/
theorem prefixCheck_cons {cfg : DyadicConfig} {A Q : Box} {H : ℕ}
    {P : Box × Box} {Ps : List (Box × Box)}
    (hc : (powerCheck cfg (H + 1) (neg A) P.1 &&
      powerCheck cfg (H + 1) (neg Q) P.2) = true)
    (ht : prefixCheck cfg A Q H Ps = true) :
    prefixCheck cfg A Q (H + 1) (P :: Ps) = true := by
  rcases P with ⟨P, W⟩
  simp only [prefixCheck, hc, ht, Bool.true_and]

/-- Supplied data gives the same prefix soundness as successful preparation. -/
theorem sound_prefix_of_check {cfg : DyadicConfig} (hp : cfg.precision ≤ 0)
    {s q : ℂ} {A Q : Box} (hs : Mem s A) (hq : Mem q Q) (H : ℕ)
    {Ps : List (Box × Box)} (hc : prefixCheck cfg A Q H Ps = true) :
    ZetaBlockBatchPrefix.Sound s q H Ps := by
  induction H generalizing Ps with
  | zero =>
    cases Ps with
    | nil => trivial
    | cons P Ps => simp only [prefixCheck, Bool.false_eq_true] at hc
  | succ H ih =>
    cases Ps with
    | nil => simp only [prefixCheck, Bool.false_eq_true] at hc
    | cons P Ps =>
      obtain ⟨hleft, hrest⟩ := Bool.and_eq_true_iff.mp hc
      obtain ⟨hP, hQ⟩ := Bool.and_eq_true_iff.mp hleft
      exact ⟨by simpa only [Nat.cast_succ] using
          mem_power_of_check hp (Nat.succ_pos H) (mem_neg hs) hP,
        by simpa only [Nat.cast_succ] using
          mem_power_of_check hp (Nat.succ_pos H) (mem_neg hq) hQ, ih hrest⟩

end RiemannGaussian.ZetaBlockCacheCheck
