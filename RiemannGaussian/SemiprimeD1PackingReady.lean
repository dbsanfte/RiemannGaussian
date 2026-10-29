/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1LeafReady

/-! # Uniform original-input packing guards for every permitted D.1 depth
Literal integer floors and ceilings are retained. No packing acceptance or
asymptotic comparison is supplied as a premise.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1PackingReady
open Filter SemiprimeD1Schedule
open scoped Topology

/-- Actual original binary ceiling logarithm. -/
def logarithm (s : ℕ) : ℕ := Nat.clog 2 (s+2)

/-- One fixed degree cap shared by every recursive call. -/
def degreeCap (s : ℕ) : ℕ := 2^((9*logarithm s+9)/10)

/-- Maximum actual packet exponent, before choosing any recursive depth. -/
def maximumExponent (s : ℕ) : ℕ := 4*(logarithm s/131072)

/-- An elementary exponential bound, proved from a literal starting index. -/
theorem linear_le_pow (m : ℕ) (hm : 16 ≤ m) : 100*(m+1) ≤ 2^m := by
  induction m,hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    have hp : 100 ≤ 100*(m+1) := by omega
    nlinarith

/-- A twentieth of the literal logarithm pays the full integer square-root factor. -/
theorem logarithm_factor (lam : ℕ) (hlam : 1000 ≤ lam) :
    Nat.sqrt lam+1 ≤ 2^(lam/20) := by
  have hm : 16 ≤ lam/20 := by omega
  have h := linear_le_pow (lam/20) hm
  have hs := Nat.sqrt_le_self lam
  have hd := Nat.mod_lt lam (by decide : 0 < 20)
  have he := Nat.mod_add_div lam 20
  omega

/-- All literal exponents fit below the original root-size exponent. -/
theorem exponent_margin (lam : ℕ) (hlam : 1000 ≤ lam) :
    1+24*(4*(lam/131072))+(9*lam+9)/10+lam/20 ≤ lam-2 ∧
    4*(lam/131072)+1 ≤ (9*lam+9)/10 := by
  omega

/-- Actual ceiling-logarithm inversion, with the additive input offset paid. -/
theorem root_power (s : ℕ) (hs : 2 ≤ s) (hl : 2 ≤ logarithm s) :
    2^(logarithm s-2) ≤ s := by
  have hp := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (show 1 < s+2 by omega)
  have he : logarithm s-1=(logarithm s-2)+1 := by omega
  change 2^(logarithm s-1) < s+2 at hp
  rw [he,pow_succ] at hp
  omega

/-- Concrete original-input guards, before selecting a recursion depth. -/
theorem packing_numeric (s : ℕ) (hs : 2 ≤ s) (hlam : 1000 ≤ logarithm s) :
    2*(64^(2*maximumExponent s))^2*degreeCap s ≤ leafSize s (logarithm s) ∧
    64^(2*maximumExponent s)*2^maximumExponent s ≤ leafSize s (logarithm s) ∧
    2*2^maximumExponent s ≤ degreeCap s := by
  let lam := logarithm s
  let a := maximumExponent s
  let c := (9*lam+9)/10
  have hm := exponent_margin lam hlam
  have hf := logarithm_factor lam hlam
  have hp := root_power s hs (by omega)
  have hfirst : (2*(64^(2*a))^2*2^c)*(Nat.sqrt lam+1) ≤ s := by
    calc
      _ ≤ (2*(64^(2*a))^2*2^c)*2^(lam/20) := Nat.mul_le_mul_left _ hf
      _ = 2^(1+24*a+c+lam/20) := by
        have hh : (64^(2*a))^2=(2:ℕ)^(24*a) := by
          rw [show (64:ℕ)=2^6 by norm_num,← pow_mul,← pow_mul]
          congr 1
          ring
        rw [hh]
        change (2^1*2^(24*a)*2^c)*2^(lam/20)=_
        simp only [← pow_add]
      _ ≤ 2^(lam-2) := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hm.1
      _ ≤ s := hp
  have hsmall : 64^(2*a)*2^a ≤ 2*(64^(2*a))^2*2^c := by
    have ha : a ≤ c := by dsimp [a,maximumExponent,c,lam] at *;omega
    have hpow := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ha
    have hbase : 1 ≤ 64^(2*a) := Nat.one_le_pow _ _ (by decide)
    have hfactor : 64^(2*a) ≤ 2*(64^(2*a))^2 := by nlinarith
    exact Nat.mul_le_mul hfactor hpow
  have hleaf : 2*(64^(2*a))^2*2^c ≤ leafSize s lam := by
    have hd := (Nat.le_div_iff_mul_le (show 0 < Nat.sqrt lam+1 by omega)).mpr hfirst
    exact hd.trans (Nat.le_succ _)
  refine ⟨hleaf,hsmall.trans hleaf,?_⟩
  change 2*2^a ≤ 2^c
  rw [← pow_succ']
  exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hm.2

/-- Uniform original-input acceptance, proved eventually rather than assumed. -/
theorem eventually_packing : ∀ᶠ s : ℕ in atTop,
    2*(64^(2*maximumExponent s))^2*degreeCap s ≤ leafSize s (logarithm s) ∧
    64^(2*maximumExponent s)*2^maximumExponent s ≤ leafSize s (logarithm s) ∧
    2*2^maximumExponent s ≤ degreeCap s := by
  have ht : Tendsto logarithm atTop atTop :=
    SemiprimeCounterRate.tendsto_clog_two_atTop.comp (tendsto_add_atTop_nat 2)
  filter_upwards [eventually_ge_atTop (2:ℕ),ht.eventually (eventually_ge_atTop (1000:ℕ))] with s hs hl
  exact packing_numeric s hs hl

/-- Every actual recursive exponent obeys the same original-input cap. -/
theorem actual_exponent_le (s depth : ℕ) :
    exponent (logarithm s) depth ≤ maximumExponent s := by
  simpa only [maximumExponent,epsilonDenominator] using exponent_le (logarithm s) depth

/-- Original-input packing guards hold uniformly at EVERY active depth and
for EVERY inherited degree below the one global cap. -/
theorem eventually_all_depths : ∀ᶠ s : ℕ in atTop,∀depth M degree : ℕ,
    Active s (logarithm s) depth M → degree ≤ degreeCap s →
    2*(64^(2*exponent (logarithm s) depth))^2*degree < M ∧
    64^(2*exponent (logarithm s) depth)*2^exponent (logarithm s) depth < M ∧
    max degree (2*2^exponent (logarithm s) depth) ≤ degreeCap s := by
  filter_upwards [eventually_packing] with s hs
  intro depth M degree hactive hdegree
  have ha := actual_exponent_le s depth
  have hleaf : leafSize s (logarithm s) < M := hactive.1
  have hpow : 64^(2*exponent (logarithm s) depth) ≤ 64^(2*maximumExponent s) :=
    Nat.pow_le_pow_right (by decide : 0<(64:ℕ)) (Nat.mul_le_mul_left _ ha)
  have htwo : 2^exponent (logarithm s) depth ≤ 2^maximumExponent s :=
    Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) ha
  refine ⟨lt_of_le_of_lt ((Nat.mul_le_mul
    (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hpow 2)) hdegree).trans hs.1) hleaf,
    lt_of_le_of_lt ((Nat.mul_le_mul hpow htwo).trans hs.2.1) hleaf,?_⟩
  exact max_le hdegree ((Nat.mul_le_mul_left 2 htwo).trans hs.2.2)

end RiemannGaussian.SemiprimeD1PackingReady
