/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeMacroParameters

/-! # Original-derived transform stopping and resource arithmetic
Only proof-side target notation uses powers/logarithms. The physical program
constructs those counters by marker writes. These facts derive its least stop
and fixed-polynomial scalar envelope from the original acquired width.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackTransformArithmetic
open SemiprimeMacroParameters

/-- Counter quadrupling agrees with the square of counter doubling. -/
theorem square_pow (k:ℕ) : (4:ℕ)^k=((2:ℕ)^k)^2 := by
  rw [show (4:ℕ)=(2:ℕ)^2 by decide,←pow_mul,←pow_mul,Nat.mul_comm]

/-- Every earlier literal counter state fails the stopping test. -/
theorem before_stop (ell k:ℕ) (hk:k<transformExponent ell) : (4:ℕ)^k<16*ell := by
  by_contra h
  have hs:16*ell≤((2:ℕ)^k)^2:=by rw [←square_pow];omega
  have he:=transform_minimal hs
  omega

/-- The original least exponent really meets the physical stopping test. -/
theorem at_stop (ell:ℕ) : 16*ell≤(4:ℕ)^transformExponent ell := by
  rw [square_pow]
  exact transform_square_lower ell

/-- The zero-width transform has no doubling rounds. -/
theorem exponent_zero : transformExponent 0=0 := by norm_num [transformExponent]

/-- Every natural exponent is bounded by its dyadic value. -/
theorem count_le_power (k:ℕ) : k≤(2:ℕ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    have hp:0<(2:ℕ)^k:=pow_pos (by decide) _
    omega

/-- Final square magnitude is linear in the original width, including zero. -/
theorem square_bound (ell:ℕ) : (4:ℕ)^transformExponent ell≤64*ell+1 := by
  by_cases h:ell=0
  · subst ell;rw [exponent_zero];norm_num
  · have hp:0<ell:=Nat.pos_of_ne_zero h
    have hs:=transform_square_upper hp
    change ((2:ℕ)^transformExponent ell)^2<64*ell at hs
    rw [←square_pow] at hs
    omega

/-- All actually visited radius/square states satisfy an original-width magnitude cap. -/
theorem prefix_powers (ell k:ℕ) (hk:k≤transformExponent ell) :
    (2:ℕ)^k≤64*ell+1 ∧ (4:ℕ)^k≤64*ell+1 := by
  have hs:(4:ℕ)^k≤(4:ℕ)^transformExponent ell:=Nat.pow_le_pow_right (by decide) hk
  have hs':(4:ℕ)^k≤64*ell+1:=hs.trans (square_bound ell)
  exact ⟨(Nat.pow_le_pow_left (by decide:(2:ℕ)≤4) k).trans hs',hs'⟩

/-- The number of actual growth rounds is bounded by original width. -/
theorem exponent_bound (ell:ℕ) : transformExponent ell≤64*ell+1 :=
  (count_le_power _).trans (prefix_powers ell _ (le_refl _)).1

/-- The actual radix is also small; no quotient-height premise is supplied. -/
theorem radix_bound (ell:ℕ) : radixBits ell≤64*ell+1 :=
  (Nat.div_le_self _ _).trans (prefix_powers ell _ (le_refl _)).1

/-- Exact failed comparison plus physical doubling/quadrupling cost. -/
def failCost (ell k:ℕ) : ℕ :=
  (6*((4:ℕ)^k+16*ell)+10)+(7*(2:ℕ)^k+13*(4:ℕ)^k+5)

/-- Exact executed round-count recurrence; it is not a runtime fuel input. -/
def loopTime (ell k:ℕ) : ℕ→ℕ
  | 0 => 6*((4:ℕ)^k+16*ell)+10
  | n+1 => failCost ell k+loopTime ell (k+1) n

/-- Every original-derived failure round has a linear numeric transition bound. -/
theorem failCost_le (ell k:ℕ) (hk:k≤transformExponent ell) : failCost ell k≤1760*ell+41 := by
  have hp:=prefix_powers ell k hk
  unfold failCost
  omega

/-- All rounds use their actual floor-free counter path and derived original stop. -/
theorem loopTime_le (ell k n:ℕ) (h:k+n=transformExponent ell) :
    loopTime ell k n≤n*(1760*ell+41)+(480*ell+16) := by
  induction n generalizing k with
  | zero =>
    have hk:k≤transformExponent ell:=by omega
    have hp:=(prefix_powers ell k hk).2
    simp only [loopTime,Nat.zero_mul,Nat.zero_add]
    omega
  | succ n ih =>
    have hk:k≤transformExponent ell:=by omega
    have ht:(k+1)+n=transformExponent ell:=by omega
    have hf:=failCost_le ell k hk
    have hi:=ih (k+1) ht
    calc
      loopTime ell k (n+1)=failCost ell k+loopTime ell (k+1) n := rfl
      _ ≤ (1760*ell+41)+(n*(1760*ell+41)+(480*ell+16)) := Nat.add_le_add hf hi
      _ = (n+1)*(1760*ell+41)+(480*ell+16) := by ring

/-- Original root loop has no supplied iteration or work estimate. -/
theorem root_loopTime_le (ell:ℕ) :
    loopTime ell 0 (transformExponent ell)≤(64*ell+1)*(1760*ell+41)+(480*ell+16) := by
  have h:=loopTime_le ell 0 (transformExponent ell) (by omega)
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (exponent_bound ell)) _)

/-- Actual final physical radix-copy/extraction cost. -/
def radixTime (ell:ℕ) : ℕ := if ell=0 then 11 else 25*radixBits ell+5

/-- Radix extraction cost is derived from the actual original parameter. -/
theorem radixTime_le (ell:ℕ) : radixTime ell≤25*(64*ell+1)+11 := by
  unfold radixTime
  split
  · omega
  · have h:=radix_bound ell;omega

/-- Exact source-level whole metadata acquisition time. -/
def totalTime (ell:ℕ) : ℕ :=
  (85*ell+71)+(loopTime ell 0 (transformExponent ell)+radixTime ell)+1

/-- Actual full acquisition admits one fixed polynomial for every original width. -/
theorem totalTime_le (ell:ℕ) : totalTime ell≤120000*(ell+1)^2 := by
  have hl:=root_loopTime_le ell
  have hr:=radixTime_le ell
  have hn:(85*ell+71)+((64*ell+1)*(1760*ell+41)+(480*ell+16)+(25*(64*ell+1)+11))+1 ≤
      120000*(ell+1)^2:=by nlinarith
  unfold totalTime
  omega
end RiemannGaussian.SemiprimeD1StackTransformArithmetic
