/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAxesLoop

/-! # Exact residue decomposition and original-input loop bounds
All native divisions and powers here are mathematical specifications, not
operations in the fixed physical program.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackAxesArithmetic
open SemiprimeD1StackAxesLoop SemiprimeMacroParameters

/-- Proof-side parity of the retained original exponent. -/
def odd (E:ℕ) : Bool := decide (E%2=1)
/-- Exact parity marker count; no parity answer is supplied to the machine. -/
theorem tail_odd (E:ℕ) : tailBit (odd E)=E%2 := by
  have hr:E%2<2:=Nat.mod_lt _ (by decide)
  by_cases h:E%2=1
  · simp [tailBit,odd,h]
  · have hz:E%2=0:=by omega
    simp [tailBit,odd,hz]
/-- The actual exponent word is partitioned into physical pairs plus its final marker. -/
theorem exponent_parts (E:ℕ) : 2*(E/2)+tailBit (odd E)=E := by
  rw [tail_odd]
  omega
/-- The odd-marker output is the original ceil-half exponent. -/
theorem second_exponent (E:ℕ) : E/2+tailBit (odd E)=E-E/2 := by
  have h:=exponent_parts E
  omega
/-- The paired loop has a fixed polynomial times the largest visited counter. -/
theorem loop_bound (h:ℕ) (odd:Bool) (k:ℕ) :
    loopTime k h odd≤(14*2^(k+h+1)+12)*(h+1) := by
  induction h generalizing k with
  | zero =>
    cases odd <;> simp only [loopTime,Nat.add_zero,Nat.zero_add,Nat.mul_one,pow_succ'] <;> omega
  | succ h ih =>
    have hi:=ih (k+1)
    have he:(k+1)+h+1=k+(h+1)+1:=by omega
    rw [he] at hi
    have hp:(2:ℕ)^k≤2^(k+(h+1)+1):=Nat.pow_le_pow_right (by decide) (by omega)
    simp only [loopTime]
    nlinarith
/-- Closed original exponent-loop bound uses the actual retained R/E resources. -/
theorem original_loop_bound (E:ℕ) :
    loopTime 0 (E/2) (odd E)≤(28*2^E+12)*(E+1) := by
  have h:=loop_bound (E/2) (odd E) 0
  have hp:(2:ℕ)^(0+E/2+1)≤2^(E+1):=Nat.pow_le_pow_right (by decide) (by omega)
  have hd:E/2≤E:=Nat.div_le_self _ _
  have hp2:(2:ℕ)^(E+1)=2*2^E:=pow_succ' _ _
  rw [hp2] at hp
  have hc:14*2^(0+E/2+1)+12≤28*2^E+12:=by omega
  exact h.trans (Nat.mul_le_mul hc (by omega))
/-- Exact complete original-input instruction count. -/
def totalTime (n:ℕ) : ℕ := SemiprimeD1StackTransformArithmetic.totalTime n+
  10*transformExponent n+13+loopTime 0 (transformExponent n/2) (odd (transformExponent n))
/-- Full original-input acquisition has one fixed quadratic transition cap. -/
theorem totalTime_le (n:ℕ) : totalTime n≤400000*(n+1)^2 := by
  have hm:=SemiprimeD1StackTransformArithmetic.totalTime_le n
  have he:=SemiprimeD1StackTransformArithmetic.exponent_bound n
  have hr:=(SemiprimeD1StackTransformArithmetic.prefix_powers n (transformExponent n) (le_refl _)).1
  have hl:=original_loop_bound (transformExponent n)
  unfold totalTime
  nlinarith
end RiemannGaussian.SemiprimeD1StackAxesArithmetic
