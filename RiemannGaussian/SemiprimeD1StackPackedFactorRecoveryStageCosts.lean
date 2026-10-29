/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryDiscriminant
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryHalves
import RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryValidation
/-! # Actual recovery-stage clock caps from physical binary word lengths -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryStageCosts
open SemiprimeD1StackPackedFactorRecoveryEncoding SemiprimeD1StackPackedFactorRecoveryPrimitives
open SemiprimeBitArithmetic SemiprimeBitDivision
/-- Exact actual adder trace is linear in the physically present operand bytes. -/
theorem add_le (L : ℕ) (xs ys : List Bool) (hx : xs.length≤L) (hy : ys.length≤L) :
    addTime xs ys≤20*(L+1) := by
  have hm : max xs.length ys.length≤L := max_le hx hy
  have ho:=(addBits_counts xs ys false).2.2.2.2
  unfold addTime
  omega
/-- Actual ripple subtraction pays its output borrow bit as well as all difference bytes. -/
theorem subtract_le (L : ℕ) (xs ys : List Bool) (hx : xs.length≤L) (hy : ys.length≤L) :
    subtractTime xs ys≤20*(L+1) := by
  have hm : max xs.length ys.length≤L := max_le hx hy
  have ho:=(subBits_counts xs ys false).2.2.2.2
  unfold subtractTime
  omega
/-- This uses the frozen multiplier's ACTUAL source time cap, never a native report. -/
theorem multiply_le (L : ℕ) (xs ys : List Bool) (hx : xs.length≤L) (hy : ys.length≤L) :
    multiplyTime xs ys≤1000*(L+1)^3 := by
  have ht:=SemiprimeD1StackMultiplierExecution.source_time xs ys
  have hp : SemiprimeD1StackMultiplierExecution.timeBound xs.length ys.length+1≤
      2*L+2+100*(L+1)*(L*(L+2)+L+3) := by
    unfold SemiprimeD1StackMultiplierExecution.timeBound
    calc
      _ = 2*xs.length+2+100*(xs.length+1)*(xs.length*(ys.length+2)+ys.length+3) := by ring
      _ ≤ _ := by gcongr
  have hc : 2*L+2+100*(L+1)*(L*(L+2)+L+3)≤1000*(L+1)^3 := by
    ring_nf
    omega
  unfold multiplyTime
  exact (Nat.add_le_add_right ht 1).trans (hp.trans hc)
/-- Real numeric comparison includes subtraction, all difference drains and its caller return. -/
theorem compare_le (L : ℕ) (xs ys : List Bool) (hx : xs.length≤L) (hy : ys.length≤L) :
    compareTime xs ys≤30*(L+1) := by
  have ht:=SemiprimeD1StackWordLessExecution.totalTime_le xs ys
  unfold compareTime
  omega
/-- Summed actual discriminant calls and cleanup have one fixed cubic physical-word cap. -/
theorem discriminant_le (L : ℕ) (n s : List Bool) (hn : n.length≤L) (hs : s.length≤L)
    (hsq : (squareWord s).length≤L) (hf : (fourWord n).length≤L) (hd : (discriminant n s).length≤L) :
    SemiprimeD1StackPackedFactorRecoveryDiscriminant.time n s≤3000*(L+1)^3 := by
  have hm:=multiply_le L s s hs hs
  have ht:=subtract_le L (squareWord s) (fourWord n) hsq hf
  have hl : L+1≤(L+1)^3 := Nat.le_self_pow (by decide : 3≠0) _
  unfold SemiprimeD1StackPackedFactorRecoveryDiscriminant.time
  nlinarith
/-- Lower-half cost is linear in actual words, with every borrow/parity/output pop counted. -/
theorem minus_le (L : ℕ) (s root lo : List Bool) (hs : s.length≤L) (hr : root.length≤L) (hl : lo.length≤L) :
    SemiprimeD1StackPackedFactorRecoveryHalves.minusTime s root lo≤100*(L+1) := by
  have ht:=subtract_le L s root hs hr
  unfold SemiprimeD1StackPackedFactorRecoveryHalves.minusTime
  omega
/-- Upper-half cost includes actual addition, low-bit pop, preserving copy and output drain. -/
theorem plus_le (L : ℕ) (s root hi : List Bool) (hs : s.length≤L) (hr : root.length≤L) (hh : hi.length≤L) :
    SemiprimeD1StackPackedFactorRecoveryHalves.plusTime s root hi≤100*(L+1) := by
  have ht:=add_le L s root hs hr
  unfold SemiprimeD1StackPackedFactorRecoveryHalves.plusTime
  omega
/-- Each actual comparison to literal binary2 has a linear operand-byte cap. -/
theorem factor_le (L : ℕ) (factor : List Bool) (hf : factor.length≤L) (hL : 2≤L) :
    SemiprimeD1StackPackedFactorRecoveryFactorChecks.time factor≤40*(L+1) := by
  have hc:=compare_le L factor [false,true] hf hL
  unfold SemiprimeD1StackPackedFactorRecoveryFactorChecks.time
  omega
/-- Actual multiplication of the two physical factors, including both paid copies. -/
theorem product_le (L : ℕ) (small large : List Bool) (hs : small.length≤L) (hl : large.length≤L) :
    SemiprimeD1StackPackedFactorRecoveryValidation.productTime small large≤1100*(L+1)^3 := by
  have hm:=multiply_le L small large hs hl
  have h : L+1≤(L+1)^3 := Nat.le_self_pow (by decide : 3≠0) _
  unfold SemiprimeD1StackPackedFactorRecoveryValidation.productTime
  nlinarith
/-- Both real equality directions and their physical flags are linear in actual operand bytes. -/
theorem equality_le (L : ℕ) (n product : List Bool) (hn : n.length≤L) (hp : product.length≤L) :
    SemiprimeD1StackPackedFactorRecoveryValidation.equalityTime n product≤100*(L+1) := by
  have h0:=compare_le L product n hp hn
  have h1:=compare_le L n product hn hp
  unfold SemiprimeD1StackPackedFactorRecoveryValidation.equalityTime
  omega
/-- Complete common physical validation has a fixed cubic cap in its actual operand-word widths. -/
theorem validation_le (L : ℕ) (n small large : List Bool) (hL : 2≤L)
    (hn : n.length≤L) (hs : small.length≤L) (hl : large.length≤L)
    (hp : (SemiprimeD1StackPackedFactorRecoveryValidation.productWord small large).length≤L) :
    SemiprimeD1StackPackedFactorRecoveryValidation.time n small large≤3000*(L+1)^3 := by
  have h0:=factor_le L small hs hL
  have h1:=factor_le L large hl hL
  have h2:=product_le L small large hs hl
  have h3:=equality_le L n (SemiprimeD1StackPackedFactorRecoveryValidation.productWord small large) hn hp
  have h4 : L+1≤(L+1)^3 := Nat.le_self_pow (by decide : 3≠0) _
  unfold SemiprimeD1StackPackedFactorRecoveryValidation.time
  nlinarith
end RiemannGaussian.SemiprimeD1StackPackedFactorRecoveryStageCosts
