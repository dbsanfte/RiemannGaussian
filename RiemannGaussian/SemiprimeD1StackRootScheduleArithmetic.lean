/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1Schedule
import RiemannGaussian.SemiprimeD1PublicPackingReady
import Mathlib.Data.Nat.Size
/-! # Exact arithmetic specifications for physical root-schedule acquisition
These equations identify the actual stack counters; they introduce no runtime
logarithm, square-root, quotient or acquired-parameter supplier.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
namespace RiemannGaussian.SemiprimeD1StackRootScheduleArithmetic
/-- The literal root logarithm acquired by the two finite width branches. -/
def lambda (ell : Nat) : Nat := if ell=0 then 1 else 20+ell.size
/-- Repeated physical division by two counts the binary size exactly. -/
theorem size_step (n : Nat) (hn : 0<n) : n.size=(n/2).size+1 := by
  apply eq_of_forall_ge_iff
  intro k
  cases k with
  | zero => have hp:=Nat.size_pos.mpr hn;omega
  | succ k =>
    rw [Nat.add_le_add_iff_right,Nat.size_le,Nat.size_le,pow_succ]
    exact (Nat.div_lt_iff_lt_mul (by decide : 0<2)).symm
/-- Every counted logarithmic metadata word is at most its physical input width. -/
theorem size_le_self (n : Nat) : n.size≤n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn:n=0
    · subst n;rfl
    · have hp:0<n:=by omega
      have hq:n/2<n:=Nat.div_lt_self hp (by decide)
      rw [size_step n hp]
      have h:=ih (n/2) hq
      omega
/-- Exact ceiling log of a successor, including zero. -/
theorem clog_succ (n : Nat) : Nat.clog 2 (n+1)=n.size := by
  apply eq_of_forall_ge_iff
  intro k
  rw [Nat.clog_le_iff_le_pow (by decide),Nat.size_le]
  omega
/-- The scaled original root logarithm is exactly the physically counted size
plus twenty; the width-zero branch is also exact. -/
theorem lambda_original (ell : Nat) :
    lambda ell=Nat.clog 2 (SemiprimeD1PublicPackingReady.scale ell+2) := by
  by_cases hz:ell=0
  · subst ell;decide
  · have hp:0<ell:=by omega
    have hs:0<ell.size:=Nat.size_pos.mpr hp
    have hupper:ell+1≤2^ell.size:=by have h:=Nat.lt_size_self ell;omega
    have hlower:2^(ell.size-1)≤ell:=Nat.lt_size.mp (by omega)
    have hu:2^20*ell+2≤2^(20+ell.size):=by
      rw [pow_add]
      have h:=Nat.mul_le_mul_left (2^20) hupper
      norm_num at h ⊢
      omega
    have hl:2^(20+ell.size-1)<2^20*ell+2:=by
      rw [show 20+ell.size-1=20+(ell.size-1) by omega,pow_add]
      have h:=Nat.mul_le_mul_left (2^20) hlower
      omega
    have h0:Nat.clog 2 (2^20*ell+2)≤20+ell.size:=Nat.clog_le_of_le_pow hu
    have h1:20+ell.size-1<Nat.clog 2 (2^20*ell+2):=(Nat.lt_clog_iff_pow_lt (by decide)).mpr hl
    unfold lambda SemiprimeD1PublicPackingReady.scale
    simp only [hz,ite_false]
    omega
/-- All acquired root logarithms have a fixed original-width linear bound. -/
theorem lambda_le (ell : Nat) : lambda ell≤ell+20 := by
  unfold lambda
  split
  · omega
  · have h:=size_le_self ell;omega
/-- The root's conservative lower guard is four more real size scans plus eight. -/
theorem minimum_original (ell : Nat) :
    4*(lambda ell).size+8=SemiprimeD1PrecisionEnvelope.minimumLevels (lambda ell) := by
  unfold SemiprimeD1PrecisionEnvelope.minimumLevels
  rw [clog_succ]
/-- Seventeen actual halving calls give the exact original root valuation block. -/
theorem levels_original (ell : Nat) :
    lambda ell/2^17=SemiprimeD1Schedule.levels (lambda ell) 0 := by
  simp only [SemiprimeD1Schedule.levels,pow_zero,Nat.div_one]
  rfl
/-- At the root, two physically copied level blocks are exactly the packet exponent. -/
theorem exponent_original (ell : Nat) :
    2*(lambda ell/2^17)=SemiprimeD1Schedule.exponent (lambda ell) 0 := by
  rw [levels_original]
  simp [SemiprimeD1Schedule.exponent,SemiprimeD1Schedule.previous]
end RiemannGaussian.SemiprimeD1StackRootScheduleArithmetic
