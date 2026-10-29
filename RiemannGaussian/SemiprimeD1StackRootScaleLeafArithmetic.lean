/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootScheduleArithmetic
import Mathlib.Data.Nat.Sqrt
/-! # Exact odd-subtraction invariant and original leaf threshold specifications -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackRootScaleLeafArithmetic
/-- The next physical odd block after k actual successful subtraction rounds. -/
def odd (k : Nat) : Nat :=2*k+1
/-- The fixed scale materialized by exactly twenty actual doublings. -/
def scale (ell : Nat) : Nat :=2^20*ell
/-- Exact acquired integer square root of the original acquired lambda. -/
def root (ell : Nat) : Nat :=Nat.sqrt (SemiprimeD1StackRootScheduleArithmetic.lambda ell)
/-- Exact original root leaf threshold; never a runtime answer supplier. -/
def leaf (ell : Nat) : Nat :=scale ell/(root ell+1)+1
/-- One successful odd subtraction preserves the complete original square invariant. -/
theorem subtract_invariant (n k : Nat) (h : odd k≤ n) :
    (n-odd k)+(k+1)^2=n+k^2 :=by
  have hn: n-odd k+odd k=n:=Nat.sub_add_cancel h
  unfold odd at *
  nlinarith
/-- An actual failed odd subtraction locates the UNIQUE exact integer square root. -/
theorem stop_exact (n k : Nat) (h : n<odd k) : Nat.sqrt (n+k^2)=k :=by
  have hlo:k≤ Nat.sqrt (n+k^2):=Nat.le_sqrt'.mpr (by omega)
  have hhi:Nat.sqrt (n+k^2)<k+1:=Nat.sqrt_lt'.mpr (by unfold odd at h;nlinarith)
  omega
/-- The remaining physical input strictly decreases at every successful iteration. -/
theorem subtract_lt (n k : Nat) (h : odd k≤ n) : n-odd k<n :=by unfold odd at h ⊢;omega
/-- A physical potential used ONLY to account for executed loop transitions. -/
theorem potential_decreases (n k : Nat) (h : odd k≤ n) :
    2*(n-odd k)+(k+1)+1<2*n+k+1 :=by
  have hn:n-odd k+odd k=n:=Nat.sub_add_cancel h
  unfold odd at *
  omega
/-- Exact integer threshold equals the same old literal Schedule.leafSize. -/
theorem leaf_original (ell : Nat) :
    leaf ell=SemiprimeD1Schedule.leafSize (SemiprimeD1PublicPackingReady.scale ell)
      (SemiprimeD1StackRootScheduleArithmetic.lambda ell) :=rfl
/-- Materialized metadata scale has the same original literal constant. -/
theorem scale_original (ell : Nat) : scale ell=SemiprimeD1PublicPackingReady.scale ell :=rfl
end RiemannGaussian.SemiprimeD1StackRootScaleLeafArithmetic
