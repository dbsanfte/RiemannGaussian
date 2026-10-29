/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PacketTableClock

/-! # Explicit polynomial prefactors for actual eager child tables
All report suppliers remain literal arguments of the fixed arithmetic
prefactors. The original constructor bounds discharge those arguments; no
exponential requested-coefficient factor is called polynomial.
-/
set_option autoImplicit false
set_option maxHeartbeats 100000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1ChildClockFactor
open SemiprimeD1JetAxes SemiprimeD1ChildTableClock SemiprimeD1PacketTableClock SemiprimeD1PacketEntryClock

/-- Fixed arithmetic coefficient in the full old-cache physical table copy. -/
def cacheCoefficient (old : Context) (extra : List ℕ) (p D : ℕ) : ℕ :=
  D*(4*D+7)+1+old.rank*(3*old.precision+4)+1+4*D+
    SemiprimeD1ChildTableCopy.liftBudget old extra p+12

/-- Every actual old-table routing/report repetition remains in this prefactor. -/
def leftPolynomial (old : Context) (extra : List ℕ) (p D O v : ℕ) : ℕ :=
  (2*O+D+(9*p+(extra++old.axes).prod+13)+5+D+v+12)+
    (lookupBudget old D+7+cacheCoefficient old extra p D+lookupBudget ⟨extra++old.axes,p⟩ D+7)

/-- Whole actual old-child table clock has the literal eager 2^D scale. -/
theorem leftBudget_factor (old : Context) (extra : List ℕ) (p D O v : ℕ) :
    leftBudget old extra p D O v ≤ leftPolynomial old extra p D O v*2^D := by
  have hq : 1 ≤ (2:ℕ)^D := Nat.one_le_pow _ _ (by decide)
  calc
    _ = (2*O+D+(9*p+(extra++old.axes).prod+13)+5+D+v+12)+
        (lookupBudget old D+7+cacheCoefficient old extra p D+lookupBudget ⟨extra++old.axes,p⟩ D+7)*2^D := by
      unfold leftBudget cacheBudget cacheCoefficient
      ring
    _ ≤ _ := add_mul_le _ _ _ hq

/-- New-table controls and producer reports, outside eager assignment acquisition. -/
def rightControls (H Z G A L e : ℕ) : ℕ := H+Z+L+12+G+A+e+10

/-- Explicit physical packet-table polynomial prefactor; all source/header/fresh
reports are retained at their actual per-table multiplicity. -/
def rightPolynomial (ctx : Context) (a A K P T B L E H Z G e : ℕ) : ℕ :=
  rightControls H Z G A L e+
    (entryPolynomial ctx a A K P T B L E+lookupBudget ctx A+14)

/-- Actual packet table scale includes BOTH all assignments and the literal
coefficient recursion. The original CatalogSize theorem absorbs their product. -/
theorem rightClock_factor (ctx : Context) (a A K P T B L E H Z G e : ℕ) :
    rightClock ctx a A K P T B L E H Z G e ≤
      rightPolynomial ctx a A K P T B L E H Z G e*(2^A*(K+1)^A) := by
  have hv : 1 ≤ (K+1)^A := Nat.one_le_pow _ _ (by omega)
  have he := entryClock_factor ctx a A K P T B L E
  have hcoef : entryClock ctx a A K P T B L E+7+lookupBudget ctx A+7 ≤
      (entryPolynomial ctx a A K P T B L E+lookupBudget ctx A+14)*(K+1)^A := by
    calc
      _ ≤ entryPolynomial ctx a A K P T B L E*(K+1)^A+7+lookupBudget ctx A+7 :=
        Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right he 7) _) 7
      _ = (lookupBudget ctx A+14)+entryPolynomial ctx a A K P T B L E*(K+1)^A := by ring
      _ ≤ _ := by
        have h := add_mul_le (lookupBudget ctx A+14) (entryPolynomial ctx a A K P T B L E) _ hv
        simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h
  have hq : 1 ≤ 2^A*(K+1)^A := by
    exact one_le_mul_of_one_le_of_one_le (Nat.one_le_pow _ _ (by decide)) hv
  calc
    _ = rightControls H Z G A L e+
        (entryClock ctx a A K P T B L E+7+lookupBudget ctx A+7)*2^A := by
      unfold rightClock tableClock rightControls
      ring
    _ ≤ rightControls H Z G A L e+
        ((entryPolynomial ctx a A K P T B L E+lookupBudget ctx A+14)*(K+1)^A)*2^A :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ hcoef) _
    _ = rightControls H Z G A L e+
        (entryPolynomial ctx a A K P T B L E+lookupBudget ctx A+14)*(2^A*(K+1)^A) := by ring
    _ ≤ _ := add_mul_le _ _ _ hq

end RiemannGaussian.SemiprimeD1ChildClockFactor
