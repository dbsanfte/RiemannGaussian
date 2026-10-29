/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1WordPacketTableClock

/-! # Explicit new right-table exponential factor
The actual tape recopy is cubic in the truth-table scale. Its factor is
therefore retained as 2^(3D), not transferred from the frozen cheap lookup.
-/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1WordPacketClockFactor
open SemiprimeD1JetAxes SemiprimeD1WordPacketTableClock
open SemiprimeD1WordPacketEntryClock
open SemiprimeD1ChildTableCopyTape (tapeBudget tableCap)

/-- Exact polynomial multiplying a cubed table scale in tape serialization. -/
def tapeCoefficient (C : ℕ) : ℕ := 8*(C+1)*C+11

/-- Actual scan/serialization budget at a scaled stored table is cubic in that scale. -/
theorem tape_scaled (C q : ℕ) (hq:1 ≤ q) :
    (tapeBudget (C*q)+7)*q ≤ tapeCoefficient C*q^3 := by
  have hs:C*q+1 ≤ (C+1)*q:=by nlinarith
  have hm:8*(C*q+1)*(C*q) ≤ 8*((C+1)*q)*(C*q):=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 8 hs)
  have hp:1 ≤ q^2:=Nat.one_le_pow _ _ hq
  have hh:11 ≤ 11*q^2:=by nlinarith
  unfold tapeBudget tapeCoefficient
  calc
    _ ≤ (8*((C+1)*q)*(C*q)+11*q^2)*q :=
      Nat.mul_le_mul_right q (by omega)
    _ = _ := by ring

/-- Physical per-entry storage coefficient before its literal truth-table scale. -/
def storageCoefficient (ctx : Context) : ℕ := ctx.rank*(3*ctx.precision+4)+3

/-- Polynomial prefactor of the complete actual right acquisition and recopy. -/
def rightFactor (ctx : Context) (a A K P T B L E H Z G e : ℕ) : ℕ :=
  H+Z+G+L+A+e+22+(entryPolynomial ctx a A K P T B L E+7)+tapeCoefficient (storageCoefficient ctx)

/-- Concrete right budget factors through the original catalogue/table envelope.
Every source/header/node contribution remains in the polynomial prefactor. -/
theorem rightClock_factor (ctx : Context) (a A K P T B L E H Z G e D : ℕ)
    (hcoef:2^A*(K+1)^A ≤ 2^D) :
    rightClock ctx a A K P T B L E H Z G e ≤ rightFactor ctx a A K P T B L E H Z G e*2^(3*D) := by
  let q:ℕ:=2^A
  let v:ℕ:=(K+1)^A
  let cap:ℕ:=2^(3*D)
  have hq:1 ≤ q:=Nat.one_le_two_pow
  have hv:1 ≤ v:=Nat.one_le_pow _ _ (by omega)
  have hcap:1 ≤ cap:=Nat.one_le_two_pow
  have hqv:q ≤ q*v:=by nlinarith
  have hpow:(q*v)^3 ≤ cap:=by
    change (q*v)^3 ≤ 2^(3*D)
    rw [Nat.mul_comm 3 D,pow_mul]
    exact Nat.pow_le_pow_left hcoef 3
  have hq3:q^3 ≤ cap:=(Nat.pow_le_pow_left hqv 3).trans hpow
  have he:q*v ≤ cap:=hcoef.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hc:=entryClock_factor ctx a A K P T B L E
  have hadd:entryClock ctx a A K P T B L E+7 ≤ 
      (entryPolynomial ctx a A K P T B L E+7)*v:=by
    have h7:7≤7*v:=by omega
    calc
      _ ≤ entryPolynomial ctx a A K P T B L E*v+7*v:=Nat.add_le_add hc h7
      _ = _:=by ring
  have hentry:(entryClock ctx a A K P T B L E+7)*q ≤ 
      (entryPolynomial ctx a A K P T B L E+7)*cap:=by
    calc
      _  ≤  ((entryPolynomial ctx a A K P T B L E+7)*v)*q:=Nat.mul_le_mul_right _ hadd
      _ = (entryPolynomial ctx a A K P T B L E+7)*(q*v):=by ring
      _  ≤  _:=Nat.mul_le_mul_left _ he
  have htape:(tapeBudget (tableCap ctx A)+7)*q ≤ 
      tapeCoefficient (storageCoefficient ctx)*cap:=by
    have h:=tape_scaled (storageCoefficient ctx) q hq
    exact h.trans (Nat.mul_le_mul_left _ hq3)
  have hconstant:H+Z+G+L+A+e+22 ≤ (H+Z+G+L+A+e+22)*cap:=by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (H+Z+G+L+A+e+22) hcap
  unfold rightClock tableClock rightFactor
  change H+Z+(entryClock ctx a A K P T B L E+7)*q+L+12+G+
      (tapeBudget (tableCap ctx A)+7)*q+A+e+10 ≤ _
  calc
    _ = (H+Z+G+L+A+e+22)+(entryClock ctx a A K P T B L E+7)*q+
      (tapeBudget (tableCap ctx A)+7)*q:=by ring
    _  ≤  (H+Z+G+L+A+e+22)*cap+(entryPolynomial ctx a A K P T B L E+7)*cap+
      tapeCoefficient (storageCoefficient ctx)*cap:=
      Nat.add_le_add (Nat.add_le_add hconstant hentry) htape
    _ = _:=by ring
end RiemannGaussian.SemiprimeD1WordPacketClockFactor
