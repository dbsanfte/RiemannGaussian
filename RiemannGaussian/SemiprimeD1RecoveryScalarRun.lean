/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1HermiteWeightBits

/-! # Explicit native scalar loops for ORIGINAL recovery acquisition
These loops expose actual finite enumeration, powers and dyadic stripping.
Reports count native scalar arithmetic/control and allocated list cells. They
are not an assertion that native big-integer arithmetic costs one physical bit.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1RecoveryScalarRun

/-- Native scalar value with retained finite arithmetic/control/cell work. -/
structure Run (α : Type) where
  /-- The actual acquired result. -/
  value : α
  /-- Native operations and explicit traversed/constructed cells. -/
  work : ℕ

/-- Actual integer power by n repeated signed multiplications. -/
def intPower (x : ℤ) : ℕ → Run ℤ
  | 0 => ⟨1,1⟩
  | n+1 => let prev:=intPower x n;⟨prev.value*x,prev.work+3⟩

/-- The acquired integer power is the original requested power, not an answer input. -/
theorem intPower_value (x : ℤ) (n : ℕ) : (intPower x n).value=x^n := by
  induction n with
  | zero => simp [intPower]
  | succ n ih => simp only [intPower,ih,pow_succ]

/-- Every repeated integer power step is retained in the native report. -/
theorem intPower_work (x : ℤ) (n : ℕ) : (intPower x n).work=3*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [intPower,ih];omega

/-- Actual rational power by repeated canonical rational multiplication. -/
def rationalPower (x : ℚ) : ℕ → Run ℚ
  | 0 => ⟨1,1⟩
  | n+1 => let prev:=rationalPower x n;⟨prev.value*x,prev.work+3⟩

/-- The acquired rational power agrees with the original scalar power. -/
theorem rationalPower_value (x : ℚ) (n : ℕ) : (rationalPower x n).value=x^n := by
  induction n with
  | zero => simp [rationalPower]
  | succ n ih => simp only [rationalPower,ih,pow_succ]

/-- Native rational power work retains all canonical multiplication calls. -/
theorem rationalPower_work (x : ℚ) (n : ℕ) : (rationalPower x n).work=3*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rationalPower,ih];omega

/-- Actual ascending original grid indices, paying every append/copy and length scan. -/
def indices : ℕ → Run (List ℕ)
  | 0 => ⟨[],1⟩
  | n+1 => let prev:=indices n;⟨prev.value++[n],prev.work+2*prev.value.length+5⟩

/-- Acquired indices have EXACT original List.range ordering. -/
theorem indices_value (n : ℕ) : (indices n).value=List.range n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [indices,ih,List.range_succ]

/-- The actual complete original grid traversal has a literal polynomial report. -/
theorem indices_work (n : ℕ) : (indices n).work=n*n+4*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [indices,ih,indices_value,List.length_range];ring

/-- Actual replicated slope cells, with the immutable scalar value cached once. -/
def replicateRun (n : ℕ) (x : ℚ) : Run (List ℚ) :=
  match n with
  | 0 => ⟨[],1⟩
  | k+1 => let prev:=replicateRun k x;⟨x::prev.value,prev.work+3⟩

/-- Every acquired repeated slope has the original ordering and multiplicity. -/
theorem repeat_value (n : ℕ) (x : ℚ) : (replicateRun n x).value=List.replicate n x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [replicateRun,ih,List.replicate_succ]

/-- Repeated-slope allocation is completely retained in the report. -/
theorem repeat_work (n : ℕ) (x : ℚ) : (replicateRun n x).work=3*n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [replicateRun,ih];omega

/-- Native dyadic order by explicit modulo/division recursion with original finite fuel. -/
def orderFuel : ℕ → ℕ → Run ℕ
  | 0,_ => ⟨0,1⟩
  | fuel+1,n =>
    if n=0 then ⟨0,2⟩ else if n%2=0 then
      let tail:=orderFuel fuel (n/2);⟨tail.value+1,tail.work+5⟩
    else ⟨0,3⟩

/-- Bounded actual dyadic stripping recovers the original valuation without a valuation supplier. -/
theorem orderFuel_value (fuel n : ℕ) (hn : n=0 ∨ padicValNat 2 n≤fuel) :
    (orderFuel fuel n).value=padicValNat 2 n := by
  induction fuel generalizing n with
  | zero =>
    rcases hn with rfl|hn
    · simp [orderFuel]
    · simp only [orderFuel];omega
  | succ fuel ih =>
    by_cases hz : n=0
    · simp [orderFuel,hz]
    have hval : padicValNat 2 n≤fuel+1 := hn.resolve_left hz
    by_cases he : n%2=0
    · have hd : 2∣n := Nat.dvd_iff_mod_eq_zero.mpr he
      have hp : 1≤padicValNat 2 n := one_le_padicValNat_of_dvd hz hd
      have hv:=padicValNat.div (p:=2) hd
      have hb : padicValNat 2 (n/2)≤fuel := by omega
      simp only [orderFuel,hz,ite_false,he,ite_true,ih _ (Or.inr hb)]
      omega
    · have hv : padicValNat 2 n=0 := padicValNat.eq_zero_of_not_dvd
        (by intro h;exact he (Nat.dvd_iff_mod_eq_zero.mp h))
      simp only [orderFuel,hz,ite_false,he,hv]

/-- Every actual recursion frame is paid; the bound is polynomial in ORIGINAL fuel. -/
theorem orderFuel_work (fuel n : ℕ) : (orderFuel fuel n).work≤5*fuel+3 := by
  induction fuel generalizing n with
  | zero => simp [orderFuel]
  | succ fuel ih =>
    simp only [orderFuel]
    split_ifs <;> dsimp only
    · omega
    · have h:=ih (n/2);omega
    · omega

end RiemannGaussian.SemiprimeD1RecoveryScalarRun
