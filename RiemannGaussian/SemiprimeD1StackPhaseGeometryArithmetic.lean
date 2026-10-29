/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseGeometry
import RiemannGaussian.SemiprimeD1RecoveryWeightRun
/-! # Exact binary phase values and dyadic stripping semantics -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackPhaseGeometryArithmetic
open SemiprimeBitArithmetic SemiprimeBitDivision
/-- Actual little-endian power word, with only a+1 cells. -/
def powerWord (a : Nat) : List Bool :=List.replicate a false++[true]
/-- Actual low word produced by the frozen ripple subtractor. -/
def difference (xs ys : List Bool) : List Bool :=(subBits xs ys false).result.bits
/-- Actual first borrow selects the negative signed-point branch. -/
def negative (a : Nat) (t : List Bool) : Bool :=(subBits t (powerWord a) false).borrow
/-- Padded physical magnitude word, selected using only the actual borrow. -/
def magnitude (a : Nat) (t : List Bool) : List Bool :=
  if negative a t then difference (powerWord a) t else difference t (powerWord a)
/-- Proof-side low-bit scan result. Zero padding resets all provisional markers. -/
def valuation : List Bool→Nat
  | []=>0
  | false::xs=>if bitValue xs=0 then 0 else valuation xs+1
  | true::_=>0
/-- The center occupies exactly a+1 physical bits. -/
theorem powerWord_length (a : Nat) : (powerWord a).length=a+1 :=by simp [powerWord]
/-- Physical low-zero shifting constructs the exact binary center. -/
theorem powerWord_value (a : Nat) : bitValue (powerWord a)=2^a :=by
  induction a with
  | zero=>rfl
  | succ a ih=>
    change bitValue (false::powerWord a)=2^(a+1)
    simp only [bitValue,bitNat,Bool.false_eq_true,ite_false,Nat.zero_add,ih,pow_succ]
    omega
/-- Exact shift word identity used by the physically repeated center loop. -/
theorem powerWord_succ (a : Nat) : powerWord (a+1)=false::powerWord a :=rfl
/-- Exact acquired sign, including every possible all-zero padding word. -/
theorem negative_true (a : Nat) (t : List Bool) : negative a t=true ↔ bitValue t<2^a :=by
  simpa only [negative,powerWord_value,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero]
    using subBits_borrow_iff t (powerWord a) false
/-- The chosen subtraction never underflows. -/
theorem magnitude_value (a : Nat) (t : List Bool) :
    bitValue (magnitude a t)=((bitValue t: Int)-(2^a:Nat)).natAbs :=by
  unfold magnitude
  cases h:negative a t with
  | false=>
    have hn:¬bitValue t<2^a:=by intro ht;have hh:=(negative_true a t).mpr ht;rw [h] at hh;cases hh
    have hd:=subBits_difference (xs:=t) (ys:=powerWord a) h
    rw [powerWord_value] at hd
    simp only [Bool.false_eq_true,ite_false]
    change bitValue (difference t (powerWord a))=_
    rw [difference,hd]
    exact (Int.natAbs_natCast_sub_natCast_of_ge (by omega)).symm
  | true=>
    have hn:bitValue t<2^a:=(negative_true a t).mp h
    have hb:(subBits (powerWord a) t false).borrow=false:=by
      cases hh:(subBits (powerWord a) t false).borrow with
      | false=>rfl
      | true=>have hx:=(subBits_borrow_iff (powerWord a) t false).mp hh
              simp only [powerWord_value,bitNat,Bool.false_eq_true,ite_false,Nat.add_zero] at hx
              omega
    have hd:=subBits_difference hb
    rw [powerWord_value] at hd
    simp only [ite_true]
    change bitValue (difference (powerWord a) t)=_
    rw [difference,hd]
    exact (Int.natAbs_natCast_sub_natCast_of_le (by omega)).symm
/-- Both branch results retain the full paid subtractor width, including padding. -/
theorem magnitude_length (a : Nat) (t : List Bool) :
    (magnitude a t).length=max t.length (a+1) :=by
  unfold magnitude difference
  split_ifs <;> rw [(subBits_counts _ _ false).2.2.2.2,powerWord_length]
  exact max_comm _ _
/-- Physical provisional-order markers never outnumber scanned input cells. -/
theorem valuation_le (xs : List Bool) : valuation xs≤ xs.length :=by
  induction xs with
  | nil=>rfl
  | cons b xs ih=>
    cases b with
    | false=>simp only [valuation,List.length_cons];split_ifs <;> omega
    | true=>change 0≤ xs.length+1;omega
/-- The all-zero word has dyadic order zero under the original convention. -/
theorem valuation_zero (xs : List Bool) (h : bitValue xs=0) : valuation xs=0 :=by
  cases xs with
  | nil=>rfl
  | cons b xs=>
    cases b with
    | false=>
      have ht:bitValue xs=0:=by
        simp only [bitValue,bitNat,Bool.false_eq_true,ite_false,Nat.zero_add] at h
        omega
      simp only [valuation,ht,ite_true]
    | true=>
      simp only [bitValue,bitNat,ite_true] at h
      omega
/-- The actual low-bit stripping result is exactly the original 2-adic valuation. -/
theorem valuation_eq (xs : List Bool) : valuation xs=padicValNat 2 (bitValue xs) :=by
  induction xs with
  | nil=>simp [valuation,bitValue]
  | cons b xs ih=>
    cases b with
    | false=>
      by_cases hz:bitValue xs=0
      · simp [valuation,bitValue,bitNat,hz]
      · simp only [valuation,hz,ite_false,bitValue,bitNat,Bool.false_eq_true,ite_false,Nat.zero_add]
        rw [padicValNat.mul (by decide : (2:Nat)≠0) hz,padicValNat_self,←ih]
        omega
    | true=>
      have h:¬2∣1+2*bitValue xs:=by omega
      simpa only [valuation,bitValue,bitNat,ite_true] using (padicValNat.eq_zero_of_not_dvd h).symm
end RiemannGaussian.SemiprimeD1StackPhaseGeometryArithmetic
