/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import Mathlib

/-! # Actual same-bit crossing excludes the next two-adic power
No grid bound and no displacement valuation premise is assumed. Negative
interpolation nodes are included by integer remainder arithmetic.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1CrossingBit

/-- Adding exactly2^i flips the i-th bit even after reducing modulo2^(i+1). -/
theorem same_bit_not_shift (x y i : ℕ) (hbit : x.testBit i=y.testBit i) :
    y%2^(i+1)≠(2^i+x)%2^(i+1) := by
  intro h
  have hb:=congrArg (fun z : ℕ => z.testBit i) h
  simp only [Nat.testBit_mod_two_pow,Nat.lt_succ_self,decide_true,Bool.true_and,
    Nat.testBit_two_pow_add_eq] at hb
  rw [←hbit] at hb
  cases h : x.testBit i <;> simp [h] at hb

/-- Original crossing displacement cannot be divisible by the next power of two. -/
theorem crossing_not_dvd (t : ℤ) (x y i : ℕ)
    (ht : t%(2^(i+1):ℤ)=(2^i:ℤ)) (hbit : x.testBit i=y.testBit i) :
    ¬(2^(i+1):ℤ)∣t-y+x := by
  intro hd
  have hp : (0:ℤ)<2^i := by positivity
  have ht' : Int.ModEq (2^(i+1)) t (2^i) := by
    change t%_=(2^i:ℤ)%_
    rw [ht,Int.emod_eq_of_lt (by positivity) (by rw [pow_succ];omega)]
  have hz := hd.modEq_zero_int.add_right (y:ℤ)
  have hx := ht'.add_right (x:ℤ)
  have hz' : Int.ModEq (2^(i+1)) (t+x) y := by convert hz using 1 <;> ring
  have hy : Int.ModEq (2^(i+1)) (y:ℤ) (2^i+x) := hz'.symm.trans hx
  have hn : Nat.ModEq (2^(i+1)) y (2^i+x) := by
    apply Int.natCast_modEq_iff.mp
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add] using hy
  exact same_bit_not_shift x y i hbit hn

/-- Same-bit crossings have a nonzero displacement with valuation at most i. -/
theorem crossing_nonzero_and_val_le (t : ℤ) (x y i : ℕ)
    (ht : t%(2^(i+1):ℤ)=(2^i:ℤ)) (hbit : x.testBit i=y.testBit i) :
    (t - (y : ℤ) + (x : ℤ) ≠ 0) ∧ (padicValInt 2 (t - y + x) ≤ i) := by
  have hd:=crossing_not_dvd t x y i ht hbit
  constructor
  · intro hz
    apply hd
    rw [hz]
    exact dvd_zero _
  · by_contra h
    have hv : i+1≤padicValInt 2 (t-y+x) := by omega
    exact hd ((padicValInt_dvd_iff_of_ne_one (by decide : 2≠1) (i+1) _).mpr (Or.inr hv))

/-- An actual nonzero node of valuation i has the unique half-modulus residue.
This includes negative odd quotients. -/
theorem node_mod_of_valuation (t : ℤ) (i : ℕ) (ht : t≠0)
    (hi : padicValInt 2 t=i) : t%(2^(i+1):ℤ)=(2^i:ℤ) := by
  have hd : (2:ℤ)^i∣t := by rw [←hi];exact padicValInt_dvd t
  have hn : ¬(2:ℤ)^(i+1)∣t := by
    intro hpow
    have hh := (padicValInt_dvd_iff_of_ne_one (p:=2) (by decide : 2≠1) (i+1) t).mp hpow
    rcases hh with hz|hv
    · exact ht hz
    · omega
  rcases hd with ⟨q,hq⟩
  have hqnot : ¬(2:ℤ)∣q := by
    intro he
    rcases he with ⟨k,hk⟩
    apply hn
    refine ⟨k,?_⟩
    rw [hq,hk,pow_succ]
    ring
  have hqr : q%2=1 := by
    have hzero : q%2≠0 := by simpa only [Int.dvd_iff_emod_eq_zero] using hqnot
    have hnon:=Int.emod_nonneg q (by decide : (2:ℤ)≠0)
    have hlt:=Int.emod_lt_of_pos q (by decide : (0:ℤ)<2)
    omega
  rw [hq,pow_succ,Int.mul_emod_mul_of_pos q 2 (by positivity),hqr,mul_one]

/-- Original valuation-plus-same-bit conditions discharge displacement assumptions. -/
theorem crossing_of_valuation (t : ℤ) (x y i : ℕ) (ht : t≠0)
    (hi : padicValInt 2 t=i) (hbit : x.testBit i=y.testBit i) :
    (t - (y : ℤ) + (x : ℤ) ≠ 0) ∧ (padicValInt 2 (t - y + x) ≤ i) :=
  crossing_nonzero_and_val_le t x y i (node_mod_of_valuation t i ht hi) hbit

end RiemannGaussian.SemiprimeD1CrossingBit
