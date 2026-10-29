/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1JetScalarBits

/-! # Physical odd inversion using only bounded binary additions and products
The inverse is acquired by p explicit Newton steps modulo2^p. Negative one is
the actual p-cell all-true word. No native modular inverse or requested inverse
word is supplied; every old report is retained once.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeD1OddInverseBits
open SemiprimeBitArithmetic
open SemiprimeD1JetScalarBits
open SemiprimeSourceCompactBits (Compact)

/-- Exact interpretation of one actual scalar word. -/
def value (p : ℕ) (bits : List Bool) : ZMod (2^p) := bitValue bits

/-- Physically allocate the modular negative-one word once. -/
def negativeOne (p : ℕ) : Report := ⟨List.replicate p true,p+2⟩

/-- Exact unsigned all-one word value, without subtraction conventions at zero. -/
theorem negativeOne_value (p : ℕ) : bitValue (negativeOne p).bits+1=2^p := by
  induction p with
  | zero => simp [negativeOne,bitValue]
  | succ p ih =>
    simp only [negativeOne,List.replicate_succ,bitValue,bitNat,ite_true,pow_succ] at ih ⊢
    omega

/-- The acquired all-one word really denotes negative one in the target ring. -/
theorem negativeOne_zmod (p : ℕ) : value p (negativeOne p).bits = -1 := by
  have h : (bitValue (negativeOne p).bits:ZMod (2^p))+1=0 := by
    have he := congrArg (fun n : ℕ => (n:ZMod (2^p))) (negativeOne_value p)
    simpa only [Nat.cast_add,Nat.cast_one,ZMod.natCast_self] using he
  exact add_eq_zero_iff_eq_neg.mp h

/-- Physical reduction agrees with the original word's target-ring value. -/
theorem reduce_zmod (p : ℕ) (bits : List Bool) : value p (reduce p bits).bits=value p bits := by
  simp only [value,reduce_value,ZMod.natCast_mod]

/-- One literal Newton step, with each product and sum cached exactly once. -/
def step (p : ℕ) (a negative two current : List Bool) : Report :=
  let product := mul p a current
  let opposite := mul p negative product.bits
  let correction := add p two opposite.bits
  let out := mul p current correction.bits
  ⟨out.bits,product.clock+opposite.clock+correction.clock+out.clock+10⟩

/-- Every actual step produces a compact target-width word. -/
theorem step_good (p : ℕ) (a negative two current : List Bool) :
    (step p a negative two current).bits.length≤p ∧ Compact (step p a negative two current).bits :=
  ⟨mul_length _ _ _,mul_compact _ _ _⟩

/-- The actual scalar circuit implements x*(2-a*x), using no signed division. -/
theorem step_value (p : ℕ) (a negative two current : List Bool)
    (hnegative : value p negative = -1) (htwo : value p two=2) :
    value p (step p a negative two current).bits =
      value p current*(2-value p a*value p current) := by
  change (bitValue (mul p current (add p two (mul p negative (mul p a current).bits).bits).bits).bits:ZMod (2^p))=_
  rw [mul_zmod,add_zmod,mul_zmod,mul_zmod]
  change value p current*(value p two+value p negative*(value p a*value p current))=_
  rw [hnegative,htwo]
  ring

/-- One actual Newton step squares the old inverse error. -/
theorem step_error (p : ℕ) (a negative two current : List Bool)
    (hnegative : value p negative = -1) (htwo : value p two=2) :
    value p a*value p (step p a negative two current).bits-1 =
      -(value p a*value p current-1)^2 := by
  rw [step_value p a negative two current hnegative htwo]
  ring

/-- Explicit row of p bounded-word Newton updates, retaining every previous report. -/
def loop (p : ℕ) (a negative two : List Bool) : ℕ→Report
  | 0 => reduce p [true]
  | n+1 =>
    let previous := loop p a negative two n
    let here := step p a negative two previous.bits
    ⟨here.bits,previous.clock+here.clock+3⟩

/-- All actual inverse iterates remain compact and have intrinsic precision width. -/
theorem loop_good (p : ℕ) (a negative two : List Bool) (n : ℕ) :
    (loop p a negative two n).bits.length≤p ∧ Compact (loop p a negative two n).bits := by
  cases n with
  | zero => exact ⟨reduce_length _ _,reduce_compact _ _⟩
  | succ n => exact step_good _ _ _ _ _

/-- Each actual iterate gains at least one dyadic bit; the ring may have zero divisors. -/
theorem loop_content (p : ℕ) (a negative two : List Bool)
    (hnegative : value p negative = -1) (htwo : value p two=2)
    (ha : ∃k : ZMod (2^p),value p a-1=2*k) (n : ℕ) :
    ∃c : ZMod (2^p),value p a*value p (loop p a negative two n).bits-1=2^(n+1)*c := by
  induction n with
  | zero =>
    obtain ⟨k,hk⟩ := ha
    refine ⟨k,?_⟩
    change value p a*value p (reduce p [true]).bits-1=2^(0+1)*k
    rw [reduce_zmod]
    have hone : value p [true]=(1:ZMod (2^p)) := by norm_num [value,bitValue,bitNat]
    simpa only [hone,mul_one,Nat.zero_add,pow_one] using hk
  | succ n ih =>
    obtain ⟨c,hc⟩ := ih
    refine ⟨-(2:ZMod (2^p))^n*c^2,?_⟩
    change value p a*value p (step p a negative two (loop p a negative two n).bits).bits-1=_
    rw [step_error p a negative two _ hnegative htwo,hc,mul_pow]
    have he : ((2:ZMod (2^p))^(n+1))^2=2^(n+1+1)*2^n := by
      rw [←pow_mul,←pow_add]
      congr 1
      omega
    rw [he]
    ring

/-- Actual odd-input word inverse, with source truncation and constants paid once. -/
def inverse (p : ℕ) (input : List Bool) : Report :=
  let a := reduce p input
  let negative := negativeOne p
  let two := reduce p [false,true]
  let out := loop p a.bits negative.bits two.bits p
  ⟨out.bits,a.clock+negative.clock+two.clock+out.clock+10⟩

/-- The actual acquired inverse has no high zero bytes or supplied width premise. -/
theorem inverse_good (p : ℕ) (input : List Bool) :
    (inverse p input).bits.length≤p ∧ Compact (inverse p input).bits :=
  loop_good _ _ _ _ _

/-- Every original odd word has its true multiplicative inverse modulo2^p.
No native inverse operation, desired inverse answer or unit oracle is an input. -/
theorem inverse_correct (p : ℕ) (input : List Bool) (hodd : Odd (bitValue input)) :
    value p input*value p (inverse p input).bits=1 := by
  let a := (reduce p input).bits
  let negative := (negativeOne p).bits
  let two := (reduce p [false,true]).bits
  have ha : ∃k : ZMod (2^p),value p a-1=2*k := by
    obtain ⟨k,hk⟩ := hodd
    refine ⟨(k:ZMod (2^p)),?_⟩
    rw [show value p a=value p input from reduce_zmod p input]
    have he : value p input=2*(k:ZMod (2^p))+1 := by
      change (bitValue input:ZMod (2^p))=2*(k:ZMod (2^p))+1
      rw [hk]
      push_cast
      rfl
    rw [he]
    ring
  have ht : value p two=2 := by
    rw [show value p two=value p [false,true] from reduce_zmod p _]
    norm_num [value,bitValue,bitNat]
  obtain ⟨c,hc⟩ := loop_content p a negative two (negativeOne_zmod p) ht ha p
  have hz : (2:ZMod (2^p))^p=0 := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using ZMod.natCast_self (2^p)
  rw [pow_succ,hz,zero_mul,zero_mul,sub_eq_zero] at hc
  change value p input*value p (loop p a negative two p).bits=1
  rw [←show value p a=value p input from reduce_zmod p input]
  exact hc

end RiemannGaussian.SemiprimeD1OddInverseBits
