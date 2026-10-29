/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OddInverseBits

/-! # Intrinsic physical cost of acquired odd inverses -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000
namespace RiemannGaussian.SemiprimeD1OddInverseBounds
open SemiprimeD1OddInverseBits SemiprimeD1JetScalarBits
open SemiprimeBitArithmetic

/-- One actual bounded modular product has a fixed quadratic physical report. -/
theorem mul_bounded (p : ℕ) (a b : List Bool) (ha : a.length ≤ p) (hb : b.length ≤ p) :
    (mul p a b).clock ≤ 50*(p+1)^2 := by
  have hc := mul_clock p a b
  have hm := Nat.mul_le_mul ha (show a.length+b.length+2 ≤ 2*p+2 by omega)
  nlinarith

/-- One actual bounded modular sum has a fixed linear physical report. -/
theorem add_bounded (p : ℕ) (a b : List Bool) (ha : a.length ≤ p) (hb : b.length ≤ p) :
    (add p a b).clock ≤ 40*(p+1) := by
  have hc := add_clock p a b
  have hm : max a.length b.length ≤ p := max_le ha hb
  omega

/-- Every scalar operation of one Newton stage is paid, with no output width advice. -/
theorem step_clock (p : ℕ) (a negative two current : List Bool)
    (ha : a.length ≤ p) (hn : negative.length ≤ p) (ht : two.length ≤ p) (hx : current.length ≤ p) :
    (step p a negative two current).clock ≤ 250*(p+1)^2 := by
  have h1 := mul_bounded p a current ha hx
  have h2 := mul_bounded p negative (mul p a current).bits hn (mul_length _ _ _)
  have h3 := add_bounded p two (mul p negative (mul p a current).bits).bits ht (mul_length _ _ _)
  have h4 := mul_bounded p current (add p two (mul p negative (mul p a current).bits).bits).bits hx
    (add_length _ _ _)
  change (mul p a current).clock+(mul p negative (mul p a current).bits).clock+
    (add p two (mul p negative (mul p a current).bits).bits).clock+
      (mul p current (add p two (mul p negative (mul p a current).bits).bits).bits).clock+10 ≤ _
  nlinarith

/-- Literal p-independent stage loop bound, with earlier reports retained once. -/
theorem loop_clock (p : ℕ) (a negative two : List Bool)
    (ha : a.length ≤ p) (hn : negative.length ≤ p) (ht : two.length ≤ p) (n : ℕ) :
    (loop p a negative two n).clock ≤ 9*p+5+n*(250*(p+1)^2+3) := by
  induction n with
  | zero => simpa only [loop,Nat.zero_mul,Nat.add_zero] using reduce_clock p [true]
  | succ n ih =>
    have hs := step_clock p a negative two (loop p a negative two n).bits ha hn ht
      (loop_good p a negative two n).1
    change (loop p a negative two n).clock+(step p a negative two (loop p a negative two n).bits).clock+3 ≤ _
    nlinarith

/-- Complete original-word inverse acquisition has a cubic physical report.
Only p is needed: truncation visits at most p bits of the source word. -/
theorem inverse_clock (p : ℕ) (input : List Bool) :
    (inverse p input).clock ≤ 400*(p+1)^3 := by
  have ha := reduce_clock p input
  have ht := reduce_clock p [false,true]
  have hl := loop_clock p (reduce p input).bits (negativeOne p).bits (reduce p [false,true]).bits
    (reduce_length _ _) (by simp [negativeOne]) (reduce_length _ _) p
  change (reduce p input).clock+(negativeOne p).clock+(reduce p [false,true]).clock+
    (loop p (reduce p input).bits (negativeOne p).bits (reduce p [false,true]).bits p).clock+10 ≤ _
  simp only [negativeOne] at hl ⊢
  nlinarith

/-- The actually computed physical inverse is the same unit inverse used by the
existing universal kernel semantics; no inverse answer or unit proof is supplied. -/
theorem inverse_eq_native (p : ℕ) (input : List Bool) (hodd : Odd (bitValue input)) :
    value p (inverse p input).bits=(value p input)⁻¹ := by
  have hc := inverse_correct p input hodd
  have hu : IsUnit (value p input) := isUnit_iff_exists_inv.mpr ⟨_,hc⟩
  calc
    _ = value p (inverse p input).bits*1 := (mul_one _).symm
    _ = value p (inverse p input).bits*(value p input*(value p input)⁻¹) := by
      rw [ZMod.mul_inv_of_unit _ hu]
    _ = (value p input*value p (inverse p input).bits)*(value p input)⁻¹ := by ring
    _ = _ := by rw [hc,one_mul]

end RiemannGaussian.SemiprimeD1OddInverseBounds
