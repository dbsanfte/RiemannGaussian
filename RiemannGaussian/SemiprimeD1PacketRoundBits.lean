/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1CounterMaximum

/-! # Physical rounding of an acquired maximum to a packet multiple
The packet size is 2^a. The implementation scans the low bits, copies the high
tail once, increments only when needed, and prefixes actual zero bits. It never
encodes a native quotient, maximum or padded-load answer.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1PacketRoundBits
open SemiprimeBitArithmetic

/-- Actual low-bit nonzero flag and physically copied high tail. -/
structure Cut where
  /-- Some removed low bit was one. -/
  low : Bool
  /-- Acquired high bits. -/
  high : List Bool
  /-- All scans, Boolean decisions and the single actual high-tail copy. -/
  clock : ℕ
  deriving Repr

/-- Remove at most a low cells; no loop over an empty source is executed. -/
def cut : ℕ → List Bool → Cut
  | 0,bits =>
    let out := SemiprimeSourceCompactBits.copy bits
    ⟨false,out.bits,out.clock+2⟩
  | _+1,[] => ⟨false,[],1⟩
  | a+1,b::bits =>
    let rest := cut a bits
    ⟨b || rest.low,rest.high,rest.clock+3⟩

/-- The high word is exactly the original suffix, not a re-encoded integer. -/
theorem cut_high (a : ℕ) (bits : List Bool) : (cut a bits).high=bits.drop a := by
  induction a generalizing bits with
  | zero => simp [cut,SemiprimeSourceCompactBits.copy_bits]
  | succ a ih => cases bits <;> simp [cut,ih]

/-- Width follows the actual acquired source word. -/
theorem cut_length (a : ℕ) (bits : List Bool) : (cut a bits).high.length≤bits.length := by
  rw [cut_high,List.length_drop]
  omega

/-- The single scan and copied tail cost linear work in the actual source width. -/
theorem cut_clock (a : ℕ) (bits : List Bool) : (cut a bits).clock≤3*bits.length+3 := by
  induction a generalizing bits with
  | zero => simp [cut,SemiprimeSourceCompactBits.copy_clock]
  | succ a ih =>
    cases bits with
    | nil => simp [cut]
    | cons b bits =>
      have h := ih bits
      simp only [cut,List.length_cons]
      omega

/-- The acquired high tail has the exact quotient interval. -/
theorem cut_interval (a : ℕ) (bits : List Bool) :
    2^a*bitValue (cut a bits).high≤bitValue bits ∧
      bitValue bits<2^a*(bitValue (cut a bits).high+1) := by
  induction a generalizing bits with
  | zero => simp [cut,SemiprimeSourceCompactBits.copy_bits]
  | succ a ih =>
    cases bits with
    | nil => simp [cut,bitValue,pow_pos (by decide : 0<(2:ℕ))]
    | cons b bits =>
      have h := ih bits
      have hb : bitNat b≤1 := by cases b <;> simp [bitNat]
      simp only [cut,bitValue,pow_succ]
      constructor <;> nlinarith [h.1,h.2]

/-- The low-bit flag is zero exactly at a packet multiple of the acquired quotient. -/
theorem cut_zero (a : ℕ) (bits : List Bool) :
    (cut a bits).low=false ↔ bitValue bits=2^a*bitValue (cut a bits).high := by
  induction a generalizing bits with
  | zero => simp [cut,SemiprimeSourceCompactBits.copy_bits]
  | succ a ih =>
    cases bits with
    | nil => simp [cut,bitValue]
    | cons b bits =>
      have h := ih bits
      cases b with
      | false =>
        simp only [cut,Bool.false_or,bitValue,bitNat,Bool.false_eq_true,ite_false,zero_add,pow_succ]
        rw [h]
        constructor <;> intro he <;> nlinarith
      | true =>
        simp only [cut,Bool.true_or,Bool.true_eq_false,bitValue,bitNat,ite_true,pow_succ]
        constructor
        · intro hf
          exact hf.elim
        · intro he
          have hp := congrArg (fun n : ℕ => n%2) he
          norm_num [Nat.add_mod,Nat.mul_mod] at hp

/-- Prefixing actual zero cells multiplies the existing value by the packet size. -/
theorem zero_prefix_value (a : ℕ) (bits : List Bool) :
    bitValue (List.replicate a false++bits)=2^a*bitValue bits := by
  induction a with
  | zero => simp
  | succ a ih =>
    simp only [List.replicate_succ,List.cons_append,bitValue,bitNat,Bool.false_eq_true,
      ite_false,zero_add,ih,pow_succ]
    ring

/-- Physical ceiling to the next packet multiple, retaining every producer report. -/
def round (a : ℕ) (bits : List Bool) : SemiprimeSourceCompactBits.Report :=
  let data := cut a bits
  let high := if data.low then SemiprimeSourceCompactBits.increment data.high else ⟨data.high,0⟩
  let out := SemiprimeSourceCompactBits.trim (List.replicate a false++high.bits)
  ⟨out.bits,data.clock+high.clock+3*a+out.clock+5⟩

/-- The executed ceiling is a multiple of the packet size. -/
theorem round_value (a : ℕ) (bits : List Bool) :
    bitValue (round a bits).bits=
      2^a*(bitValue (cut a bits).high+if (cut a bits).low then 1 else 0) := by
  unfold round
  dsimp only
  rw [SemiprimeSourceCompactBits.trim_value,zero_prefix_value]
  split_ifs <;> simp [SemiprimeSourceCompactBits.increment_value]

/-- The actual rounded maximum covers every original count. -/
theorem le_round (a : ℕ) (bits : List Bool) : bitValue bits≤bitValue (round a bits).bits := by
  have h := cut_interval a bits
  rw [round_value]
  cases hl : (cut a bits).low with
  | false =>
    have he := (cut_zero a bits).mp hl
    simp only [Bool.false_eq_true,ite_false,add_zero]
    omega
  | true => simpa only [ite_true] using h.2.le

/-- At most one packet of padding is added, even at zero. -/
theorem round_le (a : ℕ) (bits : List Bool) :
    bitValue (round a bits).bits≤bitValue bits+2^a := by
  have h := cut_interval a bits
  rw [round_value]
  split_ifs <;> nlinarith

/-- No unary expansion of the numerical maximum is acquired. -/
theorem round_compact (a : ℕ) (bits : List Bool) :
    SemiprimeSourceCompactBits.Compact (round a bits).bits :=
  SemiprimeSourceCompactBits.trim_compact _

end RiemannGaussian.SemiprimeD1PacketRoundBits
