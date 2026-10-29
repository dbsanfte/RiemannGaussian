/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1ModeRoutingWireColours
import Mathlib.Data.Nat.Bits

/-! # Original arithmetic tile membership implies the physical orientation bit
This connects y=y0 mod2^(i+1) to the executed bit scan of the encoded tile ordinal.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeD1ModeRoutingTile
open SemiprimeD1ModeRoutingBits SemiprimeBitArithmetic

/-- Little-endian physical words have the usual mathematical binary constructor. -/
theorem bitValue_cons (b : Bool) (bits : List Bool) : bitValue (b::bits)=Nat.bit b (bitValue bits) := by
  cases b <;> simp [SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat,Nat.bit_val,Nat.add_comm]

/-- Actual physical bit acquisition agrees with the corresponding natural bit. -/
theorem readBit_testBit (bits : List Bool) (i : ℕ) :
    (readBit bits i).value=(bitValue bits).testBit i := by
  induction bits generalizing i with
  | nil => simp [readBit,bitValue]
  | cons b bits ih =>
    rw [bitValue_cons]
    cases i with
    | zero => exact (Nat.testBit_bit_zero b (bitValue bits)).symm
    | succ i =>
      rw [Nat.testBit_bit_succ]
      exact ih i

/-- The original arithmetic column-tile condition supplies the actual tile bit. -/
theorem tile_bit (a : ℕ) (i : Fin a) (tile : Fin (2^(i.val+1))) (slots : List Bool)
    (ht : bitValue slots%2^(i.val+1)=tile.val) :
    (slots[i.val]?).getD false=
      (SemiprimeD1ModeRoutingBits.acquire [] a i tile).bit := by
  have hh := congrArg (fun n => Nat.testBit n i.val) ht
  rw [Nat.testBit_mod_two_pow] at hh
  have hi : decide (i.val < i.val+1)=true := by simp
  rw [hi,Bool.true_and] at hh
  rw [←readBit_value,readBit_testBit]
  change (bitValue slots).testBit i.val=(readBit _ _).value
  rw [readBit_testBit,SemiprimeSourceHistogramPortKeys.encodeKey_value]
  exact hh

/-- Routing's tile bit does not depend on a packet's class fields. -/
theorem acquire_bit (key : List Bool) (a : ℕ) (i : Fin a) (tile : Fin (2^(i.val+1))) :
    (SemiprimeD1ModeRoutingBits.acquire key a i tile).bit=
      (SemiprimeD1ModeRoutingBits.acquire [] a i tile).bit := rfl

end RiemannGaussian.SemiprimeD1ModeRoutingTile
