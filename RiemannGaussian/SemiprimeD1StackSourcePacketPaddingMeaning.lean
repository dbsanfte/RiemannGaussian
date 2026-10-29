/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourcePacketPaddingEncoding
/-! # Exact original packet-multiple ceiling, including zero and exponent zero -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourcePacketPaddingMeaning
open SemiprimeD1StackSourcePacketPaddingEncoding
open SemiprimeBitArithmetic (bitValue)
/-- Actual reverse/trim preserves the zero-prefixed high-suffix value. -/
theorem rounded_value (a:Nat) (bits:List Bool) :
    bitValue (rounded a bits)=2^a*(bitValue (high a bits)+if (SemiprimeD1PacketRoundBits.cut a bits).low then 1 else 0) :=by
  rw [rounded,SemiprimeD1StackReduceExecution.trimReverse_value,List.reverse_reverse,prefixed,
    SemiprimeD1PacketRoundBits.zero_prefix_value]
  unfold roundedHigh
  split_ifs <;> simp only [SemiprimeD1StackSourceEnvironmentEncoding.successor_value,Nat.add_zero]
/-- The returned binary word has no high-order zeros, including the empty zero encoding. -/
theorem rounded_compact (a:Nat) (bits:List Bool) :SemiprimeSourceCompactBits.Compact (rounded a bits) :=
  SemiprimeD1StackReduceExecution.trimReverse_compact _
/-- The entire actual output word equals the frozen original PacketRoundBits ceiling; its old report clock is unused. -/
theorem rounded_original (a:Nat) (bits:List Bool) :rounded a bits=(SemiprimeD1PacketRoundBits.round a bits).bits :=by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ (rounded_compact a bits)
    (SemiprimeD1PacketRoundBits.round_compact a bits)
  rw [rounded_value,SemiprimeD1PacketRoundBits.round_value]
  rfl
/-- Zero maximum remains zero for every acquired unary exponent, with no forced packet allocation. -/
theorem rounded_zero (a:Nat) :rounded a []=[] :=by
  apply SemiprimeSourceCompactWordIds.compact_value_injective (rounded a []) [] (rounded_compact a []) trivial
  rw [rounded_value]
  cases a <;> rfl
/-- At exponent zero the source preserves every compact binary maximum exactly. -/
theorem rounded_at_zero (bits:List Bool) (h:SemiprimeSourceCompactBits.Compact bits) :rounded 0 bits=bits :=by
  apply SemiprimeSourceCompactWordIds.compact_value_injective _ _ (rounded_compact 0 bits) h
  rw [rounded_value]
  simp only [SemiprimeD1PacketRoundBits.cut,high,SemiprimeSourceCompactBits.copy_bits,pow_zero,Bool.false_eq_true,ite_false,Nat.add_zero,Nat.one_mul]
/-- No word longer than the acquired exponent plus the actual maximum and one carry is constructed as the final padded binary word. -/
theorem prefixed_length (a:Nat) (bits:List Bool) :(prefixed a bits).length≤ a+bits.length+1 :=by
  have hh:(high a bits).length≤ bits.length:=SemiprimeD1PacketRoundBits.cut_length a bits
  have hs:=SemiprimeD1StackSourceEnvironmentEncoding.successor_length (high a bits)
  unfold prefixed roundedHigh
  split_ifs <;> simp only [List.length_append,List.length_replicate] <;> omega
end RiemannGaussian.SemiprimeD1StackSourcePacketPaddingMeaning
