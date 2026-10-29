/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInputBounds

/-! # Whole original public input checker, all finite assignments and bit costs
Both active and inactive positions and both input sides are included. The
physical index's length is identified with the original descriptor; all N/width/
bound/word/guard/flag work is ACTUALLY acquired by this SAME complete program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackPublicInputOriginal
open SemiprimeD1StackPublicInput SemiprimeD1StackPublicInputState SemiprimeD1StackPublicInputBounds
open SemiprimeMacroGraph SemiprimeMacroParameters SemiprimeBitArithmetic

/-- Complete original public verdict on EVERY original finite input assignment,
with no guard/canonicality/word/flag/result/clock advice to the executing machine. -/
theorem output_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val)
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits)))))→Bool) :
    (done bits (List.ofFn input) indexWord).data output=
      [(SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.input side i) input).accepted] := by
  change [M.expected bits (List.ofFn input) indexWord]=_
  exact congrArg (fun b : Bool=>[b]) (SemiprimeD1StackPublicInputMeaning.expected_original bits hc hN side i indexWord hi input)
/-- Original physical N+assignment+descriptor inventory is linear in bitlength,
including the optional active flag bit and every inactive position. -/
theorem original_inventory (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val)
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits)))))→Bool) :
    bits.length+(List.ofFn input).length+indexWord.length+2≤140*(bitLength (bitValue bits)+1) := by
  rw [List.length_ofFn,SemiprimeD1BinaryDigitAcquisitionBounds.canonical_width bits hc,hi]
  simp only [arity]
  have hiR:=i.isLt
  have hshape:=axes_product (bitLength (bitValue bits))
  have h:=(SemiprimeD1StackTransformArithmetic.prefix_powers (bitLength (bitValue bits)) _ le_rfl).1
  change transformLength (bitLength (bitValue bits))≤64*bitLength (bitValue bits)+1 at h
  split_ifs <;> omega
/-- Fixed original-bitlength quadratic ACTUAL clock before every original side,
position and finite assignment; old/native report clocks are not substituted. -/
theorem original_time (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val)
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits)))))→Bool) :
    runBound bits (List.ofFn input) indexWord≤1000000000000000000*(bitLength (bitValue bits)+1)^2 := by
  have h:=Nat.pow_le_pow_left (original_inventory bits hc side i indexWord hi input) 2
  rw [mul_pow] at h
  norm_num at h
  unfold runBound
  simp only [List.length_ofFn]
  omega
/-- SAME genuine fixed52-role bit machine on the original raw assignment, with
its complete original-N quadratic clock, before ALL original input families. -/
noncomputable def machineOriginal (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (side : Fin 2) (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val)
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits)))))→Bool) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn input) indexWord))
      (some (SemiprimeD1StackCalls.configuration (done bits (List.ofFn input) indexWord)))
      (1000000000000000000*(bitLength (bitValue bits)+1)^2) := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0) hN
  let h:=machineCheck bits (List.ofFn input) indexWord hb
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (original_time bits hc side i indexWord hi input)⟩
/-- EVERY actual original-input prefix counts all52 Boolean roles, retained
public/index/raw/suffix data, all work/shadows AND all real return-label cells. -/
theorem original_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (side : Fin 2) (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val)
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits)))))→Bool)
    (fuel : ℕ) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn input) indexWord)))=some cfg) :
    (∑k : Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤100000000000000000000*(bitLength (bitValue bits)+1)^2 := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0) hN
  have h:=machine_prefix_cells bits (List.ofFn input) indexWord hb fuel cfg hr
  have hp:=Nat.pow_le_pow_left (original_inventory bits hc side i indexWord hi input) 2
  rw [mul_pow] at hp
  norm_num at hp
  simp only [List.length_ofFn] at h
  omega
end RiemannGaussian.SemiprimeD1StackPublicInputOriginal
