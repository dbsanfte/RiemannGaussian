/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputStorage
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputMeaning
import RiemannGaussian.SemiprimeD1StackPublicInputOriginal
/-! # Whole actual marked input source on the entire original input family
This is a physical per-entry source. Descriptor acquisition, whole table DFS,
other marked-table families and the literal recursive caller remain separate.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputOriginal
open SemiprimeD1StackMarkedPublicInput SemiprimeD1StackMarkedPublicInputEncoding
open SemiprimeD1StackMarkedPublicInputBounds SemiprimeD1StackMarkedPublicInputCost
open SemiprimeD1StackMarkedPublicInputMeaning SemiprimeD1StackMarkedPublicInputExecution
open SemiprimeMacroGraph SemiprimeMacroParameters SemiprimeBitArithmetic
/-- All actual input bytes are bounded uniformly before any side/index/assignment. -/
theorem original_inventory (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (side : Fin 2) (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val)
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits))))) → Bool) :
    inputSize bits (List.ofFn input) indexWord ≤ 140*(bitLength (bitValue bits)+1) :=
  SemiprimeD1StackPublicInputOriginal.original_inventory bits hc side i indexWord hi input
/-- One literal real source computes the exact new coefficient on EVERY local row;
there is no satisfying model, decoded digit, mark or precision answer premise. -/
theorem source_run_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val)
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits))))) → Bool) :
    ∃ t ≤ 100000000000000000000*(bitLength (bitValue bits)+1)^2,
      SemiprimeD1StackCalls.run program t (initial bits (List.ofFn input) indexWord [decide (side=1)])=
        some (done bits (List.ofFn input) indexWord (decide (side=1))) ∧
      bitValue ((done bits (List.ofFn input) indexWord (decide (side=1))).data (aux .output))=
        SemiprimeD1PackedMomentPrecision.coefficient (bitValue bits) hN (.inl (.input side i)) input ∧
      ((done bits (List.ofFn input) indexWord (decide (side=1))).data (aux .output)).length=
        SemiprimeD1PackedMomentPrecision.precision (bitValue bits) ∧
      (∀ k : P.Stack, (done bits (List.ofFn input) indexWord (decide (side=1))).data (checker k)=
        acquired bits (List.ofFn input) indexWord k) := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0) hN
  obtain ⟨t,ht,hr⟩ := source_run_bounded bits (List.ofFn input) indexWord (decide (side=1)) hb
  have hp := Nat.pow_le_pow_left (original_inventory bits hc side i indexWord hi input) 2
  rw [mul_pow] at hp
  norm_num at hp
  refine ⟨t,?_,hr,coefficient_original bits hc hN side i indexWord hi input,
    coefficient_width bits hc (List.ofFn input) indexWord (decide (side=1)),fun _ => rfl⟩
  unfold polynomial at ht
  omega
/-- Entire original-family space bound includes all66 real data roles, shadows
and actual return-label cells on the SAME compiled machine. -/
theorem original_prefix_cells (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (indexWord : List Bool) (hi : indexWord.length=i.val)
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits))))) → Bool)
    (fuel : Nat) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits (List.ofFn input) indexWord [decide (side=1)])))=some cfg) :
    (∑ k : Stack, (cfg.stk (some k)).length)+(cfg.stk none).length ≤
      100000000000000000000000*(bitLength (bitValue bits)+1)^2 := by
  have hb : bits≠[] := by intro he;rw [he] at hN;exact (Nat.lt_irrefl 0) hN
  have hs := SemiprimeD1StackMarkedPublicInputStorage.machine_prefix_cells bits
    (List.ofFn input) indexWord (decide (side=1)) hb fuel cfg hp
  have hh := Nat.pow_le_pow_left (original_inventory bits hc side i indexWord hi input) 2
  rw [mul_pow] at hh
  norm_num at hh
  omega
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputOriginal

