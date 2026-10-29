/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1RadixOperandBits
import RiemannGaussian.SemiprimePaidFactorDecoder
import RiemannGaussian.SemiprimePublicBudgetDimensions
import RiemannGaussian.SemiprimeMacroEntryBitPrimitives

/-! # Original selected-wire operand, assembled as literal Boolean digits
The closed caller acquires the original edge enumeration and reads each original
input digit using the existing paid explicit index/selected-label scans. Radix
assembly then uses only physical shifts and additions. The typed label/index
reports stay separate from the arithmetic bit clock and need host lowering.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1PublicOperandBits
open scoped BigOperators
open SemiprimePublicAcquiredExecution SemiprimeMacroParameters SemiprimeBitArithmetic
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking
attribute [local irreducible] edgeEnumeration decodeOperand

/-- Actual digit bytes and the original typed index/label traversal report. -/
structure DigitRun where
  /-- Literal little-endian digit read from the selected original wire list. -/
  bits : List Bool
  /-- Every actual original index scan and selected-label scan, with list tags. -/
  metadataWork : ℕ

/-- Read one original input digit from an internally acquired, cached edge list. -/
def digit (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2)
    (edges : FiniteEnumeration (PublicEdge N)) (i : ℕ) : DigitRun :=
  if hi : i < firstAxis (bitLength N)*secondAxis (bitLength N) then
    let reports := List.ofFn (fun bit => SemiprimePaidFactorDecoder.inputBit N side values i hi bit edges)
    ⟨reports.map (fun r => r.value),(reports.map (fun r => r.work)).sum+3*reports.length+3⟩
  else ⟨[],2⟩

/-- Actual cached digit bytes reproduce the public decoder's original bit word. -/
theorem digit_value (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2) (i : ℕ) :
    bitValue (digit N values side (edgeEnumeration N) i).bits=
      if hi : i < firstAxis (bitLength N)*secondAxis (bitLength N) then
        SemiprimeMacroEntryExecution.binaryDecode (fun bit =>
          SemiprimeAcquiredPrefixSearch.selectedBits values
            ((edgeEnumeration N).equivFin.symm (SemiprimePaidFactorDecoder.inputWire N side i hi bit)))
      else 0 := by
  unfold digit
  split
  · rename_i hi
    simp only [List.map_ofFn]
    change bitValue (SemiprimeMacroEntryBitPrimitives.portBits _)=_
    rw [SemiprimeMacroEntryBitPrimitives.portBits_value]
    congr 1
    funext bit
    exact SemiprimePaidFactorDecoder.inputBit_value N side values i hi bit _ rfl
  · rfl

/-- Digit width is derived from the literal original input-port construction. -/
theorem digit_width (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2)
    (edges : FiniteEnumeration (PublicEdge N)) (i : ℕ) :
    (digit N values side edges i).bits.length ≤ firstAxis (bitLength N)*secondAxis (bitLength N)+1 := by
  unfold digit
  split <;> simp only [List.length_map,List.length_ofFn,List.length_nil] <;> omega

/-- Every digit's original index/label report has a closed actual-data bound. -/
theorem digit_work (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2) (i : ℕ) :
    (digit N values side (edgeEnumeration N) i).metadataWork ≤
      (firstAxis (bitLength N)*secondAxis (bitLength N)+1)*
        (2*wireCount N+6*values.length+9)+3 := by
  unfold digit
  split
  · rename_i hi
    have hs := Finset.sum_le_sum (fun (bit : Fin (firstAxis (bitLength N)*secondAxis (bitLength N)+1))
        (_ : bit∈Finset.univ) =>
      SemiprimePaidFactorDecoder.inputBit_work N side values i hi bit _ rfl)
    simp only [List.map_ofFn,List.sum_ofFn,List.length_ofFn,Function.comp_def]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
    nlinarith
  · change 2 ≤ _
    omega

/-- Literal operand bytes and separate physical-arithmetic/native-index reports. -/
structure Run where
  /-- The assembled binary operand, without evaluating native radix powers. -/
  bits : List Bool
  /-- Actual physical Horner shifts/additions and radix-template allocation. -/
  arithmeticClock : ℕ
  /-- Actual typed index/label reports and finite constructor allowances. -/
  metadataWork : ℕ

/-- Closed original-N operand producer; no word, decoder or bit getter is input. -/
def run (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2) : Run :=
  let edges := edgeEnumeration N
  let original := (List.range (digitCount (bitLength N))).map (digit N values side edges)
  let radix := List.replicate (radixBits (bitLength N)) false
  let assembled := SemiprimeD1RadixOperandBits.run radix (original.map DigitRun.bits)
  ⟨assembled.bits,assembled.clock+3*radix.length+3*(original.length+1)+1,
    (original.map DigitRun.metadataWork).sum+10*(wireCount N+original.length+radix.length+1)^2⟩

/-- The actual Boolean output equals the original ordinary integer operand
decoder. Original label and port order, carries and all radix positions agree. -/
theorem run_value (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2) :
    bitValue (run N values side).bits=decodeOperand N values side := by
  unfold run
  dsimp only
  rw [SemiprimeD1RadixOperandBits.run_value]
  simp only [List.length_replicate,List.map_map,Function.comp_def]
  rw [SemiprimeD1RadixOperandBits.value_range]
  unfold decodeOperand
  apply Finset.sum_congr rfl
  intro i _
  rw [digit_value]
  rfl

/-- Every physical intermediate/output width is polynomial in the actual
original digit count, radix width and input-word width. -/
theorem run_width (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2) :
    (run N values side).bits.length ≤ digitCount (bitLength N)*
      (radixBits (bitLength N)+firstAxis (bitLength N)*secondAxis (bitLength N)+2) := by
  have h := SemiprimeD1RadixOperandBits.run_width
    (List.replicate (radixBits (bitLength N)) false)
    (((List.range (digitCount (bitLength N))).map (digit N values side (edgeEnumeration N))).map DigitRun.bits)
    (firstAxis (bitLength N)*secondAxis (bitLength N)+1) (by
      intro bits hb
      obtain ⟨source,hs,rfl⟩ := List.mem_map.mp hb
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hs
      exact digit_width N values side _ i)
  simpa only [run,List.length_replicate,List.length_map,List.length_range,Nat.add_assoc] using h

/-- All physical arithmetic work of the actual original operand assembly. -/
theorem run_arithmeticClock (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2) :
    (run N values side).arithmeticClock ≤ 20*(digitCount (bitLength N)+1)^2*
      (radixBits (bitLength N)+firstAxis (bitLength N)*secondAxis (bitLength N)+2)+
      3*radixBits (bitLength N)+3*(digitCount (bitLength N)+1)+1 := by
  have h := SemiprimeD1RadixOperandBits.run_clock
    (List.replicate (radixBits (bitLength N)) false)
    (((List.range (digitCount (bitLength N))).map (digit N values side (edgeEnumeration N))).map DigitRun.bits)
    (firstAxis (bitLength N)*secondAxis (bitLength N)+1) (by
      intro bits hb
      obtain ⟨source,hs,rfl⟩ := List.mem_map.mp hb
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hs
      exact digit_width N values side _ i)
  simp only [List.length_replicate,List.length_map,List.length_range,Nat.add_assoc] at h
  norm_num only at h
  unfold run
  simp only [List.length_replicate,List.length_map,List.length_range]
  simp only [Nat.add_assoc] at h ⊢
  omega

/-- Original digit/label traversal reports are retained rather than omitted or
identified with a free operand decoder. Native bit/address lowering is separate. -/
theorem run_metadataWork (N : ℕ) (values : List (Fin (wireCount N) × Bool)) (side : Fin 2) :
    (run N values side).metadataWork ≤
      digitCount (bitLength N)*((firstAxis (bitLength N)*secondAxis (bitLength N)+1)*
        (2*wireCount N+6*values.length+9)+3)+
      10*(wireCount N+digitCount (bitLength N)+radixBits (bitLength N)+1)^2 := by
  have h := Finset.sum_le_sum (fun (i : Fin (digitCount (bitLength N))) (_ : i∈Finset.univ) =>
    digit_work N values side i.val)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at h
  unfold run
  simp only [List.map_map,Function.comp_def,List.length_map,List.length_range,List.length_replicate]
  have hs : ((List.range (digitCount (bitLength N))).map
      (fun i => (digit N values side (edgeEnumeration N) i).metadataWork)).sum ≤
      digitCount (bitLength N)*((firstAxis (bitLength N)*secondAxis (bitLength N)+1)*
        (2*wireCount N+6*values.length+9)+3) := by
    rw [←List.sum_toFinset _ (List.nodup_range (n:=_))]
    simpa only [List.toFinset_range,Finset.sum_range] using h
  omega

end RiemannGaussian.SemiprimeD1PublicOperandBits
