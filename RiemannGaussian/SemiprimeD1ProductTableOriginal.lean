/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableSpec
import RiemannGaussian.SemiprimeD1ZeroBoundaryTables
/-! # Entire acquired product table is the original product tensor
All definitions referenced here are proof-side specifications of the closed
original-N source. Every finite assignment retains its original port order.
Individual coefficients are literal integers before any network product, and
the same acquired words reduce correctly at every precision.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1ProductTableOriginal
open SemiprimeD1TensorTables SemiprimeBitArithmetic SemiprimeMacroParameters
namespace S
export SemiprimeD1StackProductTableSpec (arity answer leafWords tree outputTape)
end S
/-- Each false-first leaf uses exactly the original prefix followed by its
remaining ordered finite assignment. No assignment is omitted or permuted. -/
theorem tree_entry (bits front : List Bool) (n : Nat) (input : Fin n→Bool) :
    valueAt (S.tree bits front n) input=S.leafWords bits (front++List.ofFn input) := by
  induction n generalizing front with
  | zero => simp only [S.tree,valueAt,List.ofFn_zero,List.append_nil]
  | succ n ih =>
    cases h:input 0
    · simp only [S.tree,valueAt,h,Bool.false_eq_true,ite_false]
      simpa only [List.ofFn_succ,h,List.append_assoc,List.singleton_append] using
        ih (front++[false]) (fun j=>input j.succ)
    · simp only [S.tree,valueAt,h,ite_true]
      simpa only [List.ofFn_succ,h,List.append_assoc,List.singleton_append] using
        ih (front++[true]) (fun j=>input j.succ)
/-- The physically acquired three-word depth is exactly every original product
vertex's arity; the product index contributes no table permutation. -/
theorem original_arity (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits)))) :
    S.arity bits=SemiprimeMacroGraph.subdividedArity (.inl (SemiprimeMacroGraph.Vertex.product
      (digits:=digitCount (bitLength (bitValue bits))) k)) := by
  change 3*(SemiprimeD1StackPublicProductExecution.cached bits).length=
    SemiprimeMacroGraph.arity (.product (digits:=digitCount (bitLength (bitValue bits))) k)
  rw [SemiprimeD1StackPublicProductFinite.product_arity,
    SemiprimeD1StackPublicProductFinite.public_width bits hc]
/-- Every original assignment gives the exact original accepted zero/one word
vector, with canonical root coefficients rather than a modular equality only. -/
theorem leaf_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (SemiprimeMacroGraph.arity (.product
      (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    S.leafWords bits (List.ofFn input)=
      [if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.product k) input).accepted
        then [true] else []] := by
  unfold S.leafWords S.answer
  rw [SemiprimeD1StackPublicProductFinite.public_original bits hc hN k input]
/-- ENTIRE actual output tape equals the exact old checker-built tensor, for
ALL original product indices and ALL canonical positive original inputs. -/
theorem output_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits)))) :
    S.outputTape bits=SemiprimeD1TensorTapeCodec.tape
      (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl (.product k))) := by
  have ha:=original_arity bits hc k
  unfold S.outputTape
  rw [ha]
  apply congrArg SemiprimeD1TensorTapeCodec.tape
  apply SemiprimeD1ZeroBoundaryTables.table_ext
  intro input
  rw [tree_entry,List.nil_append]
  dsimp only [SemiprimeD1BooleanRootTablesOriginal.reference]
  rw [SemiprimeD1ZeroBoundaryTables.build_entry]
  have hget : (fun j=>((List.ofFn input).toArray[j.val]?).getD false)=input := by
    funext j
    simp only [List.getElem?_toArray,List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some]
  change S.leafWords bits (List.ofFn input)=
    [if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.product k)
      (fun j=>((List.ofFn input).toArray[j.val]?).getD false)).accepted then [true] else []]
  have he:=congrArg (fun f=>
    [if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.product k) f).accepted
      then [true] else []]) hget
  exact (leaf_original bits hc hN k input).trans he.symm
/-- The actual integral coefficient of EACH acquired product entry is zero or
one before any network multiplication, contraction or precision reduction. -/
theorem literal_entry_coefficient (bits front : List Bool) (n : Nat) (input : Fin n→Bool) :
    SemiprimeD1JetAlgebra.coefficient (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1JetBoxIndex.exponent [] 0)
      (SemiprimeD1JetBoxIndex.exponent_inBox [] 0 (by simp) (by decide))
      (SemiprimeD1JetLiteralLift.literal [] (valueAt (S.tree bits front n) input))=
      if S.answer bits (front++List.ofFn input) then 1 else 0 := by
  rw [SemiprimeD1JetLiteralLift.literal_coefficient [] _ (by simp) 0 (by decide),tree_entry]
  cases h:S.answer bits (front++List.ofFn input) <;>
    simp [S.leafWords,h,bitValue,bitNat]
/-- For every original product index and local assignment, its individual
literal integer coefficient is exactly the original public checker's indicator. -/
theorem literal_original_coefficient (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits)
    (k : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (SemiprimeMacroGraph.arity (.product
      (digits:=digitCount (bitLength (bitValue bits))) k))→Bool) :
    SemiprimeD1JetAlgebra.coefficient (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1JetBoxIndex.exponent [] 0)
      (SemiprimeD1JetBoxIndex.exponent_inBox [] 0 (by simp) (by decide))
      (SemiprimeD1JetLiteralLift.literal [] (S.leafWords bits (List.ofFn input)))=
      if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.product k) input).accepted
        then 1 else 0 := by
  rw [SemiprimeD1JetLiteralLift.literal_coefficient [] _ (by simp) 0 (by decide),leaf_original bits hc hN k input]
  cases (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.product k) input).accepted <;>
    simp [bitValue,bitNat]
/-- Arbitrary precision reduces this same literal integer entry to the acquired
word interpretation; no upward reduction map or replacement table is needed. -/
theorem literal_entry_reduce (bits front : List Bool) (n p : Nat) (input : Fin n→Bool) :
    SemiprimeD1JetScalarMap.scalarMap (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1DyadicInteger.reduction p)
      (SemiprimeD1JetLiteralLift.literal [] (valueAt (S.tree bits front n) input))=
      SemiprimeD1JetInterpretation.interpret ⟨[],p⟩ (valueAt (S.tree bits front n) input) :=
  SemiprimeD1JetLiteralLift.literal_reduce [] p _
end RiemannGaussian.SemiprimeD1ProductTableOriginal
