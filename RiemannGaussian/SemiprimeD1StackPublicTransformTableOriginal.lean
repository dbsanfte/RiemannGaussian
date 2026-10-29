/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformTableExecution
import RiemannGaussian.SemiprimeD1ZeroBoundaryTables
/-! # Entire original transform-family tensor and integer entries
Scope routing/acquisition remains explicit caller work. Once its acquired
scope has the original arity, the SAME fixed420-role compiler produces the
ENTIRE old tensor in its unchanged original local-port order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformTableOriginal
open SemiprimeD1StackPublicTransformTable SemiprimeD1StackPublicTransformTableTrace
open SemiprimeD1StackPublicTransformTableExecution
open SemiprimeMacroParameters SemiprimeBitArithmetic
open SemiprimeD1StackPublicScaleFinite (selector)
namespace T
export SemiprimeD1StackStaticTableSpec (leafWords tree tree_entry)
end T
/-- Every original finite assignment has its actual original checker0/1
coefficient word, for ALL original transform directions and coordinate pairs. -/
theorem leaf_first_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : SemiprimeMacroGraph.Transform)
    (j : Fin (firstAxis (bitLength (bitValue bits))))
    (input : Fin (SemiprimeMacroGraph.arity (.first tr j : SemiprimeMacroGraph.Vertex
      (firstAxis (bitLength (bitValue bits))) (secondAxis (bitLength (bitValue bits)))
      (digitCount (bitLength (bitValue bits)))))→Bool) :
    T.leafWords (answer bits false (selector tr)) (List.ofFn input)=
      [if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.first tr j) input).accepted
        then [true] else []] := by
  unfold T.leafWords answer
  rw [SemiprimeD1StackPublicTransformPublic.first_original bits hc hN tr j input]
/-- ENTIRE old original first-transform tensor, no permutation and no subset of assignments.
The arity equality is a proof about the physically acquired caller scope only. -/
theorem table_first_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : SemiprimeMacroGraph.Transform)
    (j : Fin (firstAxis (bitLength (bitValue bits))))
    (words : List (List Bool))
    (hlen : words.length=SemiprimeMacroGraph.subdividedArity
      (.inl (.first tr j):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits))) :
    table bits false (selector tr) words=SemiprimeD1TensorTapeCodec.tape
      (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl (.first tr j))) := by
  unfold table SemiprimeD1StackStaticTableExecution.outputTape
  rw [hlen]
  apply congrArg SemiprimeD1TensorTapeCodec.tape
  apply SemiprimeD1ZeroBoundaryTables.table_ext
  intro input
  rw [T.tree_entry,List.nil_append]
  dsimp only [SemiprimeD1BooleanRootTablesOriginal.reference]
  rw [SemiprimeD1ZeroBoundaryTables.build_entry]
  have hget:(fun j=>((List.ofFn input).toArray[j.val]?).getD false)=input:=by
    funext j
    simp only [List.getElem?_toArray,List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some]
  change T.leafWords (answer bits false (selector tr)) (List.ofFn input)=
    [if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.first tr j)
      (fun j=>((List.ofFn input).toArray[j.val]?).getD false)).accepted then [true] else []]
  have he:=congrArg (fun f=>[if (SemiprimeMacroEntryBitCheck.publicBitEntry
    (bitValue bits) hN (.first tr j) f).accepted then [true] else []]) hget
  exact (leaf_first_original bits hc hN tr j input).trans he.symm
/-- The ACTUAL acquired output role, rather than an advised specification tape,
is exactly the frozen complete original first-transform table. -/
theorem output_first_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : SemiprimeMacroGraph.Transform)
    (j : Fin (firstAxis (bitLength (bitValue bits))))
    (words : List (List Bool))
    (hlen : words.length=SemiprimeMacroGraph.subdividedArity
      (.inl (.first tr j):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits))) :
    (done bits false (selector tr) words).data (SemiprimeD1StackStaticTable.aux .output)=
      SemiprimeD1TensorTapeCodec.tape
        (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl (.first tr j))) :=
  (output_table bits false (selector tr) words).trans (table_first_original bits hc hN tr j words hlen)
/-- EACH individual entry's actual integral coefficient is the original0/1
indicator BEFORE any network product, contraction or precision reduction. -/
theorem literal_first_original_coefficient (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits)
    (tr : SemiprimeMacroGraph.Transform)
    (j : Fin (firstAxis (bitLength (bitValue bits))))
    (input : Fin (SemiprimeMacroGraph.arity (.first tr j : SemiprimeMacroGraph.Vertex
      (firstAxis (bitLength (bitValue bits))) (secondAxis (bitLength (bitValue bits)))
      (digitCount (bitLength (bitValue bits)))))→Bool) :
    SemiprimeD1JetAlgebra.coefficient (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1JetBoxIndex.exponent [] 0)
      (SemiprimeD1JetBoxIndex.exponent_inBox [] 0 (by simp) (by decide))
      (SemiprimeD1JetLiteralLift.literal [] (T.leafWords (answer bits false (selector tr)) (List.ofFn input)))=
      if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.first tr j) input).accepted
        then 1 else 0 := by
  rw [SemiprimeD1JetLiteralLift.literal_coefficient [] _ (by simp) 0 (by decide),
    leaf_first_original bits hc hN tr j input]
  cases (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.first tr j) input).accepted <;>
    simp [bitValue,bitNat]
/-- Every original finite assignment has its actual original checker0/1
coefficient word, for ALL original transform directions and coordinate pairs. -/
theorem leaf_second_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : SemiprimeMacroGraph.Transform)
    (j : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (SemiprimeMacroGraph.arity (.second tr j : SemiprimeMacroGraph.Vertex
      (firstAxis (bitLength (bitValue bits))) (secondAxis (bitLength (bitValue bits)))
      (digitCount (bitLength (bitValue bits)))))→Bool) :
    T.leafWords (answer bits true (selector tr)) (List.ofFn input)=
      [if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.second tr j) input).accepted
        then [true] else []] := by
  unfold T.leafWords answer
  rw [SemiprimeD1StackPublicTransformPublic.second_original bits hc hN tr j input]
/-- ENTIRE old original second-transform tensor, no permutation and no subset of assignments.
The arity equality is a proof about the physically acquired caller scope only. -/
theorem table_second_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : SemiprimeMacroGraph.Transform)
    (j : Fin (secondAxis (bitLength (bitValue bits))))
    (words : List (List Bool))
    (hlen : words.length=SemiprimeMacroGraph.subdividedArity
      (.inl (.second tr j):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits))) :
    table bits true (selector tr) words=SemiprimeD1TensorTapeCodec.tape
      (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl (.second tr j))) := by
  unfold table SemiprimeD1StackStaticTableExecution.outputTape
  rw [hlen]
  apply congrArg SemiprimeD1TensorTapeCodec.tape
  apply SemiprimeD1ZeroBoundaryTables.table_ext
  intro input
  rw [T.tree_entry,List.nil_append]
  dsimp only [SemiprimeD1BooleanRootTablesOriginal.reference]
  rw [SemiprimeD1ZeroBoundaryTables.build_entry]
  have hget:(fun j=>((List.ofFn input).toArray[j.val]?).getD false)=input:=by
    funext j
    simp only [List.getElem?_toArray,List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some]
  change T.leafWords (answer bits true (selector tr)) (List.ofFn input)=
    [if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.second tr j)
      (fun j=>((List.ofFn input).toArray[j.val]?).getD false)).accepted then [true] else []]
  have he:=congrArg (fun f=>[if (SemiprimeMacroEntryBitCheck.publicBitEntry
    (bitValue bits) hN (.second tr j) f).accepted then [true] else []]) hget
  exact (leaf_second_original bits hc hN tr j input).trans he.symm
/-- The ACTUAL acquired output role, rather than an advised specification tape,
is exactly the frozen complete original second-transform table. -/
theorem output_second_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : SemiprimeMacroGraph.Transform)
    (j : Fin (secondAxis (bitLength (bitValue bits))))
    (words : List (List Bool))
    (hlen : words.length=SemiprimeMacroGraph.subdividedArity
      (.inl (.second tr j):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits))) :
    (done bits true (selector tr) words).data (SemiprimeD1StackStaticTable.aux .output)=
      SemiprimeD1TensorTapeCodec.tape
        (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl (.second tr j))) :=
  (output_table bits true (selector tr) words).trans (table_second_original bits hc hN tr j words hlen)
/-- EACH individual entry's actual integral coefficient is the original0/1
indicator BEFORE any network product, contraction or precision reduction. -/
theorem literal_second_original_coefficient (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits)
    (tr : SemiprimeMacroGraph.Transform)
    (j : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (SemiprimeMacroGraph.arity (.second tr j : SemiprimeMacroGraph.Vertex
      (firstAxis (bitLength (bitValue bits))) (secondAxis (bitLength (bitValue bits)))
      (digitCount (bitLength (bitValue bits)))))→Bool) :
    SemiprimeD1JetAlgebra.coefficient (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1JetBoxIndex.exponent [] 0)
      (SemiprimeD1JetBoxIndex.exponent_inBox [] 0 (by simp) (by decide))
      (SemiprimeD1JetLiteralLift.literal [] (T.leafWords (answer bits true (selector tr)) (List.ofFn input)))=
      if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.second tr j) input).accepted
        then 1 else 0 := by
  rw [SemiprimeD1JetLiteralLift.literal_coefficient [] _ (by simp) 0 (by decide),
    leaf_second_original bits hc hN tr j input]
  cases (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.second tr j) input).accepted <;>
    simp [bitValue,bitNat]
/-- Arbitrary precision reduces this SAME actual individual integral entry. -/
theorem literal_entry_reduce (bits raw : List Bool) (second inverse : Bool) (p : Nat) :
    SemiprimeD1JetScalarMap.scalarMap (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1DyadicInteger.reduction p)
      (SemiprimeD1JetLiteralLift.literal [] (T.leafWords (answer bits second inverse) raw))=
      SemiprimeD1JetInterpretation.interpret ⟨[],p⟩ (T.leafWords (answer bits second inverse) raw) :=
  SemiprimeD1JetLiteralLift.literal_reduce [] p _
end RiemannGaussian.SemiprimeD1StackPublicTransformTableOriginal
