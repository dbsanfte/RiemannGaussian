/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleTableExecution
import RiemannGaussian.SemiprimeD1ZeroBoundaryTables
/-! # Entire original scale-family tensor and integer entries
Scope routing/acquisition remains explicit caller work. Once its acquired
scope has the original arity, the SAME fixed332-role compiler produces the
ENTIRE old tensor in its unchanged original local-port order.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicScaleTableOriginal
open SemiprimeD1StackPublicScaleTable SemiprimeD1StackPublicScaleTableTrace
open SemiprimeD1StackPublicScaleTableExecution
open SemiprimeMacroParameters SemiprimeBitArithmetic
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1StackPublicScaleFinite (selector)
namespace T
export SemiprimeD1StackStaticTableSpec (leafWords tree tree_entry)
end T
/-- Every original finite assignment has its actual original checker0/1
coefficient word, for ALL original transform directions and coordinate pairs. -/
theorem leaf_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : SemiprimeMacroGraph.Transform)
    (j : Fin (firstAxis (bitLength (bitValue bits)))) (k : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (SemiprimeMacroGraph.arity (.scale tr j k : SemiprimeMacroGraph.Vertex
      (firstAxis (bitLength (bitValue bits))) (secondAxis (bitLength (bitValue bits)))
      (digitCount (bitLength (bitValue bits)))))→Bool) :
    T.leafWords (answer bits (unary j.val) (unary k.val) (selector tr)) (List.ofFn input)=
      [if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.scale tr j k) input).accepted
        then [true] else []] := by
  have he:=SemiprimeD1StackPublicScaleFinite.public_original bits hc hN tr j k input
  have hv:=SemiprimeD1StackPublicScaleOriginal.verdict_value bits (List.ofFn input)
    (unary j.val) (unary k.val) (selector tr) j.val k.val
  have ha:answer bits (unary j.val) (unary k.val) (selector tr) (List.ofFn input)=
      (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.scale tr j k) input).accepted := by
    simpa only [answer,unary,List.length_replicate,List.singleton_inj] using hv.symm.trans he
  unfold T.leafWords
  rw [ha]
/-- ENTIRE old original scale tensor, no permutation and no subset of assignments.
The arity equality is a proof about the physically acquired caller scope only. -/
theorem table_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : SemiprimeMacroGraph.Transform)
    (j : Fin (firstAxis (bitLength (bitValue bits)))) (k : Fin (secondAxis (bitLength (bitValue bits))))
    (words : List (List Bool))
    (hlen : words.length=SemiprimeMacroGraph.subdividedArity
      (.inl (.scale tr j k):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits))) :
    table bits (unary j.val) (unary k.val) (selector tr) words=SemiprimeD1TensorTapeCodec.tape
      (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl (.scale tr j k))) := by
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
  change T.leafWords (answer bits (unary j.val) (unary k.val) (selector tr)) (List.ofFn input)=
    [if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.scale tr j k)
      (fun j=>((List.ofFn input).toArray[j.val]?).getD false)).accepted then [true] else []]
  have he:=congrArg (fun f=>[if (SemiprimeMacroEntryBitCheck.publicBitEntry
    (bitValue bits) hN (.scale tr j k) f).accepted then [true] else []]) hget
  exact (leaf_original bits hc hN tr j k input).trans he.symm
/-- The ACTUAL acquired output role, rather than an advised specification tape,
is exactly the frozen complete original scale table. -/
theorem output_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<bitValue bits)
    (tr : SemiprimeMacroGraph.Transform)
    (j : Fin (firstAxis (bitLength (bitValue bits)))) (k : Fin (secondAxis (bitLength (bitValue bits))))
    (words : List (List Bool))
    (hlen : words.length=SemiprimeMacroGraph.subdividedArity
      (.inl (.scale tr j k):SemiprimePublicAcquiredExecution.PublicVertex (bitValue bits))) :
    (done bits (unary j.val) (unary k.val) (selector tr) words).data (SemiprimeD1StackStaticTable.aux .output)=
      SemiprimeD1TensorTapeCodec.tape
        (SemiprimeD1BooleanRootTablesOriginal.reference (bitValue bits) hN (.inl (.scale tr j k))) :=
  (output_table bits (unary j.val) (unary k.val) (selector tr) words).trans (table_original bits hc hN tr j k words hlen)
/-- EACH individual entry's actual integral coefficient is the original0/1
indicator BEFORE any network product, contraction or precision reduction. -/
theorem literal_original_coefficient (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits)
    (tr : SemiprimeMacroGraph.Transform)
    (j : Fin (firstAxis (bitLength (bitValue bits)))) (k : Fin (secondAxis (bitLength (bitValue bits))))
    (input : Fin (SemiprimeMacroGraph.arity (.scale tr j k : SemiprimeMacroGraph.Vertex
      (firstAxis (bitLength (bitValue bits))) (secondAxis (bitLength (bitValue bits)))
      (digitCount (bitLength (bitValue bits)))))→Bool) :
    SemiprimeD1JetAlgebra.coefficient (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1JetBoxIndex.exponent [] 0)
      (SemiprimeD1JetBoxIndex.exponent_inBox [] 0 (by simp) (by decide))
      (SemiprimeD1JetLiteralLift.literal [] (T.leafWords (answer bits (unary j.val) (unary k.val) (selector tr)) (List.ofFn input)))=
      if (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.scale tr j k) input).accepted
        then 1 else 0 := by
  rw [SemiprimeD1JetLiteralLift.literal_coefficient [] _ (by simp) 0 (by decide),
    leaf_original bits hc hN tr j k input]
  cases (SemiprimeMacroEntryBitCheck.publicBitEntry (bitValue bits) hN (.scale tr j k) input).accepted <;>
    simp [bitValue,bitNat]
/-- Arbitrary precision reduces this SAME actual individual integral entry.
No upward modular map or lifted aggregate replaces any local coefficient. -/
theorem literal_entry_reduce (bits stride frequency raw : List Bool) (inverse : Bool) (p : Nat) :
    SemiprimeD1JetScalarMap.scalarMap (SemiprimeD1JetBoxIndex.dims [])
      (SemiprimeD1DyadicInteger.reduction p)
      (SemiprimeD1JetLiteralLift.literal [] (T.leafWords (answer bits stride frequency inverse) raw))=
      SemiprimeD1JetInterpretation.interpret ⟨[],p⟩ (T.leafWords (answer bits stride frequency inverse) raw) :=
  SemiprimeD1JetLiteralLift.literal_reduce [] p _
end RiemannGaussian.SemiprimeD1StackPublicScaleTableOriginal
