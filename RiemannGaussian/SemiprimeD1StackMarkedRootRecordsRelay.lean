/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedRootRecordsIntegral
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableOriginal
/-! # Exact integer preservation of the seventeen relayed factor families
The whole ordered Boolean table is identified before any network product.
Every zero-mark original row is literally the same compact zero/one word.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRelay
open SemiprimeD1TensorTables SemiprimeBitArithmetic
namespace Old
export SemiprimeD1BooleanRootTablesOriginal (reference)
end Old
namespace New
export SemiprimeD1StackMarkedPublicInputTableOriginal (reference wordOf reference_entry)
end New
/-- Generic original build entry, before concrete graph or vertex instantiation. -/
theorem original_entry (N : Nat) (hN : 0 < N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (input : Fin (SemiprimeMacroGraph.subdividedArity v) → Bool) :
    valueAt (Old.reference N hN v) input=
      [if SemiprimeMacroGraphSemantics.subdividedTable (SemiprimePublicFactorCount.publicConfig N hN) v input
       then [true] else []] := by
  unfold Old.reference
  rw [SemiprimeD1ZeroBoundaryTables.build_entry]
  have hget : (fun j : Fin (SemiprimeMacroGraph.subdividedArity v) =>
      ((List.ofFn input).toArray[j.val]?).getD false)=input := by
    funext j
    simp only [List.getElem?_toArray,List.getElem?_ofFn,j.isLt,dite_true,Option.getD_some]
  change [if (SemiprimeSubdividedEntry.publicSubdividedEntry N hN v
    (fun j => ((List.ofFn input).toArray[j.val]?).getD false)).accepted then [true] else []]=_
  have hfirst := congrArg (fun f => [if (SemiprimeSubdividedEntry.publicSubdividedEntry N hN v f).accepted
    then [true] else []]) hget
  exact hfirst.trans (congrArg (fun b : Bool => [if b then [true] else []])
    (SemiprimeSubdividedEntry.publicSubdividedEntry_correct N hN v input))
/-- Each original coefficient is exactly zero or one in the naturals. -/
theorem original_integer (N : Nat) (hN : 0 < N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (input : Fin (SemiprimeMacroGraph.subdividedArity v) → Bool) :
    (valueAt (Old.reference N hN v) input).map bitValue=
      [if SemiprimeMacroGraphSemantics.subdividedTable (SemiprimePublicFactorCount.publicConfig N hN) v input
       then 1 else 0] := by
  rw [original_entry]
  cases SemiprimeMacroGraphSemantics.subdividedTable (SemiprimePublicFactorCount.publicConfig N hN) v input <;> rfl
/-- Both literal Boolean words are already compact at precision two. -/
theorem original_good (N : Nat) (hN : 0 < N) (v : SemiprimePublicAcquiredExecution.PublicVertex N) :
    Good ⟨[],2⟩ (Old.reference N hN v) := by
  unfold Old.reference
  apply build_good
  intro raw _
  change GoodWords ⟨[],2⟩ [if _ then [true] else []]
  split <;> simp [GoodWords,SemiprimeD1JetAxes.Context.rank,SemiprimeSourceCompactBits.Compact]
/-- Canonical zero and one bytes agree with the marked table's integer codec. -/
theorem wordOf_bool (b : Bool) : New.wordOf (if b then 1 else 0)=if b then [true] else [] := by
  apply SemiprimeSourceCompactWordIds.compact_value_injective
  · exact SemiprimeSourceHistogramPortKeys.encodeKey_compact _
  · cases b <;> simp [SemiprimeSourceCompactBits.Compact]
  · have h := SemiprimeSourceHistogramPortKeys.encodeKey_value (if b then 1 else 0)
    exact h.trans (by cases b <;> rfl)
/-- Relaying an unmarked factor preserves the ENTIRE exact ordered marked table.
The zero-mark premise is a mathematical fact discharged by its constructor. -/
theorem relay_table (N : Nat) (hN : 0 < N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (hm : ∀ input, SemiprimeD1PackedMomentDigits.localMark (SemiprimePublicFactorCount.publicConfig N hN) v input=0) :
    Old.reference N hN v=New.reference N hN v := by
  apply SemiprimeD1ZeroBoundaryTables.table_ext
  intro input
  rw [original_entry,New.reference_entry]
  unfold SemiprimeD1PackedMomentPrecision.coefficient
  rw [hm input]
  simp only [Nat.mul_zero,Nat.add_zero]
  exact congrArg (fun w => [w]) (wordOf_bool _).symm
/-- The byte-identical relay is intrinsically Good at every larger scalar precision. -/
theorem relay_good (N : Nat) (hN : 0 < N) (v : SemiprimePublicAcquiredExecution.PublicVertex N)
    (p : Nat) (hp : 2 ≤ p) : Good ⟨[],p⟩ (Old.reference N hN v) :=
  SemiprimeD1StackMarkedRootRecordsIntegral.good_mono [] 2 p hp _ (original_good N hN v)
end RiemannGaussian.SemiprimeD1StackMarkedRootRecordsRelay
