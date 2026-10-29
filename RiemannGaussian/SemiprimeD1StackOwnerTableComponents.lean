/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerTable
import RiemannGaussian.SemiprimeD1StackProcedureInclusion
/-! # Actual counting, complete prefix scan and literal owner-table source calls -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackOwnerTableComponents
open SemiprimeD1StackOwnerTable SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1OwnerPrefixBits (records scan)

/-- ONE real scope scan physically acquires degree from every scope-ID record. -/
theorem count_call (key prefixBytes : List Bool) (scopeWords : List (List Bool)) :
    Runs program (SemiprimeD1StackDigitCountExecution.totalTime scopeWords+1) .start
      (data key prefixBytes (vectorBits scopeWords) [] [] []) .count0
      (data key prefixBytes (vectorBits scopeWords) (List.replicate scopeWords.length true) [] []) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program countStack Label.count count_injective
    D.program (.inl .main) (fun _=>rfl) .start .count0 rfl _
    (SemiprimeD1StackDigitCountExecution.initial (vectorBits scopeWords))
    (SemiprimeD1StackDigitCountExecution.done scopeWords)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackDigitCountExecution.acquire_run scopeWords
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · exact (hk k rfl).elim
        · cases k;rfl
/-- The full actual prefix scanner computes both flags from original records.
No allowed-pair result is supplied to the count/table program. -/
theorem prefix_call (degree : Fin 3) (key : List Bool) (rows : List (List Bool×Bool))
    (tail scopeBytes : List Bool) :
    Runs program (SemiprimeD1StackOwnerPrefixExecution.loopTime key rows+2) (.scan degree)
      (data key (records rows tail) scopeBytes [] [] []) (.low degree)
      (data key tail scopeBytes [] [(scan key rows true true).1,(scan key rows true true).2] []) := by
  apply SemiprimeD1StackProcedureInclusion.included_call program Sum.inl Label.prefixScan Sum.inl_injective
    P.program (.loop true true) (fun _=>rfl) (.scan degree) (.low degree) rfl _
    (SemiprimeD1StackOwnerPrefix.initial key (records rows tail))
    (SemiprimeD1StackOwnerPrefix.done key rows tail)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackOwnerPrefixExecution.source_run key rows tail
  · constructor
    · intro k;rfl
    · intro k hk;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rcases k with k|k
        · cases k <;> rfl
        · cases k;rfl
/-- Empty-data finite palette code writes every literal byte through real pushes. -/
theorem palette_call (degree : Fin 3) (low high : Bool) (key tail scopeBytes : List Bool) :
    Runs program ((SemiprimeD1OwnerTablePalette.bytes degree low high).length+2) (.emit degree low high)
      (data key tail scopeBytes [] [] []) .done
      (data key tail scopeBytes [] [] (SemiprimeD1OwnerTablePalette.bytes degree low high)) := by
  apply included_call program (fun _ : Unit=>output) Label.palette
    (by intro a b h;cases a;cases b;rfl) T.code ((degree,low,high),0)
    (fun _=>rfl) (.emit degree low high) .done rfl _
    (SemiprimeD1StackOwnerPaletteSource.initial (degree,low,high))
    (SemiprimeD1StackOwnerPaletteSource.done (degree,low,high))
  · rfl
  · rfl
  · exact SemiprimeD1StackOwnerPaletteSource.source_run (degree,low,high)
  · constructor
    · intro k;cases k;rfl
    · intro k hk;rfl
  · constructor
    · intro k;cases k;rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · cases k <;> rfl
        · cases k;exact (hk () rfl).elim
end RiemannGaussian.SemiprimeD1StackOwnerTableComponents
