/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanFactorCataloguePrimitives
/-! # Actual final row reversal and canonical binary-only machine initialization -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueFinish
open SemiprimeD1StackBooleanFactorCatalogue SemiprimeD1StackBooleanFactorCatalogueView
open SemiprimeD1StackProcedureFragments (Runs included_call)
/-- The one real final reversal consumes all physical history bytes and prepends
them to the already physically acquired false output terminator. -/
theorem reverse_call (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool)
    (hist out : List Bool) :
    Runs program (2*hist.length+3) (.local .reverse) (data fibre catalogue (fun _=>[]) hist out)
      (.local .done) (data fibre catalogue (fun _=>[]) [] (hist.reverse++out)) := by
  apply included_call program loggerStack Label.logger logger_injective Log.code .reverse (fun _=>rfl)
    (.local .reverse) (.local .done) rfl (2*hist.length+2)
    (⟨some .reverse,none,SemiprimeD1StackVertexRecordStream.data [] [] hist out⟩:
      SemiprimeD1StackBytecode.State Log.Stack Log.Label)
    (⟨none,none,SemiprimeD1StackVertexRecordStream.data [] [] [] (hist.reverse++out)⟩:
      SemiprimeD1StackBytecode.State Log.Stack Log.Label)
  · rfl
  · rfl
  · exact SemiprimeD1StackVertexRecordStream.reverse_run hist [] [] out none
  · constructor
    · intro k;exact data_logger _ _ _ _ _ k
    · intro k _;rfl
  · constructor
    · intro k;exact data_logger _ _ _ _ _ k
    · intro k hk
      rcases k with k|k|k|k
      · rfl
      · rfl
      · rcases k with k|k|k
        · rcases k with k|k|k
          · cases k;rfl
          · cases k <;> rfl
          · cases k with
            | ports | table=>rfl
            | history=>exact (hk .history rfl).elim
            | output=>exact (hk .output rfl).elim
        · rfl
        · cases k <;> rfl
      · rfl
/-- Literal outer halt after the real full-history reversal. -/
def done (fibre : F.Stack→List Bool) (catalogue : V.Stack→List Bool) (out : List Bool) : C.State Stack Label :=
  ⟨none,none,none,data fibre catalogue (fun _=>[]) [] out,[]⟩
/-- Actual source initialization has only one possibly nonempty role: binary N. -/
theorem input_eq (bits : List Bool) (k : Stack) :
    input bits k=(if k=originalInput then bits else []) := by
  rcases k with k|k
  · rcases k with k|k|k
    · change SemiprimeD1StackFactorScopePairs.input bits k=_
      rw [SemiprimeD1StackFactorScopePairExecution.input_eq]
      simp only [originalInput,sourceStack,SemiprimeD1StackFactorScopeFibre.originalInput,
        SemiprimeD1StackFactorScopeFibre.sourceStack,Sum.inl.injEq]
    · rcases k with k|k
      · cases k <;> rfl
      · cases k <;> rfl
    · cases k;rfl
  · rfl
/-- The fixed218-role machine genuinely begins from the canonical binary input alone. -/
theorem initial_configuration (bits : List Bool) :
    Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs:initial bits=SemiprimeD1StackCalls.initial originalInput (.local .main) bits:=by
    unfold initial SemiprimeD1StackCalls.initial
    congr 1
    funext k
    exact input_eq bits k
  rw [hs]
  exact (SemiprimeD1StackCalls.initial_correct originalInput output (.local .main) program bits).symm
end RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueFinish
