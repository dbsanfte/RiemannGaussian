/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildVertexChoiceOriginal
/-! # Semantic stopped-word bounds for the two actual child constructors
Only retained templates, scope/count, context caches and acquired table/record
bytes occur below. No bound on a previous elapsed source clock is used.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildVertexEndpointBanks
open SemiprimeD1StackChildVertexChoice SemiprimeD1StackChildVertexChoiceSpec
open SemiprimeD1TensorTapeCodec (tape vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace V
export SemiprimeD1StackVectorTable (Stack data aux)
end V
/-- Replacing one real word costs only its own bytes in a semantic cell cap. -/
theorem update_word_le {K : Type} [DecidableEq K] (base : K→List Bool) (role : K)
    (word : List Bool) (cap : ℕ) (h : ∀k,(base k).length≤cap) (k : K) :
    ((Function.update base role word) k).length≤cap+word.length := by
  by_cases he:k=role
  · subst k;rw [Function.update_self];omega
  · rw [Function.update_of_ne he]
    exact (h k).trans (Nat.le_add_right _ _)
/-- The stopped whole-table bank has only original template words, actual scope and acquired unary count. -/
theorem stable_word_le {K : Type} (original : K→List Bool) (scope : List Bool) (n cap : ℕ)
    (ho : ∀k,(original k).length≤cap) (hs : scope.length≤cap) (hn : n≤cap) (k : V.Stack K) :
    (V.data original scope n [] [] k).length≤cap := by
  rcases k with k|k
  · exact Nat.zero_le _
  · rcases k with k|k
    · exact ho k
    · rcases k with k|k
      · cases k <;> simp_all [V.data,SemiprimeD1StackStaticWordTable.store,
          SemiprimeD1StackDigitCount.data]
      · cases k <;> exact Nat.zero_le _
/-- Retained input-template words have a source-byte/VALUE cap independent of all source execution times. -/
theorem template_word_le {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ)
    (oldp newp : List Bool) (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ)
    (k : SemiprimeD1StackChildTableEntry.Stack) :
    ((SemiprimeD1StackChildLiftTableOriginal.original old extra oldp newp parent order) k).length≤
      AB.resource old extra oldp newp parent order ports := by
  exact (SemiprimeD1StackChildTableEntryStorage.initial_length old.axes (extra++old.axes)
    oldp newp parent order [] k).trans (Nat.le_add_right _ _)
/-- Complete acquired134-bank word cap uses the actual Good-table bytes, never an elapsed runtime. -/
theorem active_table_word_le {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ)
    (oldp newp : List Bool) (parent : SemiprimeD1TensorTables.Table d) (order ports : List ℕ)
    (k : SemiprimeD1StackChildLiftTable.Stack) :
    (SemiprimeD1StackChildLiftVertexOriginal.tableData old extra oldp newp parent order ports k).length≤
      AB.resource old extra oldp newp parent order ports+
        (tape (SemiprimeD1StackChildLiftVertexOriginal.vertex old extra newp parent order ports).table).length := by
  have ho:=template_word_le old extra oldp newp parent order ports
  have hs : (vectorBits (ports.map unary)).length≤AB.resource old extra oldp newp parent order ports:=Nat.le_add_left _ _
  have hn : (ports.map unary).length≤AB.resource old extra oldp newp parent order ports :=
    SemiprimeD1StackChildLiftTableResources.scope_le old extra oldp newp parent order (ports.map unary)
  have hb:=stable_word_le _ _ (ports.map unary).length _ ho hs hn
  have hh:=update_word_le _ (V.aux .output)
    (SemiprimeD1StackVectorTableExecution.outputTape
      (SemiprimeD1StackChildLiftTableOriginal.answer old extra newp parent order) (ports.map unary))
    _ hb k
  change (SemiprimeD1StackChildLiftVertexOriginal.tableData old extra oldp newp parent order ports k).length≤
    AB.resource old extra oldp newp parent order ports+
      (SemiprimeD1StackChildLiftVertexOriginal.tableData old extra oldp newp parent order ports (V.aux .output)).length at hh
  rw [SemiprimeD1StackChildLiftVertexOriginal.table_output] at hh
  exact hh
/-- The whole original singleton-record byte count consists of its actual two copied fields and four tags. -/
theorem record_length (v : SemiprimeD1LeafCounter.Vertex) :
    (SemiprimeD1StackVertexProduct.records [v]).length=
      2*(SemiprimeD1StackVertexReadExecution.portTape v.ports).length+2*(tape v.table).length+4 := by
  simp only [SemiprimeD1StackVertexProduct.records,List.length_cons,
    SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  omega
/-- Every physically acquired context word is either an original header or an acquired rank/precision marker. -/
theorem context_word_le (axes : List ℕ) (precision : List Bool) (k : SemiprimeD1StackJetContext.Stack) :
    (SemiprimeD1StackJetContextCorrectness.finalData axes precision k).length≤UB.resource axes precision := by
  have ha : (vectorBits (axes.map unary)).length≤UB.resource axes precision:=by
    unfold UB.resource SemiprimeD1StackJetContextBounds.resource;omega
  have hb : precision.length≤UB.resource axes precision:=by
    unfold UB.resource SemiprimeD1StackJetContextBounds.resource;omega
  have hr : axes.prod≤UB.resource axes precision:=by
    unfold UB.resource SemiprimeD1StackJetContextBounds.resource;omega
  have hp : SemiprimeBitArithmetic.bitValue precision≤UB.resource axes precision:=by
    unfold UB.resource SemiprimeD1StackJetContextBounds.resource;omega
  rcases k with k|k
  · cases k <;> simp_all [SemiprimeD1StackJetContextCorrectness.finalData,
      SemiprimeD1StackJetContext.bank,SemiprimeD1StackJetContextExecution.ready,SemiprimeD1StackJetSuffix.data,unary]
  · rcases k with k|k
    · cases k <;> simp_all [SemiprimeD1StackJetContextCorrectness.finalData,
        SemiprimeD1StackJetContext.bank,SemiprimeD1StackAdder.store,
        SemiprimeD1StackUnaryCounterExecution.markers]
    · fin_cases k <;> simp_all [SemiprimeD1StackJetContextCorrectness.finalData,
        SemiprimeD1StackJetContext.bank,SemiprimeD1StackJetContext.cached]
/-- Every raw unit-source field is an acquired marker cache, actual output, or empty work. -/
theorem unit_bank_word_le (width rank out : List Bool) (cap : ℕ)
    (hw : width.length≤cap) (hr : rank.length≤cap) (ho : out.length≤cap)
    (k : SemiprimeD1StackJetUnit.Stack) :
    (SemiprimeD1StackJetUnit.bank width rank [] [] out k).length≤cap := by
  rcases k with k|k
  · rcases k with k|k
    · cases k <;> exact Nat.zero_le _
    · cases k <;> first | exact hw | exact Nat.zero_le _
  · cases k <;> first | exact hr | exact ho | exact Nat.zero_le _
/-- Actual unit record adds exactly two copied table bytes per source bit and six literal tags. -/
theorem unit_record_length (axes : List ℕ) (precision : List Bool) :
    (SemiprimeD1StackChildUnitVertexFrames.recordWord axes precision).length=
      2*(SemiprimeD1StackChildUnitVertexFrames.tableWord axes precision).length+6 := by
  simp only [SemiprimeD1StackChildUnitVertexFrames.recordWord,List.length_cons,
    SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
/-- All stopped pre-framing unit/context words have a direct semantic bound. -/
theorem unit_ready_word_le (axes : List ℕ) (precision : List Bool) (k : U.Stack) :
    (SemiprimeD1StackChildUnitVertexFrames.ready axes precision k).length≤
      UB.resource axes precision+(SemiprimeD1StackChildUnitVertexFrames.tableWord axes precision).length := by
  let cap:=UB.resource axes precision+(SemiprimeD1StackChildUnitVertexFrames.tableWord axes precision).length
  have hw : (SemiprimeD1StackChildUnitVertexCalls.width axes precision).length≤cap := by
    rw [SemiprimeD1StackChildUnitVertexCalls.width_length]
    exact (SemiprimeD1StackChildUnitVertexBounds.precision_le axes precision).trans (Nat.le_add_right _ _)
  have hr : (SemiprimeD1StackChildUnitVertexCalls.rank axes precision).length≤cap := by
    rw [SemiprimeD1StackChildUnitVertexCalls.rank_length]
    exact (SemiprimeD1StackChildUnitVertexBounds.rank_le axes precision).trans (Nat.le_add_right _ _)
  have ho : (vectorBits (SemiprimeD1JetAffineCoefficient.one (SemiprimeD1StackChildUnitVertexCalls.ctx axes precision)).words).length≤cap := by
    change (vectorBits (SemiprimeD1JetAffineCoefficient.one (SemiprimeD1StackChildUnitVertexCalls.ctx axes precision)).words).length≤
      UB.resource axes precision+(false::vectorBits (SemiprimeD1JetAffineCoefficient.one
        (SemiprimeD1StackChildUnitVertexCalls.ctx axes precision)).words).length
    simp only [List.length_cons]
    omega
  rcases k with k|k
  · exact (context_word_le axes precision k).trans (Nat.le_add_right _ _)
  · rcases k with k|k
    · change (if k=SemiprimeD1StackJetUnit.widthCache ∨ k=SemiprimeD1StackJetUnit.rankCache then [] else _).length≤cap
      split
      · exact Nat.zero_le _
      · exact unit_bank_word_le _ _ _ cap hw hr ho k
    · cases k <;> exact Nat.zero_le _
/-- Entire stopped32-bank words are bounded by header/rank/precision values and exact acquired unit bytes alone. -/
theorem unit_word_le (axes : List ℕ) (precision : List Bool) (k : U.Stack) :
    ((UO.done axes precision).data k).length≤
      UB.resource axes precision+4*(SemiprimeD1StackChildUnitVertexFrames.tableWord axes precision).length+6 := by
  have h0:=unit_ready_word_le axes precision
  have h1:=update_word_le _ (SemiprimeD1StackChildUnitVertex.unit SemiprimeD1StackJetUnit.output)
    (SemiprimeD1StackChildUnitVertexFrames.tableWord axes precision) _ h0
  have h2:=update_word_le _ (U.aux .record)
    (SemiprimeD1StackChildUnitVertexFrames.recordWord axes precision) _ h1 k
  change ((UO.done axes precision).data k).length≤
    (UB.resource axes precision+(SemiprimeD1StackChildUnitVertexFrames.tableWord axes precision).length)+
      (SemiprimeD1StackChildUnitVertexFrames.tableWord axes precision).length+
      (SemiprimeD1StackChildUnitVertexFrames.recordWord axes precision).length at h2
  rw [unit_record_length] at h2
  omega
end RiemannGaussian.SemiprimeD1StackChildVertexEndpointBanks
