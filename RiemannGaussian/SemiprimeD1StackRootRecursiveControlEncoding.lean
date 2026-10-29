/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootRecursiveControl

/-! # Exact acquired-data projections for the original-input root controller
All numerical functions here specify actual encoded words. None occurs as an
operand supplier or evaluator instruction in the fixed executing program.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootRecursiveControlEncoding
open SemiprimeD1StackRootRecursiveControl
open SemiprimeBitArithmetic (bitValue)
namespace GS
export SemiprimeD1StackRecursiveSchedule (initial done result runBound)
end GS
namespace AO
export SemiprimeD1StackScheduleActiveOriginal (values)
end AO
/-- Exact original scale of the actual canonical input value. -/
def scaleValue (bits:List Bool) : Nat :=
  SemiprimeD1PublicPackingReady.scale (SemiprimeMacroParameters.bitLength (bitValue bits))
/-- Exact original logarithmic parameter, never a runtime register. -/
def lambdaValue (bits:List Bool) : Nat :=SemiprimeD1StackRootScheduleOriginal.originalLambda (bitValue bits)
/-- The count physically acquired by the original scope source. -/
def edgeValue (bits:List Bool) : Nat :=SemiprimeD1StackRootScopeBankExecution.occurrenceCount bits
/-- Mathematical root-guard parameters read from the actual source output. -/
def values (bits:List Bool) : SemiprimeD1StackScheduleActive.Param→Nat :=
  AO.values (scaleValue bits) (lambdaValue bits) 0 (edgeValue bits)
/-- Exact physically acquired original root cumulative exponent word. -/
def parentExponent (bits:List Bool) : List Bool :=
  SemiprimeD1StackRecursiveScheduleOriginal.exponentWord (lambdaValue bits) 0
/-- Each fresh physical role corresponds to one actual allocated gate role. -/
def freshRole : Fresh→G.Stack
  | .left=>.inl .left | .right=>.inl .right | .limit=>.inl .limit | .valid=>.inl .valid
  | .scratch=>.inl .scratch | .output=>.inl .output | .shadow=>.inr .levels
  | .reader=>.inr .reader | .scheduleScratch=>.inr .scratch
  | .nextLevels=>.inr .nextLevels | .nextExponent=>.inr .nextExponent
/-- The eleven fresh physical role maps are exact and exhaust their tagged region. -/
theorem freshRole_mapped (k:Fresh) : gateStack (freshRole k)=.inr k := by cases k <;> rfl
/-- Actual stopped state retains every source cell and the gate's physically acquired fresh outputs. -/
def result (bits:List Bool) : Stack→List Bool :=
  data (P.result bits) (fun k=>(GS.done (parentExponent bits) (values bits)).data (freshRole k))
/-- Real clean original-input controller halt. -/
def done (bits:List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- No graph count rescan: the existing source's real M word is shared directly. -/
theorem acquired_edges (bits:List Bool) : P.result bits P.edges=List.replicate (edgeValue bits) true := by
  unfold P.edges
  exact (SemiprimeD1StackRootParametersOriginal.metadata_preserved bits
    SemiprimeD1StackRootControllerMetadata.edges).trans
      (SemiprimeD1StackRootScopeBankExecution.result_counts bits).1
/-- Structural word projection, kept abstract so no original graph is reduced. -/
theorem initial_projection_of_words (source:P.Stack→List Bool) (a:List Bool)
    (v:SemiprimeD1StackScheduleActive.Param→Nat)
    (hl:source P.leaf=List.replicate (v .leaf) true)
    (hm:source P.minimum=List.replicate (v .minimum) true)
    (hu:source P.levels=List.replicate (v .levels) true)
    (hM:source P.edges=List.replicate (v .edges) true)
    (ha:source P.exponent=a) (k:G.Stack) :
    data source (fun _=>[]) (gateStack k)=(GS.initial a v).data k := by
  cases k with
  | inl k=>cases k with
    | leaf=>exact hl
    | minimum=>exact hm
    | levels=>exact hu
    | edges=>exact hM
    | left=>rfl
    | right=>rfl
    | limit=>rfl
    | valid=>rfl
    | scratch=>rfl
    | output=>rfl
  | inr k=>cases k with
    | exponent=>exact ha
    | levels=>rfl
    | reader=>rfl
    | scratch=>rfl
    | nextLevels=>rfl
    | nextExponent=>rfl
/-- Each shared original word agrees with the actual gate's required initial payload. -/
theorem initial_projection (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (k:G.Stack) :
    afterSource bits (gateStack k)=(GS.initial (parentExponent bits) (values bits)).data k := by
  exact initial_projection_of_words (P.result bits) (parentExponent bits) (values bits)
    (SemiprimeD1StackRootParametersOriginal.leaf_original bits hc)
    (SemiprimeD1StackRootParametersOriginal.minimum_original bits hc)
    (SemiprimeD1StackRootParametersOriginal.levels_original bits hc)
    (acquired_edges bits)
    (SemiprimeD1StackRootParametersOriginal.exponent_original bits hc) k
/-- The gate never changes any of the five directly shared parent operands. -/
theorem gate_readonly (a:List Bool) (v:SemiprimeD1StackScheduleActive.Param→Nat) (k:G.Stack)
    (hk:k∈[.inl .leaf,.inl .minimum,.inl .levels,.inl .edges,.inr .exponent]) :
    (GS.done a v).data k=(GS.initial a v).data k := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl <;>
    unfold SemiprimeD1StackRecursiveSchedule.done SemiprimeD1StackRecursiveSchedule.result <;>
    split <;> rfl
/-- Structural stopped-data projection uses only the five retained word equalities. -/
theorem result_projection_of_words (source:P.Stack→List Bool) (a:List Bool)
    (v:SemiprimeD1StackScheduleActive.Param→Nat)
    (hi:∀k:G.Stack,data source (fun _=>[]) (gateStack k)=(GS.initial a v).data k) (k:G.Stack) :
    data source (fun f=>(GS.done a v).data (freshRole f)) (gateStack k)=(GS.done a v).data k := by
  cases k with
  | inl k=>cases k with
    | leaf=>exact (hi (.inl .leaf)).trans (gate_readonly a v _ (by simp)).symm
    | minimum=>exact (hi (.inl .minimum)).trans (gate_readonly a v _ (by simp)).symm
    | levels=>exact (hi (.inl .levels)).trans (gate_readonly a v _ (by simp)).symm
    | edges=>exact (hi (.inl .edges)).trans (gate_readonly a v _ (by simp)).symm
    | left=>rfl
    | right=>rfl
    | limit=>rfl
    | valid=>rfl
    | scratch=>rfl
    | output=>rfl
  | inr k=>cases k with
    | exponent=>exact (hi (.inr .exponent)).trans (gate_readonly a v _ (by simp)).symm
    | levels=>rfl
    | reader=>rfl
    | scratch=>rfl
    | nextLevels=>rfl
    | nextExponent=>rfl
/-- Final source/gate projection is exact on every old and fresh allocated gate role. -/
theorem result_projection (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (k:G.Stack) :
    result bits (gateStack k)=(GS.done (parentExponent bits) (values bits)).data k := by
  exact result_projection_of_words (P.result bits) (parentExponent bits) (values bits)
    (initial_projection bits hc) k
end RiemannGaussian.SemiprimeD1StackRootRecursiveControlEncoding
