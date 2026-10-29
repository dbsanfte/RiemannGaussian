/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCatalogueParse
import RiemannGaussian.SemiprimeD1StackPortCatalogueArity
import RiemannGaussian.SemiprimeD1StackPortCatalogueLoop
import RiemannGaussian.SemiprimeD1StackPortCatalogueClear
/-! # Actual original vertex-to-port transduction, with acquired arity and counters -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueScan
open SemiprimeD1StackPortCatalogue SemiprimeD1StackPortCatalogueView
open SemiprimeD1StackPortCatalogueArity SemiprimeD1StackPortCatalogueLoop
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1EdgeCatalogueEncoding (Record record vertex)
open SemiprimeD1StackEdgeCatalogueParse (wordMass)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual pre-emission scalar metadata budget; no port count is provided by a caller. -/
def recordTime {r t digits:ℕ} (v:SemiprimeMacroGraph.SubdividedVertex r t digits)
    (occurrence factor:ℕ) : ℕ :=
  1+(8*wordMass (vertex v)+40)+
    (SemiprimeD1StackVertexArityRecipes.recipeBudget
      (SemiprimeD1StackVertexArityOriginal.indexValue v) (r*t+1) r t digits+109)+
    loopTime (vertex v) (SemiprimeMacroGraph.subdividedArity v) occurrence factor 0+
    (SemiprimeMacroGraph.subdividedArity v+1)+(wordMass (vertex v)+5)+1
/-- An empty first descriptor field is still a present record, never confused with EOF. -/
theorem record_head (base:V.Stack→List Bool) (words:Record) (tail raw edges:List Bool) (factor occurrence:ℕ) :
    Runs program 1 (.local .parse)
      (clean base (record words tail) (fun _=>[]) raw [] edges (unary factor) (unary occurrence) [])
      (.local (.field 0))
      (clean base (record words tail) (fun _=>[]) raw [] edges (unary factor) (unary occurrence) []) := by
  apply one_base program _ _ (.peek (aux .reader) (.local .finalReverse)
    (.local (.field 0)) (.local (.field 0))) _ _ rfl
  · change some (SemiprimeD1StackBytecode.choose (Label.local .finalReverse)
      (.local (.field 0)) (.local (.field 0)) (record words tail).head?)=some (.local (.field 0))
    cases hw:words 0 with
    | nil => simp [SemiprimeD1StackBytecode.choose,record,frame,hw]
    | cons b word => simp [SemiprimeD1StackBytecode.choose,record,frame,hw]
  · rfl
/-- One whole original vertex is parsed, its arity computed, all ports emitted, and all transient fields cleared. -/
theorem record_run {r t digits:ℕ} (v:SemiprimeMacroGraph.SubdividedVertex r t digits)
    (base:V.Stack→List Bool) (hm:Metadata r t digits base) (tail raw edges:List Bool) (factor occurrence:ℕ) :
    ∃time≤recordTime v occurrence factor,Runs program time (.local .parse)
      (clean base (record (vertex v) tail) (fun _=>[]) raw [] edges (unary factor) (unary occurrence) [])
      (.local .parse)
      (clean base tail (fun _=>[])
        ((records (vertex v) (SemiprimeMacroGraph.subdividedArity v) occurrence factor 0 []).reverse++raw)
        [] edges (unary (factor+1)) (unary (occurrence+SemiprimeMacroGraph.subdividedArity v)) []) := by
  have h0:=record_head base (vertex v) tail raw edges factor occurrence
  have h1:=SemiprimeD1StackPortCatalogueParse.fields_clean base (vertex v) tail raw [] edges (unary factor) (unary occurrence) []
  obtain ⟨ta,hta,h2⟩:=arity_run v base hm tail raw [] edges (unary factor) (unary occurrence)
  have h3:=loop_run base tail (vertex v) raw edges (SemiprimeMacroGraph.subdividedArity v) occurrence factor 0
  simp only [Nat.zero_add,show unary 0=[] from rfl] at h3
  let nextRaw:=(records (vertex v) (SemiprimeMacroGraph.subdividedArity v) occurrence factor 0 []).reverse++raw
  have h4:=SemiprimeD1StackPortCatalogueClear.slot_run base tail (vertex v) nextRaw
    (unary (SemiprimeMacroGraph.subdividedArity v)) edges (unary factor)
    (unary (occurrence+SemiprimeMacroGraph.subdividedArity v))
  have h5:=SemiprimeD1StackPortCatalogueClear.caches_run base tail (vertex v) nextRaw [] edges
    (unary factor) (unary (occurrence+SemiprimeMacroGraph.subdividedArity v)) []
  have h6:=SemiprimeD1StackPortCatalogueClear.factor_run base tail nextRaw edges factor
    (occurrence+SemiprimeMacroGraph.subdividedArity v)
  have h:=h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6)))))
  have h':=h
  simp only [unary,List.length_replicate] at h'
  refine ⟨_,?_,h'⟩
  unfold recordTime
  omega
end RiemannGaussian.SemiprimeD1StackPortCatalogueScan
