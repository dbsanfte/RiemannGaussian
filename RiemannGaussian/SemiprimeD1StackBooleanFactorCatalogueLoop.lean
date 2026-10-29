/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueFinish
import RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndices
/-! # Actual original-descriptor sweep with one retained source catalogue -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueLoop
open SemiprimeD1StackBooleanFactorCatalogue SemiprimeD1StackBooleanFactorCatalogueView
open SemiprimeD1StackBooleanFactorCatalogueSource SemiprimeD1StackBooleanFactorCataloguePrimitives
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1BooleanFactorCatalogueIndices (key scopeWords indices vertex descriptorTape)
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (factorCount)
/-- Exact physical remaining descriptor queue; every other acquired catalogue byte survives. -/
def catalogue (bits : List Bool) (fs : List (Fin (factorCount (bitValue bits)))) : V.Stack→List Bool :=
  Function.update (VS.result bits) catalogueOutput (descriptorTape (bitValue bits) fs)
/-- Exact actual source/current-scope state at the loop entry. -/
def loopData (bits : List Bool) (n : Nat) (fs : List (Fin (factorCount (bitValue bits))))
    (hist out : List Bool) : Stack→List Bool :=
  data (FS.result bits (key n)) (catalogue bits fs) (fun _=>[]) hist out
/-- Exact actual state after the current row and all physical cleanup/key advancement. -/
def nextData (bits : List Bool) (n : Nat) (fs : List (Fin (factorCount (bitValue bits))))
    (hist out : List Bool) : Stack→List Bool :=
  data (SemiprimeD1StackFactorScopeFibre.afterSource bits (key n)) (catalogue bits fs) (fun _=>[]) hist out
/-- Mathematical physical history after consuming the original index list. -/
def afterRows (bits : List Bool) : Nat→List (Fin (factorCount (bitValue bits)))→List Bool→List Bool
  | _,[],hist=>hist
  | n,f::fs,hist=>afterRows bits (n+1) fs (DA.afterHistory (vertex (bitValue bits) f) (scopeWords bits n) hist)
/-- Actual one-row budget, keeping the source scope bytes and every cleanup read. -/
def rowBudget (bits : List Bool) (M n : Nat) (f : Fin (factorCount (bitValue bits))) : Nat :=
  DA.rowBound (E.vertex (vertex (bitValue bits) f)) (scopeWords bits n) M+
    SemiprimeD1StackBooleanDescriptorRecordEncoding.mass (E.vertex (vertex (bitValue bits) f))+
    (SemiprimeD1TensorTapeCodec.vectorBits (scopeWords bits n)).length+9
/-- Whole loop allowance charges one real next-EOF read and each later actual
retained-catalogue query, without executing source acquisition again. -/
def loopBudget (bits : List Bool) (M : Nat) : Nat→List (Fin (factorCount (bitValue bits)))→Nat
  | _,[]=>0
  | n,f::fs=>rowBudget bits M n f+1+
      if fs=[] then 0 else SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key (n+1))+2+
        loopBudget bits M (n+1) fs
/-- The acquired descriptor queue has exactly its declared actual reader bytes. -/
theorem catalogue_reader (bits : List Bool) (fs : List (Fin (factorCount (bitValue bits)))) :
    catalogue bits fs catalogueOutput=descriptorTape (bitValue bits) fs := Function.update_self _ _ _
/-- Actual descriptor consumption changes only the reader suffix. -/
theorem catalogue_tail (bits : List Bool) (f : Fin (factorCount (bitValue bits)))
    (fs : List (Fin (factorCount (bitValue bits)))) :
    Function.update (catalogue bits (f::fs)) catalogueOutput (descriptorTape (bitValue bits) fs)=catalogue bits fs := by
  unfold catalogue
  rw [Function.update_idem]
/-- Even a zero constructor tag is a nonempty five-field physical descriptor. -/
theorem descriptor_head {r t digits : Nat} (v : SemiprimeMacroGraph.SubdividedVertex r t digits) (tail : List Bool) :
    ∃head rest,SemiprimeD1VertexCatalogueEncoding.vertex v tail=head::rest := by
  rw [←SemiprimeD1EdgeCatalogueEncoding.record_vertex]
  change ∃head rest,SemiprimeSourceHistogramKeyBits.frame (E.vertex v 0)
    (SemiprimeSourceHistogramKeyBits.frame (E.vertex v 1)
      (SemiprimeSourceHistogramKeyBits.frame (E.vertex v 2)
        (SemiprimeSourceHistogramKeyBits.frame (E.vertex v 3)
          (SemiprimeSourceHistogramKeyBits.frame (E.vertex v 4) tail))))=head::rest
  cases E.vertex v 0 with
  | nil=>exact ⟨false,_,rfl⟩
  | cons b bs=>exact ⟨true,_,rfl⟩
/-- ONE complete actual loop iteration: physical EOF test, real five-field
descriptor/row call, all five drains, entire scope drain and one actual key push. -/
theorem row_step (bits : List Bool) (hN:0<bitValue bits) (M n : Nat)
    (f : Fin (factorCount (bitValue bits))) (fs : List (Fin (factorCount (bitValue bits))))
    (hist out : List Bool)
    (hl:∀s∈scopeWords bits n,s.length ≤ M)
    (hv:∀s∈scopeWords bits n,bitValue s ≤ M) :
    ∃t ≤ rowBudget bits M n f,
      Runs program t (.local .loop) (loopData bits n (f::fs) hist out) (.local .next)
        (nextData bits (n+1) fs (DA.afterHistory (vertex (bitValue bits) f) (scopeWords bits n) hist) out) := by
  let v:=vertex (bitValue bits) f
  let histNext:=DA.afterHistory v (scopeWords bits n) hist
  obtain ⟨b,rest,he⟩:=descriptor_head v (descriptorTape (bitValue bits) fs)
  have h0:Runs program 1 (.local .loop) (loopData bits n (f::fs) hist out)
      (.local .row) (loopData bits n (f::fs) hist out) := by
    apply SemiprimeD1StackPhysicalLoops.peek_nonempty program (.local .loop) (.local .reverse) (.local .row)
      descriptorReader rfl _ b rest
    change catalogue bits (f::fs) catalogueOutput=b::rest
    rw [catalogue_reader]
    exact he
  obtain ⟨t,ht,h1⟩:=descriptor_call (bitValue bits) hN v (FS.result bits (key n)) (catalogue bits (f::fs))
    (descriptorTape (bitValue bits) fs) hist out (scopeWords bits n) M
    (SemiprimeD1BooleanFactorCatalogueIndices.source_output bits n) (catalogue_reader bits (f::fs)) hl hv
  rw [catalogue_tail] at h1
  have h2:=clear_fields (FS.result bits (key n)) (catalogue bits fs) (E.vertex v) histNext out
  have h3:=clear_scope (FS.result bits (key n)) (catalogue bits fs) histNext out
  rw [result_clear] at h3
  have h4:=advance_run (SemiprimeD1StackFactorScopeFibre.afterSource bits (key n)) (catalogue bits fs) histNext out
  change Runs program 1 (.local .advance) _ (.local .next)
    (data (Function.update (SemiprimeD1StackFactorScopeFibre.afterSource bits (key n)) F.query (true::key n))
      (catalogue bits fs) (fun _=>[]) histNext out) at h4
  rw [afterSource_key,←SemiprimeD1BooleanFactorCatalogueIndices.key_succ] at h4
  have h:=h0.trans (h1.trans (h2.trans (h3.trans h4)))
  refine ⟨1+((t+1)+((SemiprimeD1StackBooleanDescriptorRecordEncoding.mass (E.vertex v)+5)+
    (((FS.result bits (key n) F.output).length+1)+1))),?_,h⟩
  unfold rowBudget
  rw [SemiprimeD1BooleanFactorCatalogueIndices.source_output]
  dsimp only [v] at ht ⊢
  omega
/-- Entire actual descriptor sweep. The value/width premises describe the
physically acquired scopes and are discharged by original-source bounds. -/
theorem rows_run (bits : List Bool) (hN:0<bitValue bits) (M : Nat)
    (hwidth:∀f : Fin (factorCount (bitValue bits)),∀s∈scopeWords bits f.val,s.length ≤ M)
    (hvalue:∀f : Fin (factorCount (bitValue bits)),∀s∈scopeWords bits f.val,bitValue s ≤ M)
    (n : Nat) (fs : List (Fin (factorCount (bitValue bits))))
    (hseq:fs.map Fin.val=List.range' n fs.length) (hne:fs≠[]) (hist out : List Bool) :
    ∃t ≤ loopBudget bits M n fs,
      Runs program t (.local .loop) (loopData bits n fs hist out) (.local .reverse)
        (nextData bits (n+fs.length) [] (afterRows bits n fs hist) out) := by
  induction fs generalizing n hist with
  | nil=>exact (hne rfl).elim
  | cons f fs ih=>
    have horder:f.val=n ∧ fs.map Fin.val=List.range' (n+1) fs.length := by
      simpa only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] using hseq
    have hl:∀s∈scopeWords bits n,s.length ≤ M:=by simpa only [horder.1] using hwidth f
    have hv:∀s∈scopeWords bits n,bitValue s ≤ M:=by simpa only [horder.1] using hvalue f
    obtain ⟨t,ht,h0⟩:=row_step bits hN M n f fs hist out hl hv
    let histNext:=DA.afterHistory (vertex (bitValue bits) f) (scopeWords bits n) hist
    cases fs with
    | nil=>
      have h1:Runs program 1 (.local .next) (nextData bits (n+1) [] histNext out)
          (.local .reverse) (nextData bits (n+1) [] histNext out) := by
        apply SemiprimeD1StackPhysicalLoops.peek_empty program (.local .next) (.local .reverse)
          (.local .query) (.local .query) descriptorReader rfl _
        exact catalogue_reader bits []
      refine ⟨t+1,?_,h0.trans h1⟩
      change t+1 ≤ rowBudget bits M n f+1+0
      omega
    | cons g gs=>
      obtain ⟨b,rest,he⟩:=descriptor_head (vertex (bitValue bits) g) (descriptorTape (bitValue bits) gs)
      have h1:Runs program 1 (.local .next) (nextData bits (n+1) (g::gs) histNext out)
          (.local .query) (nextData bits (n+1) (g::gs) histNext out) := by
        apply SemiprimeD1StackPhysicalLoops.peek_nonempty program (.local .next) (.local .reverse) (.local .query)
          descriptorReader rfl _ b rest
        change catalogue bits (g::gs) catalogueOutput=b::rest
        rw [catalogue_reader]
        exact he
      have h2:=query_call bits (key (n+1)) (catalogue bits (g::gs)) histNext out
      obtain ⟨u,hu,h3⟩:=ih (n+1) horder.2 (by simp) histNext
      have hi:n+1+(g::gs).length=n+(f::g::gs).length:=by simp only [List.length_cons];omega
      rw [hi] at h3
      have h:=h0.trans (h1.trans (h2.trans h3))
      refine ⟨t+(1+((SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key (n+1))+2)+u)),?_,h⟩
      change t+(1+(SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key (n+1))+2+u)) ≤
        rowBudget bits M n f+1+(SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key (n+1))+2+
          loopBudget bits M (n+1) (g::gs))
      omega
end RiemannGaussian.SemiprimeD1StackBooleanFactorCatalogueLoop
