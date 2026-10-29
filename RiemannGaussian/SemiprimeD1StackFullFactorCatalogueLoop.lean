/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueFinish
import RiemannGaussian.SemiprimeD1BooleanFactorCatalogueIndices
/-! # Actual original-order ALL-factor sweep with full branch clocks and history -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackFullFactorCatalogueLoop
open SemiprimeD1StackFullFactorCatalogue SemiprimeD1StackFullFactorCatalogueView
open SemiprimeD1StackFullFactorCatalogueSource SemiprimeD1StackFullFactorCatalogueRows
open SemiprimeD1StackFullFactorCatalogueFields SemiprimeD1StackFullFactorCatalogueCleanup
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1BooleanFactorCatalogueIndices (key scopeWords indices vertex descriptorTape)
open SemiprimeBitArithmetic (bitValue)
open SemiprimePublicAcquiredExecution (factorCount)
/-- Actual remaining descriptor queue, retaining every other acquired catalogue word. -/
def catalogue (bits:List Bool) (fs:List (Fin (factorCount (bitValue bits)))) :V.Stack→List Bool:=
  Function.update (VS.result bits) catalogueOutput (descriptorTape (bitValue bits) fs)
/-- Exact reached shared-source, five empty raw caches and caller accumulation state. -/
def loopData (bits:List Bool) (n:Nat) (fs:List (Fin (factorCount (bitValue bits))))
    (hist out:List Bool) :Stack→List Bool:=
  data (FS.result bits (key n)) (catalogue bits fs) (fun _=>[]) hist out
/-- After physical drains and key advancement, every filter operand except the retained key is empty. -/
def nextData (bits:List Bool) (n:Nat) (fs:List (Fin (factorCount (bitValue bits))))
    (hist out:List Bool) :Stack→List Bool:=
  data (SemiprimeD1StackFactorScopeFibre.afterSource bits (key n)) (catalogue bits fs) (fun _=>[]) hist out
/-- Proof-side actual appended row history; no history/table getter exists in control. -/
def afterRow (bits:List Bool) (n:Nat) (f:Fin (factorCount (bitValue bits))) (hist out:List Bool) :List Bool:=
  DS.nextHistory (DR.originalCode (vertex (bitValue bits) f)) (DR.rawFields bits (vertex (bitValue bits) f))
    (scopeWords bits n) hist out
/-- Actual chronological accumulator after all original factors, including every arithmetic tag. -/
def afterRows (bits:List Bool) :Nat→List (Fin (factorCount (bitValue bits)))→List Bool→List Bool→List Bool
  | _,[],hist,_=>hist
  | n,f::fs,hist,out=>afterRows bits (n+1) fs (afterRow bits n f hist out) out
/-- SAME actual full component clock plus five physical parses/drains, full scope drain and key push. -/
def rowBudget (bits:List Bool) (n:Nat) (f:Fin (factorCount (bitValue bits))) (hist out:List Bool) :Nat:=
  DS.timeBound (DR.originalCode (vertex (bitValue bits) f)) (DR.rawFields bits (vertex (bitValue bits) f))
    (scopeWords bits n) hist out+9*mass (E.vertex (vertex (bitValue bits) f))+
    (SemiprimeD1TensorTapeCodec.vectorBits (scopeWords bits n)).length+49
/-- Whole real branch-clock sum: accumulated history is charged at every actual full source call. -/
def loopBudget (bits:List Bool) :Nat→List (Fin (factorCount (bitValue bits)))→List Bool→List Bool→Nat
  | _,[],_,_=>0
  | n,f::fs,hist,out=>rowBudget bits n f hist out+1+
      if fs=[] then 0 else SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key (n+1))+2+
        loopBudget bits (n+1) fs (afterRow bits n f hist out) out
/-- Acquired original descriptor reader contains exactly the reached physical suffix. -/
theorem catalogue_reader (bits:List Bool) (fs:List (Fin (factorCount (bitValue bits)))) :
    catalogue bits fs catalogueOutput=descriptorTape (bitValue bits) fs:=Function.update_self _ _ _
/-- Five actual field reads consume exactly one complete original descriptor. -/
theorem catalogue_tail (bits:List Bool) (f:Fin (factorCount (bitValue bits)))
    (fs:List (Fin (factorCount (bitValue bits)))) :
    Function.update (catalogue bits (f::fs)) catalogueOutput (descriptorTape (bitValue bits) fs)=catalogue bits fs:=by
  unfold catalogue;rw [Function.update_idem]
/-- The real five-frame parser consumes exactly the original vertex descriptor encoding. -/
theorem descriptor_record {r t digits:Nat} (v:SemiprimeMacroGraph.SubdividedVertex r t digits) (tail:List Bool) :
    SemiprimeD1VertexCatalogueEncoding.vertex v tail=suffix (E.vertex v) 0 tail:=by
  rw [←SemiprimeD1EdgeCatalogueEncoding.record_vertex v tail]
  rfl
/-- Every constructor, including empty tag zero, has a nonempty actual five-frame record. -/
theorem descriptor_head {r t digits:Nat} (v:SemiprimeMacroGraph.SubdividedVertex r t digits) (tail:List Bool) :
    ∃head rest,SemiprimeD1VertexCatalogueEncoding.vertex v tail=head::rest:=by
  rw [descriptor_record]
  change ∃head rest,SemiprimeSourceHistogramKeyBits.frame (E.vertex v 0) _=head::rest
  cases E.vertex v 0 with
  | nil=>exact ⟨false,_,rfl⟩
  | cons b bs=>exact ⟨true,_,rfl⟩
/-- Original N remains physically retained for every repeated real factor query. -/
theorem retained_N_key (bits keyBytes:List Bool) :FS.result bits keyBytes F.originalInput=bits:=rfl
/-- One COMPLETE actual row: real EOF peek, five field parsers, actual18-tag/full table source,
all original field/scope drains and one unary factor-key push. -/
theorem row_step (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (n:Nat) (f:Fin (factorCount (bitValue bits))) (fs:List (Fin (factorCount (bitValue bits))))
    (hist out:List Bool) :
    ∃t≤rowBudget bits n f hist out,Runs program t (.local .loop) (loopData bits n (f::fs) hist out)
      (.local .next) (nextData bits (n+1) fs (afterRow bits n f hist out) out):=by
  let v:=vertex (bitValue bits) f
  let histNext:=afterRow bits n f hist out
  obtain ⟨b,rest,he⟩:=descriptor_head v (descriptorTape (bitValue bits) fs)
  have h0:Runs program 1 (.local .loop) (loopData bits n (f::fs) hist out)
      (.local (.field 0)) (loopData bits n (f::fs) hist out):=by
    apply SemiprimeD1StackPhysicalLoops.peek_nonempty program (.local .loop) (.local .reverse) (.local (.field 0))
      descriptorReader rfl _ b rest
    change catalogue bits (f::fs) catalogueOutput=b::rest
    rw [catalogue_reader];exact he
  have hr:catalogue bits (f::fs) catalogueOutput=suffix (E.vertex v) 0 (descriptorTape (bitValue bits) fs):=by
    rw [catalogue_reader]
    exact descriptor_record v _
  have h1:=parse_run (FS.result bits (key n)) (catalogue bits (f::fs)) (E.vertex v)
    (descriptorTape (bitValue bits) fs) hist out hr
  rw [catalogue_tail] at h1
  obtain ⟨t,ht,h2⟩:=descriptor_call bits hc hN v (FS.result bits (key n)) (catalogue bits fs) hist out
    (scopeWords bits n) (retained_N_key bits (key n)) (SemiprimeD1BooleanFactorCatalogueIndices.source_output bits n)
  have h3:=clear_fields (FS.result bits (key n)) (catalogue bits fs) (E.vertex v) histNext out
  have h4:=clear_scope (FS.result bits (key n)) (catalogue bits fs) histNext out
  rw [result_clear] at h4
  have h5:=advance_run (SemiprimeD1StackFactorScopeFibre.afterSource bits (key n)) (catalogue bits fs) histNext out
  change Runs program 1 (.local .advance) _ (.local .next)
    (data (Function.update (SemiprimeD1StackFactorScopeFibre.afterSource bits (key n)) F.query (true::key n))
      (catalogue bits fs) (fun _=>[]) histNext out) at h5
  rw [afterSource_key,←SemiprimeD1BooleanFactorCatalogueIndices.key_succ] at h5
  have h:=h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))
  refine ⟨1+((8*mass (E.vertex v)+40)+((t+1)+((mass (E.vertex v)+5)+
    (((FS.result bits (key n) F.output).length+1)+1)))),?_,h⟩
  unfold rowBudget
  rw [SemiprimeD1BooleanFactorCatalogueIndices.source_output]
  dsimp only [v] at ht ⊢
  omega
/-- Entire actual descriptor sweep, retaining one acquired pair catalogue and all full branch clocks. -/
theorem rows_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits) (hN:0<bitValue bits)
    (n:Nat) (fs:List (Fin (factorCount (bitValue bits))))
    (hseq:fs.map Fin.val=List.range' n fs.length) (hne:fs≠[]) (hist out:List Bool) :
    ∃t≤loopBudget bits n fs hist out,Runs program t (.local .loop) (loopData bits n fs hist out)
      (.local .reverse) (nextData bits (n+fs.length) [] (afterRows bits n fs hist out) out):=by
  induction fs generalizing n hist with
  | nil=>exact (hne rfl).elim
  | cons f fs ih=>
    have horder:f.val=n ∧ fs.map Fin.val=List.range' (n+1) fs.length:=by
      simpa only [List.map_cons,List.length_cons,List.range'_succ,List.cons.injEq] using hseq
    obtain ⟨t,ht,h0⟩:=row_step bits hc hN n f fs hist out
    let histNext:=afterRow bits n f hist out
    cases fs with
    | nil=>
      have h1:Runs program 1 (.local .next) (nextData bits (n+1) [] histNext out)
          (.local .reverse) (nextData bits (n+1) [] histNext out):=by
        apply SemiprimeD1StackPhysicalLoops.peek_empty program (.local .next) (.local .reverse)
          (.local .query) (.local .query) descriptorReader rfl _
        exact catalogue_reader bits []
      refine ⟨t+1,?_,h0.trans h1⟩
      change t+1≤rowBudget bits n f hist out+1+0;omega
    | cons g gs=>
      obtain ⟨b,rest,he⟩:=descriptor_head (vertex (bitValue bits) g) (descriptorTape (bitValue bits) gs)
      have h1:Runs program 1 (.local .next) (nextData bits (n+1) (g::gs) histNext out)
          (.local .query) (nextData bits (n+1) (g::gs) histNext out):=by
        apply SemiprimeD1StackPhysicalLoops.peek_nonempty program (.local .next) (.local .reverse) (.local .query)
          descriptorReader rfl _ b rest
        change catalogue bits (g::gs) catalogueOutput=b::rest
        rw [catalogue_reader];exact he
      have h2:=query_call bits (key (n+1)) (catalogue bits (g::gs)) histNext out
      obtain ⟨u,hu,h3⟩:=ih (n+1) horder.2 (by simp) histNext
      have hi:n+1+(g::gs).length=n+(f::g::gs).length:=by simp only [List.length_cons];omega
      rw [hi] at h3
      have h:=h0.trans (h1.trans (h2.trans h3))
      refine ⟨t+(1+((SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key (n+1))+2)+u)),?_,h⟩
      change t+(1+(SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key (n+1))+2+u))≤
        rowBudget bits n f hist out+1+(SemiprimeD1StackFactorScopeFibreExecution.preparedTime bits (key (n+1))+2+
          loopBudget bits (n+1) (g::gs) histNext out)
      omega
end RiemannGaussian.SemiprimeD1StackFullFactorCatalogueLoop
