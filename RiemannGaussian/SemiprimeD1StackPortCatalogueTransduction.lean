/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCatalogueScan
/-! # Complete original factor-major transduction of all actual acquired descriptors -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortCatalogueTransduction
open SemiprimeD1StackPortCatalogue SemiprimeD1StackPortCatalogueView
open SemiprimeD1StackPortCatalogueArity SemiprimeD1StackPortCatalogueLoop
open SemiprimeD1StackPortCatalogueEmit (record8)
open SemiprimeD1StackProcedureFragments (Runs one_base)
open SemiprimeD1EdgeCatalogueEncoding (Record record vertex tape)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeMacroGraph
/-- Mathematical output of the actual factor-major port loop. -/
def output {r t digits:ℕ} : List (SubdividedVertex r t digits)→ℕ→ℕ→List Bool→List Bool
  | [],_,_,tail => tail
  | v::vs,f,n,tail => records (vertex v) (subdividedArity v) n f 0
      (output vs (f+1) (n+subdividedArity v) tail)
/-- Actual accumulated local transition upper bounds, retaining arity work for every vertex. -/
def scanTime {r t digits:ℕ} : List (SubdividedVertex r t digits)→ℕ→ℕ→ℕ
  | [],_,_ => 0
  | v::vs,f,n => SemiprimeD1StackPortCatalogueScan.recordTime v n f+
      scanTime vs (f+1) (n+subdividedArity v)
/-- Exact total number of original occurrences, independent of serialized-byte length. -/
def count {r t digits:ℕ} (vs:List (SubdividedVertex r t digits)) : ℕ :=
  (vs.map subdividedArity).sum
/-- Every recursive record constructor preserves its literal actual suffix. -/
theorem records_append (words:Record) (fuel n f slot:ℕ) (tail:List Bool) :
    records words fuel n f slot tail=records words fuel n f slot []++tail := by
  induction fuel generalizing n slot with
  | zero => rfl
  | succ fuel ih =>
    simp only [records]
    rw [ih,SemiprimeD1StackPortCatalogueLoop.record8_append]
    conv_rhs => rw [SemiprimeD1StackPortCatalogueLoop.record8_append]
    simp only [List.append_assoc]
/-- The physical recursive loop is the exact ascending original local-slot enumeration. -/
theorem records_range (words:Record) (fuel n f slot:ℕ) (tail:List Bool) :
    records words fuel n f slot tail=(List.range fuel).foldr
      (fun j rest=>SemiprimeD1PortCatalogueEncoding.encode (n+j) f (slot+j) words rest) tail := by
  induction fuel generalizing n slot with
  | zero => rfl
  | succ fuel ih =>
    rw [List.range_succ_eq_map,List.foldr_cons,List.foldr_map,records,ih]
    simp only [Nat.add_zero,record8,SemiprimeD1PortCatalogueEncoding.encode]
    simp only [Nat.succ_eq_add_one,Nat.add_left_comm,Nat.add_comm]
/-- Exact original factor-major port specification, preserving all duplicates and zero-arity factors. -/
theorem output_original {r t digits:ℕ} (vs:List (SubdividedVertex r t digits)) (f n:ℕ) (tail:List Bool) :
    output vs f n tail=SemiprimeD1PortCatalogueEncoding.fromVertices vs f n tail := by
  induction vs generalizing f n with
  | nil => rfl
  | cons v vs ih =>
    rw [output,ih,SemiprimeD1PortCatalogueEncoding.fromVertices,records_range]
    simp only [Nat.zero_add,SemiprimeD1PortCatalogueEncoding.slots]
/-- All original factors are actually traversed, including every zero-arity factor. -/
theorem scan_run {r t digits:ℕ} (vs:List (SubdividedVertex r t digits))
    (base:V.Stack→List Bool) (hm:Metadata r t digits base) (raw edges:List Bool) (f n:ℕ) :
    ∃ time ≤ scanTime vs f n,Runs program time (.local .parse)
      (clean base (tape (vs.map vertex) []) (fun _=>[]) raw [] edges (unary f) (unary n) [])
      (.local .parse)
      (clean base [] (fun _=>[]) ((output vs f n []).reverse++raw)
        [] edges (unary (f+vs.length)) (unary (n+count vs)) []) := by
  induction vs generalizing raw f n with
  | nil =>
    refine ⟨0,by exact Nat.le_refl 0,?_⟩
    simpa only [tape,List.foldr_nil,List.map_nil,output,List.reverse_nil,List.nil_append,List.length_nil,
      count,List.sum_nil,Nat.add_zero] using
      (Runs.refl program (.local .parse) (clean base [] (fun _=>[]) raw [] edges (unary f) (unary n) []))
  | cons v vs ih =>
    obtain ⟨a,ha,h0⟩:=SemiprimeD1StackPortCatalogueScan.record_run v base hm
      (tape (vs.map vertex) []) raw edges f n
    let nextRaw:=(records (vertex v) (subdividedArity v) n f 0 []).reverse++raw
    obtain ⟨b,hb,h1⟩:=ih nextRaw (f+1) (n+subdividedArity v)
    have h:=h0.trans h1
    have hout:(output vs (f+1) (n+subdividedArity v) []).reverse++nextRaw=
        (output (v::vs) f n []).reverse++raw:=by
      rw [output,records_append]
      simp only [List.reverse_append,List.append_assoc,nextRaw]
    rw [hout] at h
    refine ⟨a+b,by simp only [scanTime];omega,?_⟩
    simpa only [List.map_cons,tape,List.foldr_cons,List.length_cons,count,List.map_cons,List.sum_cons,
      show f+1+vs.length=f+(vs.length+1) by omega,
      show n+subdividedArity v+(vs.map subdividedArity).sum=
        n+(subdividedArity v+(vs.map subdividedArity).sum) by omega] using h
/-- Final physical data retain the complete edge tape and both acquired cardinality tallies. -/
def finalData (base:V.Stack→List Bool) (edges ports:List Bool) (f n:ℕ) : Stack→List Bool :=
  Function.update (clean base [] (fun _=>[]) [] [] edges (unary f) (unary n) []) (aux .output) ports
/-- Actual final EOF peek does not discard any payload. -/
theorem eof_run (base:V.Stack→List Bool) (raw edges:List Bool) (f n:ℕ) :
    Runs program 1 (.local .parse) (clean base [] (fun _=>[]) raw [] edges (unary f) (unary n) [])
      (.local .finalReverse) (clean base [] (fun _=>[]) raw [] edges (unary f) (unary n) []) := by
  apply one_base program _ _ (.peek (aux .reader) (.local .finalReverse)
    (.local (.field 0)) (.local (.field 0))) _ _ rfl
  · rfl
  · rfl
/-- Whole real transducer, including its final reverse and physically retained counts. -/
theorem ready {r t digits:ℕ} (vs:List (SubdividedVertex r t digits))
    (base:V.Stack→List Bool) (hm:Metadata r t digits base) (edges:List Bool) :
    ∃ time ≤ scanTime vs 0 0+2*(output vs 0 0 []).length+4,
      Runs program time (.local .parse)
        (clean base (tape (vs.map vertex) []) (fun _=>[]) [] [] edges [] [] []) (.local .halt)
        (finalData base edges (output vs 0 0 []) vs.length (count vs)) := by
  obtain ⟨a,ha,h0⟩:=scan_run vs base hm [] edges 0 0
  simp only [Nat.zero_add,List.append_nil,show unary 0=[] from rfl] at h0
  have h1:=eof_run base (output vs 0 0 []).reverse edges vs.length (count vs)
  have h2:=SemiprimeD1StackPortCataloguePrimitives.reverse_call true
    (clean base [] (fun _=>[]) (output vs 0 0 []).reverse [] edges (unary vs.length) (unary (count vs)) [])
    (.local .finalReverse) (.local .halt) rfl
  change Runs program (2*(output vs 0 0 []).reverse.length+3) _ _ _
    (Function.update (Function.update
      (clean base [] (fun _=>[]) (output vs 0 0 []).reverse [] edges (unary vs.length) (unary (count vs)) [])
        (oldAux .reversed) []) (aux .output) ((output vs 0 0 []).reverse.reverse++[])) at h2
  rw [List.length_reverse,List.reverse_reverse,List.append_nil,clean_raw] at h2
  refine ⟨a+(1+(2*(output vs 0 0 []).length+3)),by omega,?_⟩
  exact h0.trans (h1.trans h2)
end RiemannGaussian.SemiprimeD1StackPortCatalogueTransduction
