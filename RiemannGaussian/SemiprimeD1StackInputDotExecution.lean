/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackInputDotEvaluate
/-! # CLOSED raw-assignment grouping and guarded dot execution
The only word list in the theorems is DERIVED from the actual physical producer.
It is never an input cache, source answer, getter or evaluator on the runtime API.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackInputDotExecution
open SemiprimeD1StackInputDotEvaluate SemiprimeD1StackProcedureTrace
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeMacroEntryBitPrimitives (Expr Valid)
/-- The ACTUAL stream of acquired raw words, including every EOF-padded cell. -/
def words (raw : List Bool) (args : Args) (cached : List Bool) : List (List Bool) :=
  SemiprimeD1StackWordVectorSpec.blocks cached args.count.length raw
/-- Actual producer output shares the same physical guard/dot cache. -/
def cache (raw : List Bool) (args : Args) (cached : List Bool) : SemiprimeD1StackExprDot.Cache :=
  withVector args (vectorBits (words raw args cached))
/-- Exact physical suffix after the actual count of actual fixed-width blocks. -/
def suffix (raw : List Bool) (args : Args) (cached : List Bool) : List Bool :=
  raw.drop (args.count.length*cached.length)
/-- Actual reached store after the producer, before any guard/source evaluation. -/
def acquired (raw : List Bool) (args : Args) (cached tail : List Bool) : Stack→List Bool :=
  store (G.initial (cache raw args cached) cached tail).data (suffix raw args cached) raw
/-- Exact complete final store, retaining BOTH original raw input and unread suffix. -/
def finalData (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (stride frequency n : ℕ) (tail : List Bool) : Stack→List Bool :=
  store (SemiprimeD1StackGuardedDotExecution.done (cache raw args cached) cached baseExpr
    (words raw args cached) stride frequency n tail).data (suffix raw args cached) raw
/-- Complete actual clean halt. -/
def done (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (stride frequency n : ℕ) (tail : List Bool) : C.State Stack Label :=
  ⟨none,none,none,finalData raw args cached baseExpr stride frequency n tail,[]⟩
/-- Actual producer and consumer bounds plus their REAL calls and final halt. -/
def timeBound (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (stride frequency n : ℕ) : ℕ :=
  SemiprimeD1StackWordVectorExecution.timeBound raw cached args.count+
    SemiprimeD1StackGuardedDotExecution.timeBound (cache raw args cached) cached baseExpr
      (words raw args cached) stride frequency n+3
/-- The actual vector producer executes ONCE. Its output, width and count roles
ARE the actual consumer cache/modulus/count roles, with no native vector transport. -/
theorem acquire_call (raw : List Bool) (args : Args) (cached tail : List Bool) :
    ∃t ≤ SemiprimeD1StackWordVectorExecution.timeBound raw cached args.count+1,
      Runs program t .start (initial raw args cached tail).data .compute (acquired raw args cached tail) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackWordVectorExecution.source_run raw cached args.count
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program vectorStack Label.acquire vector_injective
    W.program (.control .start) (fun _=>rfl) .start .compute rfl t
    (W.initial raw cached args.count) (SemiprimeD1StackWordVectorExecution.done raw cached args.count)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rcases k with k|k <;> fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;rcases k with k|k <;> fin_cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rcases k with k|k
        · rcases k with k|k
          · cases k <;> first | rfl | exact (hk W.output rfl).elim
          · rfl
        · rfl
      · rcases k with k|k <;> fin_cases k <;> first | rfl | exact (hk (.inl 0) rfl).elim
/-- The exact original guard/source/evaluator is called on the ACTUALLY ACQUIRED
vector. No vector, list of words, canonicality or whole-source validity is supplied. -/
theorem guarded_call (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (hbase : args.base=SemiprimeD1StackExprCodec.encode baseExpr [])
    (stride frequency n : ℕ) (hs : args.stride=unary stride) (hf : args.frequency=unary frequency)
    (hn : args.count=unary n) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr) :
    ∃t ≤ SemiprimeD1StackGuardedDotExecution.timeBound (cache raw args cached) cached baseExpr
      (words raw args cached) stride frequency n+1,
      Runs program t .compute (acquired raw args cached tail) .done
        (finalData raw args cached baseExpr stride frequency n tail) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1StackGuardedDotExecution.source_run (cache raw args cached) cached baseExpr hbase
    (words raw args cached) stride frequency n hs hf hn rfl tail hm hb
  refine ⟨t+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.guarded Sum.inl_injective
    G.program .start (fun _=>rfl) .compute .done rfl t (G.initial (cache raw args cached) cached tail)
    (SemiprimeD1StackGuardedDotExecution.done (cache raw args cached) cached baseExpr (words raw args cached) stride frequency n tail)
    _ _ rfl rfl rfl rfl hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk;rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- CLOSED whole RAW assignment -> real words -> real canonicality guard -> real
source/evaluation execution. Only source/metadata formats, base validity and M>1
remain. NO vector/getter, native grouping/assignment, count/result or clock advice. -/
theorem source_run (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (hbase : args.base=SemiprimeD1StackExprCodec.encode baseExpr [])
    (stride frequency n : ℕ) (hs : args.stride=unary stride) (hf : args.frequency=unary frequency)
    (hn : args.count=unary n) (tail : List Bool)
    (hm : 1<SemiprimeBitArithmetic.bitValue cached) (hb : Valid cached baseExpr) :
    ∃t ≤ timeBound raw args cached baseExpr stride frequency n,
      C.run program t (initial raw args cached tail)=some (done raw args cached baseExpr stride frequency n tail) := by
  obtain ⟨t,ht,h0⟩:=acquire_call raw args cached tail
  obtain ⟨m,hmul,h1⟩:=guarded_call raw args cached baseExpr hbase stride frequency n hs hf hn tail hm hb
  obtain ⟨finish,hfinish,hout⟩:=(runs_trans program _ _ _ _ _ _ _ _ h0 h1) [] (initial raw args cached tail) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (finalData raw args cached baseExpr stride frequency n tail) [] finish hout
  refine ⟨t+m+1,?_,?_⟩
  · unfold timeBound;omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
    rfl
/-- Exact rejected halt after real grouping; original raw input and suffix,
all prepared parameters and the newly ACQUIRED vector cache remain physical. -/
def rejected (raw : List Bool) (args : Args) (cached tail : List Bool) : C.State Stack Label :=
  ⟨none,none,none,store (SemiprimeD1StackGuardedDotExecution.rejected (cache raw args cached) cached tail).data
    (suffix raw args cached) raw,[]⟩
/-- Rejected whole RAW-input pipeline needs NO base validity, modulus positivity,
metadata-format, unary-count, grouped-word or whole-source validity advice. -/
theorem reject_source_run (raw : List Bool) (args : Args) (cached tail : List Bool)
    (ha : SemiprimeD1StackGuardedDotExecution.answer cached (words raw args cached)=false) :
    ∃t ≤ SemiprimeD1StackWordVectorExecution.timeBound raw cached args.count+
      SemiprimeD1StackVectorCanonicalExecution.timeBound (words raw args cached) cached+7,
      C.run program t (initial raw args cached tail)=some (rejected raw args cached tail) := by
  obtain ⟨t,ht,h0⟩:=acquire_call raw args cached tail
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackGuardedDotExecution.reject_source_run (cache raw args cached) cached
    (words raw args cached) rfl tail ha
  have h1 : Runs program (m+1) .compute (acquired raw args cached tail) .done (rejected raw args cached tail).data := by
    apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.guarded Sum.inl_injective
      G.program .start (fun _=>rfl) .compute .done rfl m (G.initial (cache raw args cached) cached tail)
      (SemiprimeD1StackGuardedDotExecution.rejected (cache raw args cached) cached tail)
      _ _ rfl rfl rfl rfl hr
    · constructor
      · intro k;rfl
      · intro k _;rfl
    · constructor
      · intro k;rfl
      · intro k hk;rcases k with k|k
        · exact (hk k rfl).elim
        · rfl
  obtain ⟨finish,hfinish,hout⟩:=(runs_trans program _ _ _ _ _ _ _ _ h0 h1) [] (initial raw args cached tail) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (rejected raw args cached tail).data [] finish hout
  refine ⟨t+(m+1)+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl
/-- Every original requested block is acquired exactly once, with no count answer. -/
theorem words_length (raw : List Bool) (args : Args) (cached : List Bool) :
    (words raw args cached).length=args.count.length := SemiprimeD1StackWordVectorSpec.blocks_length _ _ _
/-- The caller's physical unary count format makes vector length n AUTOMATIC. -/
theorem words_length_original (raw : List Bool) (args : Args) (cached : List Bool)
    (n : ℕ) (hn : args.count=unary n) : (words raw args cached).length=n := by
  rw [words_length,hn]
  exact List.length_replicate
/-- Literal old word-block grouping, including EOF padding, under count format. -/
theorem words_original (raw : List Bool) (args : Args) (cached : List Bool)
    (n : ℕ) (hn : args.count=unary n) :
    words raw args cached=SemiprimeD1StackWordVectorSpec.blocks cached n raw := by
  simp only [words,hn,unary,List.length_replicate]
/-- Final computed status belongs to the ACTUAL acquired vector, not an input verdict. -/
theorem status_original (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (stride frequency n : ℕ) (tail : List Bool) :
    (done raw args cached baseExpr stride frequency n tail).data status=
      [SemiprimeD1StackGuardedDotExecution.answer cached (words raw args cached)] := rfl
/-- Exact old numerical dot over ACTUAL acquired blocks, or [] on actual rejection. -/
theorem output_original (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (stride frequency n : ℕ) (tail : List Bool) :
    (done raw args cached baseExpr stride frequency n tail).data output=
      if SemiprimeD1StackGuardedDotExecution.answer cached (words raw args cached) then
        (SemiprimeMacroEntryBitPrimitives.execute cached (SemiprimeD1StackDotEvaluateExecution.expression baseExpr
          (words raw args cached) stride frequency n)).bits else [] :=
  SemiprimeD1StackGuardedDotExecution.output_original _ _ _ _ _ _ _ _
/-- Original raw assignment is physically retained, not reconstructed by a getter. -/
theorem retained_raw (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (stride frequency n : ℕ) (tail : List Bool) :
    (done raw args cached baseExpr stride frequency n tail).data rawRole=raw := rfl
/-- Exact actual unread suffix, including exhaustion/padding cases. -/
theorem retained_suffix (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (stride frequency n : ℕ) (tail : List Bool) :
    (done raw args cached baseExpr stride frequency n tail).data suffixRole=
      raw.drop (args.count.length*cached.length) := rfl
/-- EVERY other producer/private alias is physically empty at completion. -/
theorem vector_cleanup (raw : List Bool) (args : Args) (cached : List Bool) (baseExpr : Expr)
    (stride frequency n : ℕ) (tail : List Bool) (k : W.Stack)
    (hk : k≠W.original ∧ k≠.inl 0) :
    (done raw args cached baseExpr stride frequency n tail).data (.inr k)=[] := by
  rcases k with k|k <;> fin_cases k <;> simp_all [done,finalData,store,W.original]
end RiemannGaussian.SemiprimeD1StackInputDotExecution
