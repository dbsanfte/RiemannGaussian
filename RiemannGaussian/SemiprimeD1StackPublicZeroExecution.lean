/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicZero

/-! # Actual public zero-word checker source trace
The original modulus template and raw word are acquired by this SAME program.
The comparator's computed bit and complete cleanup close for all raw words.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackPublicZeroExecution
open SemiprimeD1StackPublicZero SemiprimeD1StackProcedureTrace
/-- Actual shared public source output, specified after its complete trace. -/
def context (bits : List Bool) : P.Stack→List Bool := SemiprimeD1BinaryPublicAcquisitionComponents.result bits
/-- Actual acquired binary word-width template. -/
def cached (bits : List Bool) : List Bool := context bits modulusKey
/-- Literal operand obtained by the actual WordBlock procedure. -/
def word (bits raw : List Bool) : List Bool := SemiprimeD1StackWordBlockExecution.result raw (cached bits)
/-- Actual original raw suffix left by block extraction. -/
def suffix (bits raw : List Bool) : List Bool := raw.drop (cached bits).length
/-- Specification of the actually computed numeric zero verdict. -/
def answer (bits raw : List Bool) : Bool := decide (SemiprimeBitArithmetic.bitValue (word bits raw)=0)
/-- Exact reached payload after original preprocessing once. -/
def ready (bits raw : List Bool) : Stack→List Bool := store (context bits) raw [] [] []
/-- Exact reached payload after actual raw-assignment copying. -/
def afterCopy (bits raw : List Bool) : Stack→List Bool := store (context bits) raw raw [] []
/-- Exact reached payload after full actual width-sized extraction. -/
def afterBlock (bits raw : List Bool) : Stack→List Bool := store (context bits) raw (suffix bits raw) (word bits raw) []
/-- Exact halted source: original public cells/raw/suffix and one verdict only. -/
def done (bits raw : List Bool) : C.State Stack Label :=
  ⟨none,none,none,store (context bits) raw (suffix bits raw) [] [answer bits raw],[]⟩
/-- Whole actual public/checker clock; every real callee and return is charged. -/
def timeBound (bits raw : List Bool) : ℕ :=
  (SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+1)+(5*raw.length+4)+
    (SemiprimeD1StackWordBlockExecution.totalTime (cached bits)+1)+
    (SemiprimeD1StackWordEqualExecution.executionTime (word bits raw) []+1)+1

/-- Actual original N preprocessing call INSIDE this same complete checker. -/
theorem acquire_call (bits raw : List Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits,
      Runs program (t+1) .start (store (P.input bits) raw [] [] []) .copyRaw (ready bits raw) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1BinaryPublicAcquisitionExecution.source_run bits hb
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program Sum.inl Label.acquire Sum.inl_injective
    P.program (SemiprimeD1BinaryPublicAcquisition.mainLabel .start) (fun _=>rfl) .start .copyRaw rfl t
    (P.initial bits) (⟨none,none,none,context bits,[]⟩:C.State P.Stack P.Label) _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rfl
/-- The actual assignment is physically copied and its original bytes retained. -/
theorem copy_call (bits raw : List Bool) :
    Runs program (5*raw.length+4) .copyRaw (ready bits raw) .block (afterCopy bits raw) := by
  apply included_call program copyStack Label.copy copy_injective SemiprimeD1StackCopy.code 0 (fun _=>rfl)
    .copyRaw .block rfl (5*raw.length+3)
    (SemiprimeD1StackCopy.state 0 none raw [] []) (SemiprimeD1StackCopy.done raw raw) _ _
  · rfl
  · rfl
  · simpa only [List.append_nil] using SemiprimeD1StackCopy.copy_words raw [] none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · fin_cases k <;> first | rfl | exact (hk 1 rfl).elim
        · rcases k with k|k <;> rfl
/-- Complete actual extraction uses the real acquired modulus width directly;
the unused raw suffix and all original padding are retained. -/
theorem block_call (bits raw : List Bool) :
    Runs program (SemiprimeD1StackWordBlockExecution.totalTime (cached bits)+1)
      .block (afterCopy bits raw) .compare (afterBlock bits raw) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program blockStack Label.extract block_injective
    B.program RiemannGaussian.SemiprimeD1StackWordFit.Label.start (fun _=>rfl) .block .compare rfl
    (SemiprimeD1StackWordBlockExecution.totalTime (cached bits))
    (B.initial raw (cached bits)) (SemiprimeD1StackWordBlockExecution.done raw (cached bits)) _ _
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackWordBlockExecution.source_run raw (cached bits)
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · fin_cases k <;> first | rfl | exact (hk 0 rfl).elim | exact (hk 4 rfl).elim
        · rcases k with k|k <;> rfl
/-- Real numeric comparison against actual empty zero consumes the acquired
word, paying all high-zero and mismatch suffix cleanup. -/
theorem compare_call (bits raw : List Bool) :
    Runs program (SemiprimeD1StackWordEqualExecution.executionTime (word bits raw) []+1)
      .compare (afterBlock bits raw) .done (done bits raw).data := by
  apply included_call program equalStack Label.equality equal_injective E.code .loop (fun _=>rfl)
    .compare .done rfl (SemiprimeD1StackWordEqualExecution.executionTime (word bits raw) [])
    (SemiprimeD1StackWordEqual.state (some .loop) none (word bits raw) [] [])
    (SemiprimeD1StackWordEqual.state none none [] [] [answer bits raw]) _ _
  · rfl
  · rfl
  · exact SemiprimeD1StackWordEqualExecution.source_run (word bits raw) [] none
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · rcases k with k|k
        · fin_cases k <;> first | rfl | exact (hk .left rfl).elim
        · rcases k with k|k
          · cases k <;> first | rfl | exact (hk .output rfl).elim
          · rfl
/-- COMPLETE actual original-input checker for every raw assignment, with no
modulus/width/word/zero-verdict/elapsed-count advice. -/
theorem source_run (bits raw : List Bool) (hb : bits≠[]) :
    ∃t≤timeBound bits raw,C.run program t (initial bits raw)=some (done bits raw) := by
  obtain ⟨a,ha,h0⟩:=acquire_call bits raw hb
  have h1:=copy_call bits raw
  have h2:=block_call bits raw
  have h3:=compare_call bits raw
  have h:=runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3
  obtain ⟨finish,hr,ho⟩:=h [] (initial bits raw) ⟨rfl,rfl,rfl⟩
  have he:=halt_run program .done rfl (done bits raw).data [] finish ho
  refine ⟨(((a+1)+(5*raw.length+4))+(SemiprimeD1StackWordBlockExecution.totalTime (cached bits)+1))+
    (SemiprimeD1StackWordEqualExecution.executionTime (word bits raw) []+1)+1,by unfold timeBound;omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some,he]
  rfl
/-- The output is exactly the bit actually written by the real comparator. -/
theorem output_answer (bits raw : List Bool) : (done bits raw).data output=[answer bits raw] := rfl
/-- Every acquired original public cache survives. -/
theorem retained_public (bits raw : List Bool) (k : P.Stack) : (done bits raw).data (.inl k)=context bits k := rfl
/-- The actual original assignment is physically retained. -/
theorem retained_raw (bits raw : List Bool) : (done bits raw).data assignment=raw := rfl
end RiemannGaussian.SemiprimeD1StackPublicZeroExecution
