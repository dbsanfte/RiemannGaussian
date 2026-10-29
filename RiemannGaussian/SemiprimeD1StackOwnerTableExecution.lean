/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerTableComponents
/-! # Whole actual scope/prefix-to-owner-tree execution, with no count advice -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackOwnerTableExecution
open SemiprimeD1StackOwnerTable SemiprimeD1StackOwnerTableComponents SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1OwnerPrefixBits (records scan)

/-- Source fragments compose at the exact same live data store. -/
theorem chain {m n : ℕ} {pc mid next : Label} {input middle output : Stack→List Bool}
    (h : Runs program m pc input mid middle) (g : Runs program n mid middle next output) :
    Runs program (m+n) pc input next output := runs_trans program _ _ _ _ _ _ _ _ h g
/-- Actual EOF on the physically acquired scope tally selects a fixed degree. -/
theorem count_empty (pc next left right : Label)
    (hp : program pc=.base (.pop tally next left right)) (key prefixBytes scopeBytes : List Bool) :
    Runs program 1 pc (data key prefixBytes scopeBytes [] [] []) next (data key prefixBytes scopeBytes [] [] []) := by
  apply one_base program pc next (.pop tally next left right) _ _ hp
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k;rfl
/-- One real degree marker is consumed; its count never enters an unbounded label. -/
theorem count_cons (pc eof next : Label)
    (hp : program pc=.base (.pop tally eof next next)) (key prefixBytes scopeBytes rest : List Bool) :
    Runs program 1 pc (data key prefixBytes scopeBytes (true::rest) [] [])
      next (data key prefixBytes scopeBytes rest [] []) := by
  apply one_base program pc next (.pop tally eof next next) _ _ hp
  · rfl
  · funext k;rcases k with k|k
    · rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k;rfl
/-- All0/1/2 actual degree dispatches, including the empty-scope case. -/
theorem count_dispatch (degree : Fin 3) (key prefixBytes scopeBytes : List Bool) :
    Runs program (degree.val+1) .count0 (data key prefixBytes scopeBytes (List.replicate degree.val true) [] [])
      (.scan degree) (data key prefixBytes scopeBytes [] [] []) := by
  fin_cases degree
  · exact count_empty .count0 (.scan 0) .count1 .count1 rfl key prefixBytes scopeBytes
  · exact chain (count_cons .count0 (.scan 0) .count1 rfl key prefixBytes scopeBytes [])
      (count_empty .count1 (.scan 1) .count2 .count2 rfl key prefixBytes scopeBytes)
  · have h:=chain (count_cons .count0 (.scan 0) .count1 rfl key prefixBytes scopeBytes [true])
      (chain (count_cons .count1 (.scan 1) .count2 rfl key prefixBytes scopeBytes [])
        (count_empty .count2 (.scan 2) .abort .abort rfl key prefixBytes scopeBytes))
    exact h
/-- The first actually scanned compatibility byte is consumed. -/
theorem low_run (degree : Fin 3) (low high : Bool) (key tail scopeBytes : List Bool) :
    Runs program 1 (.low degree) (data key tail scopeBytes [] [low,high] [])
      (.high degree low) (data key tail scopeBytes [] [high] []) := by
  apply one_base program (.low degree) (.high degree low)
    (.pop answer .abort (.high degree false) (.high degree true)) _ _ rfl
  · cases low <;> rfl
  · funext k;rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k;rfl
/-- The second computed byte selects the fixed literal palette entry. -/
theorem high_run (degree : Fin 3) (low high : Bool) (key tail scopeBytes : List Bool) :
    Runs program 1 (.high degree low) (data key tail scopeBytes [] [high] [])
      (.emit degree low high) (data key tail scopeBytes [] [] []) := by
  apply one_base program (.high degree low) (.emit degree low high)
    (.pop answer .abort (.emit degree low false) (.emit degree low true)) _ _ rfl
  · cases high <;> rfl
  · funext k;rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · rcases k with k|k
      · cases k <;> rfl
      · cases k;rfl
/-- PROOF-side finite degree, justified by actual original scope length. It is
neither a program operand nor supplied to this machine's initial configuration. -/
def actualDegree (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) : Fin 3 :=
  ⟨scopeWords.length,by omega⟩
/-- Exact final state retains key/scope/tail bytes and clears ALL private data. -/
def done (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) : C.State Stack Label :=
  let a:=scan key rows true true
  ⟨none,none,none,data key tail (vectorBits scopeWords) [] []
    (SemiprimeD1OwnerTablePalette.bytes (actualDegree scopeWords hs) a.1 a.2),[]⟩
/-- Exact executed source length; never a machine input or control payload. -/
def traceTime (key : List Bool) (rows : List (List Bool×Bool))
    (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) : ℕ :=
  let a:=scan key rows true true
  SemiprimeD1StackDigitCountExecution.totalTime scopeWords+
    SemiprimeD1StackOwnerPrefixExecution.loopTime key rows+
    (SemiprimeD1OwnerTablePalette.bytes (actualDegree scopeWords hs) a.1 a.2).length+scopeWords.length+9
/-- COMPLETE source from actual original key/prefix/scope records only. Scope
length≤2 is a proved original graph fact, not a supplied count/degree answer. -/
theorem source_run (key : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool)
    (scopeWords : List (List Bool)) (hs : scopeWords.length≤2) :
    C.run program (traceTime key rows scopeWords hs)
      (initial key (records rows tail) (vectorBits scopeWords))=some (done key rows tail scopeWords hs) := by
  let degree:=actualDegree scopeWords hs
  let a:=scan key rows true true
  have h0:=count_call key (records rows tail) scopeWords
  have h1:=count_dispatch degree key (records rows tail) (vectorBits scopeWords)
  have h2:=prefix_call degree key rows tail (vectorBits scopeWords)
  have h3:=low_run degree a.1 a.2 key tail (vectorBits scopeWords)
  have h4:=high_run degree a.1 a.2 key tail (vectorBits scopeWords)
  have h5:=palette_call degree a.1 a.2 key tail (vectorBits scopeWords)
  have h:=chain h0 (chain h1 (chain h2 (chain h3 (chain h4 h5))))
  obtain ⟨finish,hfinish,hout⟩:=h [] (initial key (records rows tail) (vectorBits scopeWords)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (done key rows tail scopeWords hs).data [] finish hout
  have ht : (SemiprimeD1StackDigitCountExecution.totalTime scopeWords+1)+((degree.val+1)+
      ((SemiprimeD1StackOwnerPrefixExecution.loopTime key rows+2)+(1+(1+
        ((SemiprimeD1OwnerTablePalette.bytes degree a.1 a.2).length+2)))))+1=traceTime key rows scopeWords hs := by
    dsimp only [traceTime,degree,a,actualDegree]
    omega
  rw [←ht,SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
  rfl
end RiemannGaussian.SemiprimeD1StackOwnerTableExecution
