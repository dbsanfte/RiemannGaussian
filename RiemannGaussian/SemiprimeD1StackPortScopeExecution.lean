/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortScopeSource
import RiemannGaussian.SemiprimeD1StackPortScopeTransduction
/-! # Closed original-N port occurrence to canonical scope-ID association -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortScopeExecution
open SemiprimeD1StackPortScopeRecords SemiprimeD1StackPortScopeSource
open SemiprimeD1StackPortScopeView SemiprimeD1StackPortScopeTransduction
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1PortScopeEncoding (portTape output)
/-- Exact actual scoped-port output, with every original source cache retained. -/
def result (bits:List Bool) : Stack→List Bool := finalData (base bits) (output (ports bits) (ids bits) [])
/-- Exact actual stopped original-N machine state. -/
def done (bits:List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- Whole actual source/copy/zip/reverse transition envelope before original-width substitution. -/
def budget (bits:List Bool) : ℕ :=
  10^104*(bits.length+1)^30+107*((portTape (ports bits) []).length+(vectorBits (ids bits)).length)+16
/-- Actual copies provide both concrete reader tapes and empty cache/work, without any advised menu. -/
theorem afterCopies_clean (bits:List Bool) : afterCopies bits=
    clean (base bits) (portTape (ports bits) []) (vectorBits (ids bits)) (fun _=>[]) [] := by
  funext k
  rcases k with k|k|k
  · rfl
  · rfl
  · cases k <;> rfl
/-- The real zipper runs on the actual two source streams, whose equal length was DERIVED. -/
theorem ready_original (bits:List Bool) :
    ∃ time ≤ 102*((portTape (ports bits) []).length+(vectorBits (ids bits)).length)+6,
      Runs program time (.local .parse) (afterCopies bits) (.local .halt) (result bits) := by
  rw [afterCopies_clean]
  exact ready (ports bits) (ids bits) (lengths bits) (base bits)
/-- The WHOLE fixed source begins with binary N only and performs the actual ID/port association. -/
theorem source_run (bits:List Bool) (hb:bits≠[]) :
    ∃ time ≤ budget bits,C.run program time (initial bits)=some (done bits) := by
  obtain ⟨a,ha,h0⟩:=source_call bits hb
  have h1:=ports_copy bits
  have h2:=ids_copy bits
  obtain ⟨b,hb',h3⟩:=ready_original bits
  have h:=h0.trans (h1.trans (h2.trans h3))
  obtain ⟨finish,hr,hout⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  refine ⟨a+((5*(portTape (ports bits) []).length+4)+(5*(vectorBits (ids bits)).length+4+b))+1,?_,?_⟩
  · unfold budget
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
    rcases hout with ⟨hpc,hdata,hframes⟩
    change C.step program finish=some (done bits)
    simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,hdata,hframes,done]
/-- EVERY original source/cache/port/ID byte is retained through physical association. -/
theorem retained_source (bits:List Bool) (key:S.Stack) : result bits (sourceStack key)=base bits key := rfl
/-- Exact output is scope-ID first followed by every unchanged original ordered port record. -/
theorem original_scope_records (bits:List Bool) : result bits (aux .output)=
    output (SemiprimeD1PortScopeEncoding.ports (SemiprimeD1StackPortCatalogueExecution.vertices bits) 0 0)
      (SemiprimeD1OrdinalBankSpec.words (SemiprimeD1StackPortOrdinalBankExecution.occurrences bits)) [] := by
  unfold result finalData
  rw [Function.update_self]
  rfl
/-- The produced ID stream has precisely numeric occurrence ordinals, with NO wire-major identification. -/
theorem id_values (bits:List Bool) : (ids bits).map SemiprimeBitArithmetic.bitValue=
    List.range (SemiprimeD1StackPortOrdinalBankExecution.occurrences bits) :=
  SemiprimeD1OrdinalBankSpec.values _
/-- Every physically acquired ID has the same actual occurrence-count width. -/
theorem id_length (bits:List Bool) (id:List Bool) (hi:id∈ids bits) :
    id.length=SemiprimeD1StackPortOrdinalBankExecution.occurrences bits :=
  SemiprimeD1OrdinalBankSpec.word_length _ _ hi
/-- Source initList is binary N alone, derived from its actual previous-stage certificate. -/
theorem source_input (bits:List Bool) (key:S.Stack) : S.input bits key=
    (if key=SemiprimeD1StackPortOrdinalBank.portStack SemiprimeD1StackPortCatalogue.originalInput then bits else []) := by
  have hi:=SemiprimeD1StackCalls.initial_correct
    (SemiprimeD1StackPortOrdinalBank.portStack SemiprimeD1StackPortCatalogue.originalInput)
    SemiprimeD1StackPortOrdinalBank.ids (Sum.inl SemiprimeD1StackPortOrdinalBank.Control.start)
    S.program bits
  have he:=hi.trans (SemiprimeD1StackPortOrdinalBankExecution.initial_eq bits)
  have hd:=congrArg (fun cfg:SemiprimeD1StackPortOrdinalBank.machine.Cfg=>cfg.stk (some key)) he
  change (if key=SemiprimeD1StackPortOrdinalBank.portStack SemiprimeD1StackPortCatalogue.originalInput then bits else [])=
    S.input bits key at hd
  exact hd.symm
/-- One fixed complete machine is initialized by N alone, with no graph/tally/ID/record answer preloaded. -/
theorem initial_eq (bits:List Bool) : Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs:initial bits=SemiprimeD1StackCalls.initial originalInput (.local .main) bits:=by
    unfold initial input SemiprimeD1StackCalls.initial
    congr 1
    funext k
    cases k with
    | inl key => simp [source_input,originalInput,sourceStack]
    | inr key => simp [originalInput,sourceStack]
  rw [hs]
  exact (SemiprimeD1StackCalls.initial_correct originalInput (aux .output) (.local .main) program bits).symm
end RiemannGaussian.SemiprimeD1StackPortScopeExecution
