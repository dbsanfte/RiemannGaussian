/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortOrdinalBank
/-! # Whole original-N port source and actual retained-tally ordinal-bank execution -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortOrdinalBankExecution
open SemiprimeD1StackPortOrdinalBank
open SemiprimeD1StackProcedureFragments (Runs)
open SemiprimeD1StackMultiplierLink (DataRel)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Exact original occurrence cardinality, used only to specify the actual produced bytes. -/
def occurrences (bits:List Bool) : ℕ := SemiprimeD1StackPortCatalogueTransduction.count
  (SemiprimeD1StackPortCatalogueExecution.vertices bits)
/-- The completed original port data, with only fresh bank work still empty. -/
def afterPort (bits:List Bool) : Stack→List Bool :=
  Sum.elim (SemiprimeD1StackPortCatalogueExecution.result bits) (fun _=>[])
/-- Actual bank output; every original source/cache/port/wire key byte remains identical. -/
def result (bits:List Bool) : Stack→List Bool :=
  Function.update (afterPort bits) ids (vectorBits (SemiprimeD1OrdinalBankSpec.words (occurrences bits)))
/-- Exact stopped source state. -/
def done (bits:List Bool) : C.State Stack Label := ⟨none,none,none,result bits,[]⟩
/-- Whole actual source envelope before substituting original graph-size resources. -/
def budget (bits:List Bool) : ℕ :=
  10^100*(bits.length+1)^30+1000*(occurrences bits+1)^2+3
/-- The actual bank operand is the physically pushed original occurrence tally. -/
theorem acquired_count (bits:List Bool) : afterPort bits count=unary (occurrences bits) := rfl
/-- All fresh work is empty, while the count input aliases the ACTUAL completed source tally. -/
theorem bank_input (bits:List Bool) : DataRel bankStack (afterPort bits)
    (O.initial (afterPort bits count)).data (afterPort bits) := by
  constructor
  · intro k
    rcases k with k|k
    · cases k <;> rfl
    · cases k <;> rfl
  · intro k _;rfl
/-- Actual bank termination preserves every original role and changes only its physically generated ID vector. -/
theorem bank_output (bits:List Bool) : DataRel bankStack (afterPort bits)
    (SemiprimeD1StackOrdinalBankLoop.done (afterPort bits count)).data (result bits) := by
  have hl:(afterPort bits count).length=occurrences bits:=by rw [acquired_count];simp only [unary,List.length_replicate]
  change DataRel bankStack (afterPort bits)
    (O.data [] [] [] [] (vectorBits (SemiprimeD1OrdinalBankSpec.words (afterPort bits count).length))
      (afterPort bits count) [] [] []) (result bits)
  rw [hl]
  constructor
  · intro k
    rcases k with k|k
    · cases k <;> simp [bankStack,O.count,SemiprimeD1StackOrdinalBank.count,O.data,
        SemiprimeD1StackOrdinalBank.data,SemiprimeD1StackAssignmentLoop.data,result,afterPort,ids,
        SemiprimeD1StackOrdinalBank.ids,Function.update]
    · cases k <;> simp [bankStack,O.count,SemiprimeD1StackOrdinalBank.count,O.data,
        SemiprimeD1StackOrdinalBank.data,result,afterPort,count,portStack,ids,
        SemiprimeD1StackOrdinalBank.ids,Function.update]
  · intro k hk
    have hn:k≠ids:=by
      intro he
      apply hk O.ids
      exact he.symm
    exact Function.update_of_ne hn _ _
/-- The original port machine is actually called once, retaining every foreign fresh bank role. -/
theorem ports_call (bits:List Bool) (hb:bits≠[]) :
    ∃ time ≤ 10^100*(bits.length+1)^30+1,
      Runs program time (.inl .start) (input bits) (.inl .bank) (afterPort bits) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackPortCatalogueBounds.source_run_polynomial bits hb
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program portStack (fun p=>.inr (.inl p))
    portStack_injective P.program (.local .main) (fun _=>rfl) (.inl .start) (.inl .bank) rfl m
    (SemiprimeD1StackPortCatalogue.initial bits) (SemiprimeD1StackPortCatalogueExecution.done bits)
    (input bits) (afterPort bits)
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
      cases k with
      | inl k => exact False.elim (hk k rfl)
      | inr k => rfl
/-- Actual nested ordinal procedure, controlled by the retained source tally rather than any supplied M. -/
theorem bank_call (bits:List Bool) :
    ∃ time ≤ 1000*(occurrences bits+1)^2+1,
      Runs program time (.inl .bank) (afterPort bits) (.inl .halt) (result bits) := by
  obtain ⟨m,hm,hr⟩:=SemiprimeD1StackOrdinalBankLoop.source_run (afterPort bits count)
  rw [acquired_count] at hm
  simp only [unary,List.length_replicate] at hm
  refine ⟨m+1,by omega,?_⟩
  apply SemiprimeD1StackProcedureCallsTrace.included_call program bankStack (fun p=>.inr (.inr p))
    bankStack_injective O.program (.inl .start) (fun _=>rfl) (.inl .bank) (.inl .halt) rfl m
    (O.initial (afterPort bits count)) (SemiprimeD1StackOrdinalBankLoop.done (afterPort bits count))
    (afterPort bits) (result bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · exact bank_input bits
  · exact bank_output bits
/-- Whole original binary-input caller executes both real suppliers, with no prepared tally or menu. -/
theorem source_run (bits:List Bool) (hb:bits≠[]) :
    ∃ time ≤ budget bits,C.run program time (initial bits)=some (done bits) := by
  obtain ⟨a,ha,h0⟩:=ports_call bits hb
  obtain ⟨b,hb',h1⟩:=bank_call bits
  have h:=h0.trans h1
  obtain ⟨finish,hr,hout⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  refine ⟨a+b+1,by unfold budget;omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  rcases hout with ⟨hpc,hdata,hframes⟩
  change C.step program finish=some (done bits)
  simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,hdata,hframes,done]
/-- Every original port, edge and parameter byte is retained through actual bank acquisition. -/
theorem retained_port (bits:List Bool) (key:P.Stack) :
    result bits (portStack key)=SemiprimeD1StackPortCatalogueExecution.result bits key := rfl
/-- Exact physically acquired global occurrence-ID bank. -/
theorem ids_value (bits:List Bool) : result bits ids=
    vectorBits (SemiprimeD1OrdinalBankSpec.words (occurrences bits)) := Function.update_self _ _ _
/-- Exact original occurrence tally is retained, independently of the E wire-owner domain. -/
theorem count_value (bits:List Bool) : result bits count=unary (occurrences bits) := rfl
/-- Exact source-only binary input fact, derived from the source machine's actual initList certificate. -/
theorem port_input (bits:List Bool) (key:P.Stack) : P.input bits key=
    (if key=P.originalInput then bits else []) := by
  have hi:=SemiprimeD1StackCalls.initial_correct P.originalInput (P.aux .output)
    (SemiprimeD1StackPortCatalogue.Label.local .main) P.program bits
  have he:=hi.trans (SemiprimeD1StackPortCatalogueExecution.initial_eq bits)
  have hd:=congrArg (fun cfg:SemiprimeD1StackPortCatalogue.machine.Cfg=>cfg.stk (some key)) he
  change (if key=P.originalInput then bits else [])=P.input bits key at hd
  exact hd.symm
/-- One fixed original-N finite machine starts with no tally, IDs, descriptor or graph answer. -/
theorem initial_eq (bits:List Bool) : Turing.initList machine bits=SemiprimeD1StackCalls.configuration (initial bits) := by
  have hs:initial bits=SemiprimeD1StackCalls.initial (portStack P.originalInput) (.inl .start) bits:=by
    unfold initial input SemiprimeD1StackCalls.initial
    congr 1
    funext k
    cases k with
    | inl k => simp [port_input,portStack]
    | inr k => simp [portStack]
  rw [hs]
  exact (SemiprimeD1StackCalls.initial_correct (portStack P.originalInput) ids (.inl .start) program bits).symm
end RiemannGaussian.SemiprimeD1StackPortOrdinalBankExecution
