/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionArithmetic
/-! # Exact real binary increment/copy/adder calls and physical boundary views -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionPrimitives
open SemiprimeD1StackPhaseWorkingPrecision SemiprimeD1StackPhaseWorkingPrecisionArithmetic
open SemiprimeD1StackProcedureTrace
namespace Link
export SemiprimeD1StackMultiplierLink (DataRel data_update)
end Link
/-- Exact binary stage view; both actual scratch words are empty at every boundary. -/
def data (old : M.Stack→List Bool) (left right output counter next todo zeros shifts power : List Bool) : Stack→List Bool :=
  store old (words left right [] output counter next todo zeros shifts [] power)
/-- Chronological actual instruction composition retains every real outer frame. -/
theorem join {m n : Nat} {pc mid next : Label} {d e f : Stack→List Bool}
    (h : Runs program m pc d mid e) (g : Runs program n mid e next f) :
    Runs program (m+n) pc d next f :=runs_trans program m n pc mid next d e f h g
/-- One physically executed literal binary write. -/
theorem push (pc next : Label) (key : Stack) (bit : Bool) (d : Stack→List Bool)
    (hc : program pc=.base (.push key bit next)) :
    Runs program 1 pc d next (Function.update d key (bit::d key)) :=by
  apply one_base program pc next (.push key bit next) _ _ hc <;> rfl
/-- Actual preserving copy into a clear physical destination, with both real loops paid. -/
theorem copy_call (kind : Fin 10) (pc next : Label) (hc : program pc=.call (.copy kind 0) next)
    (d : Stack→List Bool) (hs : d (aux .copyScratch)=[]) (ht : d (copyTarget kind)=[]) :
    Runs program (5*(d (copySource kind)).length+4) pc d next
      (Function.update d (copyTarget kind) (d (copySource kind))) :=by
  let xs:=d (copySource kind)
  have hi:Link.DataRel (copyStack kind) d (SemiprimeD1StackCopy.state 0 none xs [] []).store d:=by
    constructor
    · intro k;fin_cases k
      · rfl
      · exact ht
      · exact hs
    · intro k _;rfl
  have ho:=Link.data_update (copyStack kind) (copy_injective kind) _ _ _ hi (1:Fin 3) xs
  have he:Function.update (SemiprimeD1StackCopy.state 0 none xs [] []).store 1 xs=
      (SemiprimeD1StackCopy.done xs xs).store:=by funext k;fin_cases k <;> rfl
  rw [he] at ho
  have hr:=SemiprimeD1StackCopy.copy_words xs [] none
  rw [List.append_nil] at hr
  exact included_call program (copyStack kind) (Label.copy kind) (copy_injective kind)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc (5*xs.length+3)
    (SemiprimeD1StackCopy.state 0 none xs [] []) (SemiprimeD1StackCopy.done xs xs) d _ rfl rfl hr hi ho
/-- Actual frozen increment consumes the counter and writes its REAL carry-prefix/wrapped bits. -/
theorem increment_call (second : Bool) (old : M.Stack→List Bool) (l r out word todo power : List Bool) :
    ∃q≤10*word.length+16,Runs program q (.increment second)
      (data old l r out word [] todo [] [] power) (.popOverflow second)
      (data old l r out [] (SemiprimeD1StackIncrement.overflow word::I.wrapped word) todo [] [] power) :=by
  obtain ⟨q,hq,hr⟩:=SemiprimeD1StackIncrementBytecode.increment_run word []
  simp only [List.append_nil] at hr
  refine ⟨q+1,by omega,?_⟩
  apply included_call program incrementStack Label.counter increment_injective Inc.code Inc.entry (fun _=>rfl)
    (.increment second) (.popOverflow second) rfl q
    ⟨some Inc.entry,none,Inc.contents word [] []⟩
    ⟨none,none,Inc.contents [] [] (SemiprimeD1StackIncrement.overflow word::I.wrapped word)⟩ _ _ rfl rfl hr
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rfl
      · cases k <;> first
        | rfl
        | exact (hk .input rfl).elim
        | exact (hk .scratch rfl).elim
        | exact (hk .output rfl).elim
/-- One REAL consuming ripple addition; original metadata and binary D remain retained. -/
theorem adder_call (second : Bool) (old : M.Stack→List Bool) (l r power : List Bool) :
    Runs program (3*(max l.length r.length+1)+2*(SemiprimeBitArithmetic.addBits l r false).bits.length+3)
      (.add second) (data old l r [] [] [] [] [] [] power)
      (if second then .done else .copyZero true)
      (data old [] [] (SemiprimeBitArithmetic.addBits l r false).bits [] [] [] [] [] power) :=by
  apply included_call program adderStack Label.adder adder_injective Add.code (.start false) (fun _=>rfl)
    (.add second) (if second then .done else .copyZero true) rfl
    (3*(max l.length r.length+1)+2*(SemiprimeBitArithmetic.addBits l r false).bits.length+2)
    (Add.state (some (.start false)) none l r [] [])
    (Add.state none none [] [] [] (SemiprimeBitArithmetic.addBits l r false).bits) _ _ rfl rfl
    (SemiprimeD1StackAdderExecution.source_run l r false)
  · constructor
    · intro k;cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> rfl
    · intro k hk;rcases k with k|k
      · rfl
      · cases k <;> first
        | rfl
        | exact (hk .left rfl).elim
        | exact (hk .right rfl).elim
        | exact (hk .scratch rfl).elim
        | exact (hk .output rfl).elim
/-- Literal ripple time is linear in the ACTUAL physical binary operand widths. -/
theorem adder_time_le (l r : List Bool) :
    3*(max l.length r.length+1)+2*(SemiprimeBitArithmetic.addBits l r false).bits.length+3≤5*(l.length+r.length)+8 :=by
  have hh:=(SemiprimeBitArithmetic.addBits_counts l r false).2.2.2.2
  have hm:max l.length r.length≤ l.length+r.length:=max_le (by omega) (by omega)
  omega
end RiemannGaussian.SemiprimeD1StackPhaseWorkingPrecisionPrimitives
