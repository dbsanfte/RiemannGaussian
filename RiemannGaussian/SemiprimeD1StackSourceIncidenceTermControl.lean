/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidenceEdges
import RiemannGaussian.SemiprimeD1StackSourceIncidenceLoopView
/-! # Actual edge returns and two-byte finite status reads in the pair controller -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceTermControl
open SemiprimeD1StackSourceIncidence SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidencePrimitives SemiprimeD1StackSourceIncidenceLoopView
open SemiprimeD1StackSourceIncidenceEdges SemiprimeD1StackSourceIncidenceCalls
open SemiprimeD1StackSourceIncidenceSpec (Status possible drop edge)
open SemiprimeD1StackProcedureTrace
/-- Same-program edge calls include a real call and real return above arbitrary actual outer frames. -/
theorem local_edge_call (pc:Label) (kind:Edge) (next:Label)
    (hc:program pc=.call (.edgeStart kind) next) (q:Nat) (before after:Stack→List Bool)
    (hr:Runs program q (.edgeStart kind) before .edgeReturn after) :
    Runs program (q+2) pc before next after :=by
  intro frames target h
  let mid:=SemiprimeD1StackCalls.execute (.call (.edgeStart kind) next) target
  have hm:SemiprimeD1StackCalls.run program 1 target=some mid:=by
    change SemiprimeD1StackCalls.step program target=some mid
    simp only [SemiprimeD1StackCalls.step,h.1,Option.map_some,hc,mid]
  have hat:At (.edgeStart kind) before (next::frames) mid:=by
    exact ⟨rfl,h.2.1,by simpa only [mid,SemiprimeD1StackCalls.execute] using congrArg (List.cons next) h.2.2⟩
  obtain ⟨finish,hf,hfAt⟩:=hr (next::frames) mid hat
  let last:SemiprimeD1StackCalls.State Stack Label:=⟨some next,finish.flag,some next,after,frames⟩
  have hl:SemiprimeD1StackCalls.run program 1 finish=some last:=by
    change SemiprimeD1StackCalls.step program finish=some last
    simp only [SemiprimeD1StackCalls.step,hfAt.1,Option.map_some,program,SemiprimeD1StackCalls.execute,hfAt.2.1,hfAt.2.2]
    rfl
  refine ⟨last,?_,rfl,rfl,rfl⟩
  rw [show q+2=1+(q+1) by omega,SemiprimeD1StackReturnLink.run_add,hm,Option.bind_some,
    SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact hl
/-- Each edge runs on the exact same full47-role loop bank, retaining both parser positions and total. -/
theorem edge_in_bank (i:Inputs) (outer inner lo lf ro rf total:List Bool) (kind:Edge) :
    ∃q≤edgeClock i.ids (if kind=.owner then lo else lf) (if kind=.owner then ro else rf),
      Runs program q (.edgeStart kind) (bank i outer inner lo lf ro rf [] [] [] [] total) .edgeReturn
        (bank i outer inner lo lf ro rf []
          [possible (edge i.ids (if kind=.owner then lo else lf) (if kind=.owner then ro else rf)),
            drop (edge i.ids (if kind=.owner then lo else lf) (if kind=.owner then ro else rf))] [] [] total) :=by
  let privateWords:=fun k=>bank i outer inner lo lf ro rf [] [] [] [] total (aux k)
  obtain ⟨q,hq,hr⟩:=edge_run i.ids i.chosen i.pfx privateWords kind rfl rfl
  have hl:endpoint privateWords false kind=(if kind=.owner then lo else lf):=by cases kind <;> rfl
  have hh:endpoint privateWords true kind=(if kind=.owner then ro else rf):=by cases kind <;> rfl
  rw [hl,hh] at hq hr
  dsimp only [privateWords] at hr
  rw [edge_bank,edge_bank] at hr
  exact ⟨q,hq,hr⟩
/-- Both actual owner-edge status bytes are physically consumed before the next finite controller branch. -/
theorem owner_flags (i:Inputs) (outer inner lo lf ro rf total:List Bool) (status:Status) :
    Runs program 2 .ownerPossible (bank i outer inner lo lf ro rf [] [possible status,drop status] [] [] total) (.factorCall status)
      (bank i outer inner lo lf ro rf [] [] [] [] total) :=by
  cases status with
  | reject=>
    have h0:=pop_run .ownerPossible .abort (.ownerDrop false) (.ownerDrop true) (aux .eqOutput)
      (bank i outer inner lo lf ro rf [] [false,false] [] [] total) [false,false] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer inner lo lf ro rf [] [false,false] [] [] total) (aux .eqOutput) [false]) at h0
    rw [update_comparison] at h0
    have h1:=pop_run (.ownerDrop false) .abort (.factorCall .reject) .abort (aux .eqOutput)
      (bank i outer inner lo lf ro rf [] [false] [] [] total) [false] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer inner lo lf ro rf [] [false] [] [] total) (aux .eqOutput) []) at h1
    rw [update_comparison] at h1
    exact join h0 h1
  | stable=>
    have h0:=pop_run .ownerPossible .abort (.ownerDrop false) (.ownerDrop true) (aux .eqOutput)
      (bank i outer inner lo lf ro rf [] [true,false] [] [] total) [true,false] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer inner lo lf ro rf [] [true,false] [] [] total) (aux .eqOutput) [false]) at h0
    rw [update_comparison] at h0
    have h1:=pop_run (.ownerDrop true) .abort (.factorCall .stable) (.factorCall .free) (aux .eqOutput)
      (bank i outer inner lo lf ro rf [] [false] [] [] total) [false] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer inner lo lf ro rf [] [false] [] [] total) (aux .eqOutput) []) at h1
    rw [update_comparison] at h1
    exact join h0 h1
  | free=>
    have h0:=pop_run .ownerPossible .abort (.ownerDrop false) (.ownerDrop true) (aux .eqOutput)
      (bank i outer inner lo lf ro rf [] [true,true] [] [] total) [true,true] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer inner lo lf ro rf [] [true,true] [] [] total) (aux .eqOutput) [true]) at h0
    rw [update_comparison] at h0
    have h1:=pop_run (.ownerDrop true) .abort (.factorCall .stable) (.factorCall .free) (aux .eqOutput)
      (bank i outer inner lo lf ro rf [] [true] [] [] total) [true] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer inner lo lf ro rf [] [true] [] [] total) (aux .eqOutput) []) at h1
    rw [update_comparison] at h1
    exact join h0 h1
/-- Both actual factor-edge status bytes are physically consumed before the next finite controller branch. -/
theorem factor_flags (i:Inputs) (outer inner lo lf ro rf total:List Bool) (first:Status) (status:Status) :
    Runs program 2 (.factorPossible first) (bank i outer inner lo lf ro rf [] [possible status,drop status] [] [] total) (.payload first status)
      (bank i outer inner lo lf ro rf [] [] [] [] total) :=by
  cases status with
  | reject=>
    have h0:=pop_run (.factorPossible first) .abort (.factorDrop first false) (.factorDrop first true) (aux .eqOutput)
      (bank i outer inner lo lf ro rf [] [false,false] [] [] total) [false,false] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer inner lo lf ro rf [] [false,false] [] [] total) (aux .eqOutput) [false]) at h0
    rw [update_comparison] at h0
    have h1:=pop_run (.factorDrop first false) .abort (.payload first .reject) .abort (aux .eqOutput)
      (bank i outer inner lo lf ro rf [] [false] [] [] total) [false] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer inner lo lf ro rf [] [false] [] [] total) (aux .eqOutput) []) at h1
    rw [update_comparison] at h1
    exact join h0 h1
  | stable=>
    have h0:=pop_run (.factorPossible first) .abort (.factorDrop first false) (.factorDrop first true) (aux .eqOutput)
      (bank i outer inner lo lf ro rf [] [true,false] [] [] total) [true,false] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer inner lo lf ro rf [] [true,false] [] [] total) (aux .eqOutput) [false]) at h0
    rw [update_comparison] at h0
    have h1:=pop_run (.factorDrop first true) .abort (.payload first .stable) (.payload first .free) (aux .eqOutput)
      (bank i outer inner lo lf ro rf [] [false] [] [] total) [false] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer inner lo lf ro rf [] [false] [] [] total) (aux .eqOutput) []) at h1
    rw [update_comparison] at h1
    exact join h0 h1
  | free=>
    have h0:=pop_run (.factorPossible first) .abort (.factorDrop first false) (.factorDrop first true) (aux .eqOutput)
      (bank i outer inner lo lf ro rf [] [true,true] [] [] total) [true,true] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer inner lo lf ro rf [] [true,true] [] [] total) (aux .eqOutput) [true]) at h0
    rw [update_comparison] at h0
    have h1:=pop_run (.factorDrop first true) .abort (.payload first .stable) (.payload first .free) (aux .eqOutput)
      (bank i outer inner lo lf ro rf [] [true] [] [] total) [true] rfl rfl
    change Runs program 1 _ _ _ (Function.update (bank i outer inner lo lf ro rf [] [true] [] [] total) (aux .eqOutput) []) at h1
    rw [update_comparison] at h1
    exact join h0 h1
end RiemannGaussian.SemiprimeD1StackSourceIncidenceTermControl
