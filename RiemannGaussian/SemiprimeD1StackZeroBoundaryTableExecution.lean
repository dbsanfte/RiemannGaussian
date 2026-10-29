/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackZeroBoundaryTable
import RiemannGaussian.SemiprimeD1ZeroBoundaryTables
/-! # Closed N-only whole-boundary acquisition with actual source and tree calls -/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeD1StackZeroBoundaryTableExecution
open SemiprimeD1StackZeroBoundaryTable
open SemiprimeD1StackProcedureFragments (Runs one_base)
/-- Actual public acquisition ONCE, with all metadata/source reports retained. -/
theorem acquire_call (bits : List Bool) (hb : bits≠[]) :
    ∃t≤SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits,
      Runs program (t+1) (.inl .start) (store (P.input bits) [] []) (.inl .seed) (store (context bits) [] []) := by
  obtain ⟨t,ht,hr⟩:=SemiprimeD1BinaryPublicAcquisitionExecution.source_run bits hb
  refine ⟨t,ht,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program Sum.inl publicLabel Sum.inl_injective
    P.program (P.mainLabel .start) (fun _=>rfl) (.inl .start) (.inl .seed) rfl t
    (P.initial bits) (⟨none,none,none,context bits,[]⟩:C.State P.Stack P.Label)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k; rfl
    · intro k hk; rfl
  · constructor
    · intro k; rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · cases k <;> rfl
/-- The ONLY actual entry acquisition is ONE literal true push. EOF supplies
all later false entries during the real writer's actual reads. -/
theorem seed_call (bits : List Bool) :
    Runs program 1 (.inl .seed) (store (context bits) [] []) (.inl .write) (store (context bits) [true] []) := by
  apply one_base program _ _ (.push (treeStack .input) true (.inl .write)) _ _ rfl
  · rfl
  · funext k; rcases k with k|k
    · rfl
    · cases k <;> rfl
/-- Real recursive writer shares the ACTUALLY acquired modulus-word markers;
its exact depth restore preserves the entire original public cache. -/
theorem tree_call (bits : List Bool) :
    Runs program (SemiprimeD1StackBooleanTreeExecution.totalTime [true] (cached bits)+1)
      (.inl .write) (store (context bits) [true] []) (.inl .done) (done bits).data := by
  apply SemiprimeD1StackProcedureInclusion.included_call program treeStack treeLabel tree_injective
    T.program .start (fun _=>rfl) (.inl .write) (.inl .done) rfl _
    (T.initial [true] (cached bits)) (SemiprimeD1StackBooleanTreeExecution.done [true] (cached bits))
  · rfl
  · rfl
  · rfl
  · rfl
  · exact SemiprimeD1StackBooleanTreeExecution.source_run [true] (cached bits)
  · constructor
    · intro k; cases k <;> rfl
    · intro k hk; rfl
  · constructor
    · intro k
      cases k with
      | input => exact (SemiprimeD1ZeroBoundaryTables.singleton_drop _).symm
      | depth => rfl
      | history => rfl
      | output => rfl
    · intro k hk
      rcases k with k|k
      · rfl
      · cases k with
        | input => exact (hk .input rfl).elim
        | depth => rfl
        | history => rfl
        | output => exact (hk .output rfl).elim
/-- Closed actual budget, source quadratic plus writer output/exponential time;
NO arity/table/stream/entry/clock answer is supplied to the program. -/
def timeBound (bits : List Bool) : ℕ :=
  SemiprimeD1BinaryPublicAcquisitionExecution.timeBound bits+40*2^(cached bits).length+4
/-- Whole N-only acquisition, all calls/returns, the true push and final halt. -/
theorem source_run (bits : List Bool) (hb : bits≠[]) :
    ∃t≤timeBound bits,C.run program t (initial bits)=some (done bits) := by
  obtain ⟨a,ha,h0⟩:=acquire_call bits hb
  have h1:=seed_call bits
  have h2:=tree_call bits
  have hh:=h0.trans (h1.trans h2)
  obtain ⟨finish,hfinish,hAt⟩:=hh [] (initial bits) ⟨rfl,rfl,rfl⟩
  refine ⟨(a+1)+(1+(SemiprimeD1StackBooleanTreeExecution.totalTime [true] (cached bits)+1))+1,?_,?_⟩
  · have ht:=SemiprimeD1StackBooleanTreeBounds.totalTime_le [true] (cached bits)
    unfold timeBound SemiprimeD1StackBooleanTreeBounds.runBound at *
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some]
    rcases hAt with ⟨hpc,hd,hframes⟩
    change C.step program finish=some (done bits)
    simp [C.step,SemiprimeD1StackCalls.step,hpc,program,C.execute,SemiprimeD1StackCalls.execute,hd,hframes,done]
end RiemannGaussian.SemiprimeD1StackZeroBoundaryTableExecution
