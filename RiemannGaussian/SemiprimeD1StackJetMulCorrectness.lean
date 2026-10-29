/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetMulExecution
/-! # Exact whole-vector physical jet multiplication
The fixed machine consumes no coefficient/route catalogue or execution advice.
It runs its own physical output counter and the actual linked point procedure.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 8192
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackJetMulCorrectness
open SemiprimeD1StackJetMul SemiprimeD1StackJetMulExecution
open SemiprimeD1StackProcedureTrace (Runs runs_trans one_base At)
open SemiprimeD1StackJetPointExecution (Cache)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1JetAxes (Context)

/-- Descending physical prepend builds the original ascending coefficient order. -/
theorem rows_eq (ctx : Context) (a b : List (List Bool)) (n : ℕ) (tail : List (List Bool)) :
    rows ctx a b n tail=(List.range n).map (fun i=>(SemiprimeD1JetRingBits.mulAt ctx a b i).bits)++tail := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih => simp [rows,ih,List.range_succ,List.map_append,List.append_assoc]

/-- Whole output bytes are exactly the frozen dense multiplication bytes. -/
theorem rows_original (ctx : Context) (a b : List (List Bool)) :
    rows ctx a b ctx.rank []=(SemiprimeD1JetRingBits.mul ctx a b).words := by
  rw [rows_eq]
  simp [SemiprimeD1JetRingBits.mul,List.map_map,Function.comp_def]

/-- Initial real vector-nil emission and physical retained-rank copy. -/
theorem prepare_run (c : Cache) :
    Runs program (5*c.rank.length+5) .start (data c [] [] []) .loop (data c c.rank [] (vectorBits [])) := by
  have h1 : Runs program 1 .start (data c [] [] []) .copyRank (data c [] [] (vectorBits [])) := by
    apply one_base program .start .copyRank (.push output false .copyRank) _ _ rfl
    · rfl
    · exact data_output_update c [] [] [] [false]
  have h2:=rank_call c (vectorBits [])
  have h:=runs_trans program _ _ _ _ _ _ _ _ h1 h2
  simpa only [show 1+(5*c.rank.length+4)=5*c.rank.length+5 by omega] using h

/-- Original-data envelope from the actual fixed-vector traversal. -/
def totalClock (ctx : Context) (c : Cache) : ℕ := 5*c.rank.length+6+loopClock ctx c ctx.rank

/-- Closed actual whole-vector execution. Original coefficient arrays appear
only in the input/refinement relation, and every returned byte is acquired by
physical routing, reads, scalar arithmetic, reduction, framing and cleanup. -/
theorem source_run (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool))
    (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary)) (hwidth : c.width.length=ctx.precision)
    (hrank : c.rank=unary ctx.rank) :
    ∃ m ≤ totalClock ctx c,
      SemiprimeD1StackCalls.run program m (initial c.a c.b c.axes c.width c.rank)=
        some (⟨none,none,none,data c [] [] (vectorBits (SemiprimeD1JetRingBits.mul ctx a b).words),[]⟩:
          SemiprimeD1StackCalls.State Stack Label) := by
  have hprepare:=prepare_run c
  obtain ⟨ml,hl,hloop⟩:=loop_run ctx hp c a b ctx.rank [] ha hb haxes hwidth hrank
  rw [←hrank,rows_original] at hloop
  have h:=runs_trans program _ _ _ _ _ _ _ _ hprepare hloop
  have hinit : At .start (data c [] [] []) [] (initial c.a c.b c.axes c.width c.rank) :=
    ⟨rfl,initial_data c,rfl⟩
  obtain ⟨out,hout,hAt⟩:=h [] _ hinit
  have hhalt:=SemiprimeD1StackProcedureTrace.halt_run program .done rfl
    (data c [] [] (vectorBits (SemiprimeD1JetRingBits.mul ctx a b).words)) [] out hAt
  refine ⟨(5*c.rank.length+5)+ml+1,?_,?_⟩
  · unfold totalClock
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hout,Option.bind_some]
    exact hhalt

/-- Genuine actual compiled finite-stack dense multiplication certificate. -/
noncomputable def machineMultiply (ctx : Context) (hp : ctx.Positive) (c : Cache) (a b : List (List Bool))
    (ha : c.a=vectorBits a) (hb : c.b=vectorBits b)
    (haxes : c.axes=vectorBits (ctx.axes.map unary)) (hwidth : c.width.length=ctx.precision)
    (hrank : c.rank=unary ctx.rank) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial c.a c.b c.axes c.width c.rank))
      (some (SemiprimeD1StackCalls.configuration
        (⟨none,none,none,data c [] [] (vectorBits (SemiprimeD1JetRingBits.mul ctx a b).words),[]⟩:
          SemiprimeD1StackCalls.State Stack Label))) (totalClock ctx c) := by
  let h:=source_run ctx hp c a b ha hb haxes hwidth hrank
  let m:=Classical.choose h
  have hm:=Classical.choose_spec h
  apply SemiprimeD1StackCalls.evalsCorrect (.inl (P.aux .a)) output Label.start program
  exact ⟨⟨m,hm.2⟩,hm.1⟩

end RiemannGaussian.SemiprimeD1StackJetMulCorrectness
