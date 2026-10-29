/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableBootstrap
import RiemannGaussian.SemiprimeD1StackProductTableDFS
/-! # Complete original-binary-N product-table source execution
The actual bootstrap acquires its own arity; the actual DFS calls the original
checker on every acquired assignment and clears all76 roles between leaves;
the actual final reversal writes the exact complete old-codec output tape.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableExecution
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableState SemiprimeD1StackProductTableSpec
open SemiprimeD1StackProcedureTrace
namespace B
export SemiprimeD1StackProductTableBootstrap (bootstrapBound bootstrap_run)
end B
namespace D
export SemiprimeD1StackProductTableDFS (weight visit_returns)
end D
/-- Exact final physical store: original N/acquired depth retained, output tape
materialized, every checker role and every temporary/source workspace cleared. -/
def result (bits : List Bool) : Stack→List Bool :=Function.update (data bits (arity bits) [] []) (.inr .output) (outputTape bits)
/-- The actual whole-source halt clears all finite transient and return flags. -/
def done (bits : List Bool) : C.State Stack Label :=⟨none,none,none,result bits,[]⟩
/-- Real final consuming reversal, including actual call/return and EVERY byte. -/
theorem reverse_table (bits : List Bool) :
    Runs program (2*(outputTape bits).length+3) .finish
      (data bits (arity bits) [] (outputTape bits).reverse) .done (result bits) := by
  have h:=SemiprimeD1StackProductTablePrimitives.reverse_call .table .finish .done rfl
    (data bits (arity bits) [] (outputTape bits).reverse)
  have hd:Function.update (data bits (arity bits) [] (outputTape bits).reverse) (.inr .reversed) []=
      data bits (arity bits) [] [] := by
    funext k
    cases k with
    | inl k=>rfl
    | inr k=>cases k <;> rfl
  change Runs program (2*(outputTape bits).reverse.length+3) .finish
    (data bits (arity bits) [] (outputTape bits).reverse) .done
    (Function.update (Function.update (data bits (arity bits) [] (outputTape bits).reverse) (.inr .reversed) [])
      (.inr .output) ((outputTape bits).reverse.reverse++[])) at h
  rw [List.length_reverse,List.reverse_reverse,List.append_nil,hd] at h
  exact h
/-- Closed SAME-source clock; no old/native constructor report is transported. -/
def timeBound (bits : List Bool) : ℕ :=B.bootstrapBound bits+D.weight bits (arity bits)*2^(arity bits)+2*(outputTape bits).length+5
/-- COMPLETE original-N-only actual source. There is NO supplied arity, raw
assignment, modulus, table, entry stream, evaluator, result or elapsed clock.
All physical N-acquisition, DFS, arithmetic, cleanup and codec work is retained. -/
theorem source_run (bits : List Bool) (hb : bits≠[]) :
    ∃t≤timeBound bits,C.run program t (initial bits)=some (done bits) := by
  obtain ⟨a,ha,h0⟩:=B.bootstrap_run bits hb
  obtain ⟨b,hbTime,hvisit⟩:=D.visit_returns bits hb (arity bits) [] []
  simp only [List.length_nil,Nat.zero_add,List.reverse_nil,List.append_nil] at hbTime hvisit
  have h1:=SemiprimeD1StackProcedureReturns.call program b .build .visit .finish
    _ _ rfl hvisit
  have h2:=reverse_table bits
  have h:=runs_trans program _ _ _ _ _ _ _ _ h0 (runs_trans program _ _ _ _ _ _ _ _ h1 h2)
  obtain ⟨finish,hfinish,hout⟩:=h [] (initial bits) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program .done rfl (result bits) [] finish hout
  refine ⟨a+((1+b)+(2*(outputTape bits).length+3))+1,?_,?_⟩
  · unfold timeBound
    omega
  · rw [SemiprimeD1StackReturnLink.run_add,hfinish,Option.bind_some,hh]
    rfl
/-- The actual completed output is the complete original-order product table. -/
theorem output_table (bits : List Bool) : (done bits).data (.inr .output)=outputTape bits := rfl
/-- The actual original binary input is retained exactly, rather than reencoded. -/
theorem retained_N (bits : List Bool) : (done bits).data (.inr .source)=bits := rfl
/-- Only the actual acquired depth remains as unary metadata. -/
theorem retained_depth (bits : List Bool) :
    (done bits).data (.inr .depth)=SemiprimeD1StackUnaryDivmod.unary (arity bits) := rfl
end RiemannGaussian.SemiprimeD1StackProductTableExecution
