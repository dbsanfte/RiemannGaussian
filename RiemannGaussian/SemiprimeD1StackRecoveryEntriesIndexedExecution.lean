/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedLoop
/-! # Whole real binary-query defaulting vector reader and exact retained inputs
The fixed program preserves the two actual input words, clears all private
work and returns the exact selected literal field, defaulting at actual EOF.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedExecution
open SemiprimeD1StackRecoveryEntriesIndexed SemiprimeD1StackRecoveryEntriesIndexedState
open SemiprimeD1StackRecoveryEntriesIndexedPrimitives SemiprimeD1StackRecoveryEntriesIndexedSpec
open SemiprimeD1StackRecoveryEntriesIndexedLoop SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeBitArithmetic (bitValue)
/-- Exact actual two-input source clock, including retained vector copy and genuine halt. -/
def timeBound (words:List (List Bool)) (query:List Bool):Nat:=5*(vectorBits words).length+4+budget query [] words+1
/-- Actual full halt retains raw query padding and raw cache payload, clearing all private/counter words. -/
def done (words:List (List Bool)) (query:List Bool):C.State Stack Label:=
  ⟨none,none,none,view (vectorBits words) query [] [] ((words[bitValue query]?).getD []),[]⟩
/-- One real preserving input copy enters the physical scan with binary zero ordinal. -/
theorem setup_run (cache query:List Bool):
    Runs program (5*cache.length+4) (.local .start) (initial cache query).data (.local .loop) (view cache query [] cache []):=by
  rw [initial_store]
  have h:=copy_call .cache (.local .start) (.local .loop) (view cache query [] [] []) cache [] rfl rfl rfl rfl
  simp only [List.append_nil] at h
  dsimp only [view,copyTarget,aux] at h
  rw [update_reader] at h
  exact h
/-- SAME finite program returns the exact original index/default semantics, without a getter or unary address supplier. -/
theorem source_run (words:List (List Bool)) (query:List Bool):
    SemiprimeD1StackCalls.run program (timeBound words query) (initial (vectorBits words) query)=some (done words query):=by
  have h0:=setup_run (vectorBits words) query
  have h1:=loop_run words (vectorBits words) query []
  rw [selected_initial] at h1
  have h:=join h0 h1
  obtain ⟨out,hr,ha⟩:=h [] (initial (vectorBits words) query) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (.local .done) rfl (done words query).data [] out ha
  rw [timeBound,SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  exact hh
/-- Exact all12-role final bank: both originals retained and nine private work tapes empty. -/
theorem result_bank (words:List (List Bool)) (query:List Bool):
    (done words query).data=Function.update (input (vectorBits words) query) (aux .value) ((words[bitValue query]?).getD []):=by
  funext k
  rcases k with k|k
  · cases k <;> rfl
  · cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedExecution
