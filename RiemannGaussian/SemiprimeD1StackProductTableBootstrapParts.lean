/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackProductTableState
/-! # Actual product-table arity acquisition from the retained binary M word
The word VALUE never becomes an arity. Three real copies/scans count its
physical cells, including every zero bit, by pushing actual depth markers.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackProductTableBootstrapParts
open SemiprimeD1StackProductTable SemiprimeD1StackProductTableState
open SemiprimeD1StackProcedureTrace
open SemiprimeD1StackPublicProductExecution (context cached)
/-- Actual acquired public bank and otherwise empty reusable checker bank. -/
def checker (bits : List Bool) : P.Stack→List Bool :=Sum.elim (context bits) (fun _=>[])
/-- Correctness view of actual acquired caches, actual depth and scanned word. -/
def bootData (bits : List Bool) (depth : ℕ) (work : List Bool) : Stack→List Bool :=
  Function.update (withChecker (data bits depth [] []) (checker bits)) (.inr .work) work
/-- Every actual copied modulus cell contributes exactly one real depth marker. -/
def scanNext (pass : Fin 3) : Label :=
  if h:pass.val<2 then .arityCopy ⟨pass.val+1,by omega⟩ else .bootstrapClear
/-- Real physical fragment composition for the same source code. -/
theorem chain {m n : ℕ} {pc mid next : Label} {input middle output : Stack→List Bool}
    (h : Runs program m pc input mid middle) (g : Runs program n mid middle next output) :
    Runs program (m+n) pc input next output := runs_trans program _ _ _ _ _ _ _ _ h g
/-- Complete real word scan, accepting EVERY marker bit pattern, with no supplied
word length/count. Only the actual input EOF selects the next fixed pass. -/
theorem scan_run (pass : Fin 3) (bits : List Bool) (depth : ℕ) (work : List Bool) :
    Runs program (2*work.length+1) (.arityScan pass) (bootData bits depth work)
      (scanNext pass) (bootData bits (depth+work.length) []) := by
  induction work generalizing depth with
  | nil=>
    apply one_base program (.arityScan pass) (scanNext pass)
      (.pop (.inr .work) (scanNext pass) (.arityPush pass) (.arityPush pass)) _ _ rfl
    · rfl
    · funext k
      cases k with
      | inl k=>rfl
      | inr k=>cases k <;> rfl
  | cons b work ih=>
    have h0 : Runs program 1 (.arityScan pass) (bootData bits depth (b::work))
        (.arityPush pass) (bootData bits depth work) := by
      apply one_base program (.arityScan pass) (.arityPush pass)
        (.pop (.inr .work) (scanNext pass) (.arityPush pass) (.arityPush pass)) _ _ rfl
      · cases b <;> rfl
      · funext k
        cases k with
        | inl k=>rfl
        | inr k=>cases k <;> rfl
    have h1 : Runs program 1 (.arityPush pass) (bootData bits depth work)
        (.arityScan pass) (bootData bits (depth+1) work) := by
      apply one_base program (.arityPush pass) (.arityScan pass)
        (.push (.inr .depth) true (.arityScan pass)) _ _ rfl
      · rfl
      · funext k
        cases k with
        | inl k=>rfl
        | inr k=>cases k <;> rfl
    have h:=chain h0 (chain h1 (ih (depth+1)))
    have ht:1+(1+(2*work.length+1))=2*(b::work).length+1 := by simp only [List.length_cons];omega
    have hd:depth+1+work.length=depth+(b::work).length := by simp only [List.length_cons];omega
    rw [ht,hd] at h
    exact h
/-- A real preserving copy of the ACTUALLY acquired binary M word, whose physical
length is then scanned; no modulus/width/value supplier is an initial operand. -/
theorem copy_arity (pass : Fin 3) (bits : List Bool) (depth : ℕ) :
    Runs program (5*(cached bits).length+4) (.arityCopy pass) (bootData bits depth [])
      (.arityScan pass) (bootData bits depth (cached bits)) := by
  have h:=SemiprimeD1StackProductTablePrimitives.copy_call .arity (.arityCopy pass) (.arityScan pass)
    rfl (bootData bits depth []) rfl rfl
  change Runs program (5*(cached bits).length+4) (.arityCopy pass) (bootData bits depth [])
    (.arityScan pass) (Function.update (bootData bits depth []) (.inr .work) (cached bits)) at h
  simpa only [bootData,Function.update_idem] using h
/-- All copy/scan/EOF work in one fixed physical pass. -/
theorem arity_round (pass : Fin 3) (bits : List Bool) (depth : ℕ) :
    Runs program (7*(cached bits).length+5) (.arityCopy pass) (bootData bits depth [])
      (scanNext pass) (bootData bits (depth+(cached bits).length) []) := by
  have h:=chain (copy_arity pass bits depth) (scan_run pass bits depth (cached bits))
  have ht:(5*(cached bits).length+4)+(2*(cached bits).length+1)=7*(cached bits).length+5 := by omega
  rw [ht] at h
  exact h
/-- THREE actual scans acquire the complete three-word product arity, preserving
the entire actual public bank. Their fixed finite pass labels contain no n. -/
theorem arity_run (bits : List Bool) :
    Runs program (3*(7*(cached bits).length+5)) (.arityCopy 0) (bootData bits 0 [])
      .bootstrapClear (bootData bits (SemiprimeD1StackProductTableSpec.arity bits) []) := by
  have h0:=arity_round 0 bits 0
  have h1:=arity_round 1 bits (0+(cached bits).length)
  have h2:=arity_round 2 bits (0+(cached bits).length+(cached bits).length)
  have h:=chain h0 (chain h1 h2)
  have ht:(7*(cached bits).length+5)+((7*(cached bits).length+5)+(7*(cached bits).length+5))=
      3*(7*(cached bits).length+5) := by omega
  have hd:0+(cached bits).length+(cached bits).length+(cached bits).length=
      SemiprimeD1StackProductTableSpec.arity bits := by unfold SemiprimeD1StackProductTableSpec.arity;omega
  rw [ht,hd] at h
  exact h
/-- Physically draining the public/checker bank retains the acquired depth. -/
theorem clean_bootData (bits : List Bool) (depth : ℕ) :
    SemiprimeD1StackProductTableCleanup.clean (bootData bits depth [])=data bits depth [] [] := by
  funext k
  cases k with
  | inl k=>rfl
  | inr k=>cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackProductTableBootstrapParts
