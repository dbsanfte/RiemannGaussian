/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputTable
import RiemannGaussian.SemiprimeD1StackStaticWordTableSpec
import RiemannGaussian.SemiprimeD1StackPublicInputTableTrace
/-! # The actual compact66 trace discharges the whole-table leaf contract -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableTrace
open SemiprimeD1StackMarkedPublicInputTable SemiprimeD1StackStaticWordTableSpec
/-- Exact physically compacted coefficient specification, not a runtime supplier. -/
def answer (bits indexWord : List Bool) (side : Bool) (raw : List Bool) : List Bool :=
  P.coefficient bits raw indexWord side
/-- Uniform paid actual source allowance, depending on raw byte LENGTH only. -/
def budget (bits indexWord : List Bool) (width : Nat) : Nat :=
  10000000000000000*(bits.length+width+indexWord.length+2)^2
/-- Actual template/raw delivery gives the ordinary real compact source input. -/
theorem initial_eq (bits raw indexWord : List Bool) (side : Bool) :
    checkerInitial static (inputTemplate bits indexWord side) raw=P.initial bits raw indexWord side := by
  exact congrArg (fun d => (⟨some (SemiprimeD1StackMarkedPublicInputCompact.ctl .start),none,none,d,[]⟩ :
    SemiprimeD1StackCalls.State P.Stack P.Label)) (template_raw_update bits raw indexWord side)
/-- Every leaf contract is DISCHARGED by the known66 source plus actual reverse/trim. -/
theorem actual_trace (bits indexWord : List Bool) (side : Bool) (hb : bits≠[]) :
    CheckerTrace static (inputTemplate bits indexWord side) (answer bits indexWord side) (budget bits indexWord) := by
  intro raw
  obtain ⟨t,ht,hr⟩ := SemiprimeD1StackMarkedPublicInputCompactBounds.source_run_bounded bits raw indexWord side hb
  refine ⟨t,ht,SemiprimeD1StackMarkedPublicInputCompact.done bits raw indexWord side,rfl,rfl,?_,rfl⟩
  rw [initial_eq]
  exact hr
/-- Each initialized template field consists solely of actual original input bytes. -/
theorem template_cell_le (bits indexWord : List Bool) (side : Bool) (k : P.Stack) :
    (inputTemplate bits indexWord side k).length ≤ bits.length+indexWord.length+1 := by
  rcases k with k|k
  · exact (SemiprimeD1StackPublicInputBounds.initial_length bits [] indexWord k).trans
      (by simp only [List.length_nil,Nat.add_zero];omega)
  · rcases k with k|k
    · exact Nat.zero_le _
    · rcases k with k|k
      · cases k <;> exact Nat.zero_le _
      · cases k <;> first | exact Nat.zero_le _ | change 1≤bits.length+indexWord.length+1;omega
/-- All66 readonly words are counted, including physically empty private/shadow roles. -/
theorem template_total_le (bits indexWord : List Bool) (side : Bool) :
    inputBytes (inputTemplate bits indexWord side) ≤ 66*(bits.length+indexWord.length+1) := by
  calc
    _ ≤ ∑ _k : P.Stack, (bits.length+indexWord.length+1) :=
      Finset.sum_le_sum (fun k _ => template_cell_le bits indexWord side k)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,
      SemiprimeD1StackMarkedPublicInputCompact.stack_card,smul_eq_mul]
/-- Only N, actual index and physical side are nonempty; no metadata or answer is in the template. -/
theorem template_only (bits indexWord : List Bool) (side : Bool) (k : P.Stack) :
    inputTemplate bits indexWord side k=
      if k=M.checker (.inl SemiprimeD1StackPublicInputWidth.original) then bits
      else if k=M.checker SemiprimeD1StackPublicInput.index then indexWord
      else if k=M.aux .side then [side] else [] := by
  rcases k with k|k
  · change SemiprimeD1StackPublicInputTable.inputTemplate bits indexWord k=_
    rw [SemiprimeD1StackPublicInputTableTrace.template_only bits indexWord k]
    simp only [M.checker,M.aux,Sum.inl.injEq,Sum.inl_ne_inr,ite_false]
  · rcases k with k|k
    · fin_cases k <;> rfl
    · rcases k with k|k <;> cases k <;> rfl
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableTrace

