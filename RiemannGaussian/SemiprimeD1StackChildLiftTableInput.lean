/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildLiftTable
/-! # Exact Entry61 initialization and own bit budget at every actual table leaf -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildLiftTableInput
open SemiprimeD1StackChildLiftTable
open SemiprimeD1TensorTapeCodec (tape vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)
namespace V
export SemiprimeD1StackVectorTableSpec (CheckerTrace checkerInitial)
end V
/-- Six actual source words are retained in the template; the assignment role starts EMPTY. -/
def original (table order oldAxes oldp newAxes newp : List Bool) : E.Stack→List Bool :=
  (E.initial table order [] oldAxes oldp newAxes newp).data
/-- The source's actual physical raw-assignment role is empty before each real reversal. -/
theorem raw_empty (table order oldAxes oldp newAxes newp : List Bool) :
    original table order oldAxes oldp newAxes newp source.raw=[] := rfl
/-- One physical assignment update changes exactly the intended Entry61 input. -/
theorem assignment_update (table order oldAxes oldp newAxes newp raw : List Bool) :
    Function.update (original table order oldAxes oldp newAxes newp) (E.gather .assignment) raw=
      (E.initial table order raw oldAxes oldp newAxes newp).data := by
  funext k
  rcases k with k|k|k|k|k|k
  · rfl
  · rfl
  · cases k <;> rfl
  · rfl
  · rfl
  · rfl
/-- The actual copied/reversed leaf entry is the whole physical source's original seven-word front door. -/
theorem checker_initial (table order oldAxes oldp newAxes newp raw : List Bool) :
    V.checkerInitial source (original table order oldAxes oldp newAxes newp) raw=
      E.initial table order raw oldAxes oldp newAxes newp := by
  change (⟨some (.local .start),none,none,
    Function.update (original table order oldAxes oldp newAxes newp) (E.gather .assignment) raw,[]⟩ :
      SemiprimeD1StackCalls.State E.Stack E.Label)=E.initial table order raw oldAxes oldp newAxes newp
  rw [assignment_update]
  rfl
/-- Every leaf has the SAME own physical input-byte/rank/precision resource, with assignment length charged. -/
def budget {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (table : SemiprimeD1TensorTables.Table d) (order : List ℕ) (n : ℕ) : ℕ :=
  SemiprimeD1StackChildTableEntryClock.wholePolynomial old.axes (extra++old.axes) oldp newp table order
    (List.replicate n false)
/-- Only physical assignment length is replaced in this SAME own-source budget. -/
theorem budget_exact {d : ℕ} (old : SemiprimeD1JetAxes.Context) (extra : List ℕ) (oldp newp : List Bool)
    (table : SemiprimeD1TensorTables.Table d) (order : List ℕ) (raw : List Bool) :
    budget old extra oldp newp table order raw.length=
      SemiprimeD1StackChildTableEntryClock.wholePolynomial old.axes (extra++old.axes) oldp newp table order raw := by
  simp only [budget,SemiprimeD1StackChildTableEntryClock.wholePolynomial,
    SemiprimeD1StackChildTableEntryBounds.resource,List.length_replicate]
/-- The concrete physical Entry61 proves EVERY leaf trace; no entry evaluator or answer is input. -/
theorem source_trace {d : ℕ} (old : SemiprimeD1JetAxes.Context) (ho : old.Positive)
    (extra : List ℕ) (he : 0<extra.prod) (oldp newp : List Bool)
    (hp : SemiprimeBitArithmetic.bitValue oldp=old.precision)
    (table : SemiprimeD1TensorTables.Table d) (hg : SemiprimeD1TensorTables.Good old table) (order : List ℕ) :
    V.CheckerTrace source
      (original (tape table) (SemiprimeD1StackChildTableEntryPrepare.orderTape order)
        (vectorBits (old.axes.map unary)) oldp (vectorBits ((extra++old.axes).map unary)) newp)
      (fun raw => (SemiprimeD1ChildTableCopyTape.entry old extra (SemiprimeBitArithmetic.bitValue newp) table order raw).words)
      (budget old extra oldp newp table order) := by
  intro raw
  obtain ⟨t,ht,hr,hout,_⟩ := SemiprimeD1StackChildTableEntryOriginal.source_run_original_bounded
    old ho extra he oldp newp hp table hg order raw
  refine ⟨t,?_,SemiprimeD1StackChildTableEntryEncoding.done old.axes (extra++old.axes)
    oldp newp (tape table) (SemiprimeD1StackChildTableEntryPrepare.orderTape order) raw
      (SemiprimeD1StackChildTableEntryPrepare.selected table raw order),rfl,rfl,?_,hout⟩
  · rw [budget_exact]
    exact ht
  · rw [checker_initial]
    exact hr
end RiemannGaussian.SemiprimeD1StackChildLiftTableInput
