/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesChildCaps
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorOriginal
/-! # Exact original recovery-entry bytes and semantic count/precision caps
The legacy canonical rows specify the actual five-field source tape in proofs;
they are not runtime inputs or a claimed canonical-row producer. Child caps
use actual coefficient widths only, never recursive child execution budgets.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesOriginalRows
open SemiprimeD1StackRecoveryEntriesEncoding
namespace D
export SemiprimeD1StackRecoveryDenominatorOriginal (encodeRow originalRows)
end D
namespace Up
export SemiprimeD1RecoveryPhysicalRun (entries entries_child_length)
end Up
namespace R
export SemiprimeD1RecoveryRowsBits (Row acquire acquire_length acquire_good)
end R
namespace I
export SemiprimeD1RecoveryIntegerBits (Entry)
end I
/-- Exact four-field old entry payload, retaining raw numerator sign/padding and child padding. -/
def encodeEntry (e:I.Entry):Entry:=![[e.numerator.negative],e.numerator.magnitude,e.denominator,e.child]
/-- A canonical source row's actual child field equals the original physical two-level cache read. -/
theorem entry_row (children:List (List (List Bool))) (r:R.Row):
    entry children (D.encodeRow r)=encodeEntry ⟨r.word.numerator,r.word.denominator,
      (SemiprimeD1RecoveryChildBits.read children
        (SemiprimeEncodedRowSelection.digits (r.node+1) r.node).bits
        (SemiprimeEncodedRowSelection.digits (r.index+1) r.index).bits).bits⟩:=by
  funext part;fin_cases part
  · rfl
  · rfl
  · rfl
  · exact (SemiprimeD1RecoveryChildBits.read_bits children _ _).symm
/-- Every old recovery row, including repeats, zeros and missing-cache defaults, occurs in exactly original order. -/
theorem entries_rows (children:List (List (List Bool))) (rows:List R.Row):
    (rows.map D.encodeRow).map (entry children)=(Up.entries children rows).entries.map encodeEntry:=by
  induction rows with
  | nil=>rfl
  | cons r rows ih=>
    simp only [List.map_cons,Up.entries]
    rw [entry_row,ih]
/-- The actual output byte tape is EXACT the old physical entries payload, not merely its values. -/
theorem output_rows (children:List (List (List Bool))) (rows:List R.Row):
    outputTape (rows.map D.encodeRow) children=records ((Up.entries children rows).entries.map encodeEntry):=by
  unfold outputTape
  rw [entries_rows]
/-- Original actual entry count derives from the canonical acquired row inventory. -/
theorem original_count (a M u:Nat) (hM:u ≤M):
    (D.originalRows a M u).length ≤SemiprimeD1WireKernelOriginal.size a*(4*M):=by
  simpa only [D.originalRows,List.length_map] using R.acquire_length a M u hM
/-- Actual output child widths derive only from literal input coefficient precision. -/
theorem original_child_precision (a M u P:Nat) (children:List (List (List Bool)))
    (hp:∀row∈children,∀word∈row,word.length ≤P):
    ∀e∈(Up.entries children (R.acquire a M u).rows).entries,e.child.length ≤P:=
  Up.entries_child_length children _ P hp
/-- Every original row numerator/denominator payload has its acquired canonical-node width, without a child-clock bound. -/
theorem original_payload_width (a M u:Nat) (hM:u ≤M):
    ∀r∈(R.acquire a M u).rows,
      r.word.numerator.magnitude.length ≤SemiprimeD1RecoveryNodeBits.width a M ∧
      r.word.denominator.length ≤SemiprimeD1RecoveryNodeBits.width a M:=
  (R.acquire_good a M u hM).2
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesOriginalRows
