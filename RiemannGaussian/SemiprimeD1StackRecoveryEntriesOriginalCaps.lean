/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesOriginalRows
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorCapacities
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesBounds
/-! # Original semantic row/child byte envelopes, independent of subtree clocks
Canonical row labels/counts/widths and child count/rank/precision alone bound
the two physical input tapes. No recursive child's runtime enters the envelope.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesOriginalCaps
open SemiprimeD1StackRecoveryEntriesOriginalRows
open SemiprimeD1StackRecoveryDenominatorCapacities
open SemiprimeD1StackRecoveryEntriesEncoding (childTape)
namespace Rows
export SemiprimeD1RecoveryRowsBits (Row pack gather acquire node_length)
end Rows
/-- Every actual packed row carries the original node and a genuine local index. -/
theorem pack_addresses (node index:Nat) (words:List SemiprimeRationalBits.RationalWord):
    ∀r∈(Rows.pack node index words).rows,r.node=node ∧r.index < index+words.length:=by
  induction words generalizing index with
  | nil=>intro r hr;cases hr
  | cons word words ih=>
    intro r hr
    simp only [Rows.pack,List.mem_cons] at hr
    rcases hr with rfl|hr
    · constructor
      · rfl
      · simp only [List.length_cons];omega
    · have h:=ih (index+1) r hr
      simp only [List.length_cons]
      exact ⟨h.1,by omega⟩
/-- Original canonical-row labels are bounded by original grid count and multiplicity, never a child runtime. -/
theorem gather_addresses (a M u:Nat) (ts:List (Fin (SemiprimeD1WireKernelOriginal.size a))) (hM:u ≤M):
    ∀r∈(Rows.gather a M u ts).rows,r.node<SemiprimeD1WireKernelOriginal.size a ∧r.index<4*M:=by
  induction ts with
  | nil=>intro r hr;cases hr
  | cons t ts ih=>
    intro r hr
    simp only [Rows.gather] at hr
    split_ifs at hr
    · exact ih r hr
    · simp only [List.mem_append] at hr
      rcases hr with hr|hr
      · have hp:=pack_addresses t.val 0 (SemiprimeD1RecoveryNodeBits.acquire a M u t).words r hr
        have hl:(SemiprimeD1RecoveryNodeBits.acquire a M u t).words.length ≤4*M:=by
          rw [Rows.node_length a M u t hM]
          exact SemiprimeD1WeightPrecision.nodeMultiplicity_le a M u t.val hM
        exact ⟨by rw [hp.1];exact t.isLt,lt_of_lt_of_le (by simpa only [Nat.zero_add] using hp.2) hl⟩
      · exact ih r hr
/-- Actual original row-address bytes have source-derived finite label bounds. -/
theorem original_addresses (a M u:Nat) (hM:u ≤M):
    ∀r∈(Rows.acquire a M u).rows,r.node<SemiprimeD1WireKernelOriginal.size a ∧r.index<4*M:=
  gather_addresses a M u _ hM
/-- All5 actual canonical-row source payloads have a semantic byte bound before any recursive child runtime. -/
theorem original_field_mass (a M u:Nat) (hM:u ≤M):
    ∀r∈D.originalRows a M u,
      fieldMass r ≤SemiprimeD1WireKernelOriginal.size a+4*M+2*SemiprimeD1RecoveryNodeBits.width a M+1:=by
  intro encoded he
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp he
  have ha:=original_addresses a M u hM r hr
  have hw:=original_payload_width a M u hM r hr
  change (SemiprimeEncodedRowSelection.digits (r.node+1) r.node).bits.length+
    (SemiprimeEncodedRowSelection.digits (r.index+1) r.index).bits.length+
      1+r.word.numerator.magnitude.length+r.word.denominator.length ≤_
  rw [SemiprimeEncodedRowSelection.digits_length,SemiprimeEncodedRowSelection.digits_length]
  omega
/-- Complete row payload sum is paid by actual canonical-row inventory and source field widths. -/
theorem payload_mass_bound (rows:List SemiprimeD1StackRecoveryDenominatorEncoding.Row) (cap:Nat)
    (h:∀r∈rows,fieldMass r ≤cap):payloadMass rows ≤rows.length*cap:=by
  induction rows with
  | nil=>simp only [payloadMass,List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons r rows ih=>
    have h0:=h r (List.mem_cons_self)
    have h1:=ih (fun s hs=>h s (List.mem_cons_of_mem r hs))
    dsimp only [payloadMass] at h1 ⊢
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega
/-- Original input-row byte cap from canonical count, actual binary metadata fields and physical word widths. -/
def rowByteBound (a M:Nat):Nat:=
  (SemiprimeD1WireKernelOriginal.size a*(4*M))*
    (2*(SemiprimeD1WireKernelOriginal.size a+4*M+2*SemiprimeD1RecoveryNodeBits.width a M+1)+6)+1
/-- Row-tape byte bound derives from original canonical source structure, with no row-generator clock transport. -/
theorem original_row_bytes (a M u:Nat) (hM:u ≤M):
    (SemiprimeD1StackRecoveryDenominatorEncoding.tape (D.originalRows a M u)).length ≤rowByteBound a M:=by
  have hp:=payload_mass_bound (D.originalRows a M u) _ (original_field_mass a M u hM)
  have hn:=original_count a M u hM
  have ht:=tape_length (D.originalRows a M u)
  have hm:=Nat.mul_le_mul_right (2*(SemiprimeD1WireKernelOriginal.size a+4*M+2*SemiprimeD1RecoveryNodeBits.width a M+1)+6) hn
  unfold rowByteBound
  nlinarith only [hp,ht,hm]
/-- Actual nested cache byte bound uses only semantic count/rank/precision. -/
def childByteBound (Q R P:Nat):Nat:=4*Q*R*(P+1)+4*Q+1
/-- Whole original two-tape byte cap is independent of every recursive subtree runtime. -/
def byteEnvelope (a M Q R P:Nat):Nat:=rowByteBound a M+childByteBound Q R P
/-- Actual original two-input byte resource is bounded from canonical rows and GoodWords-style semantic child caps. -/
theorem original_resource (a M u Q R P:Nat) (hM:u ≤M) (children:List (List (List Bool)))
    (hq:children.length ≤Q) (hr:∀row∈children,row.length ≤R) (hp:∀row∈children,∀word∈row,word.length ≤P):
    SemiprimeD1StackRecoveryEntriesBounds.resource (D.originalRows a M u) children ≤byteEnvelope a M Q R P:=by
  have h0:=original_row_bytes a M u hM
  have h1:=SemiprimeD1StackRecoveryEntriesChildCaps.child_tape_length children Q R P hq hr hp
  unfold SemiprimeD1StackRecoveryEntriesBounds.resource byteEnvelope childByteBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesOriginalCaps
