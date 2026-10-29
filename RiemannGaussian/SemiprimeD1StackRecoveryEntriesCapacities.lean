/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesLoop
import RiemannGaussian.SemiprimeD1StackRecoveryEntriesIndexedBounds
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorCapacities
/-! # Intrinsic actual child/payload lengths and real row-step clocks
All estimates use actual source tape bytes. No recursive child runtime appears
in a cache-size premise or a source clock, so no depth-dependent exponent is introduced.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesCapacities
open SemiprimeD1StackRecoveryDenominatorEncoding (Row tape)
open SemiprimeD1StackRecoveryDenominatorCapacities (fieldMass)
open SemiprimeD1StackRecoveryEntriesEncoding (childTape selectedChild)
open SemiprimeD1StackRecoveryEntriesLoop (selectedRow clearMass)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeBitArithmetic (bitValue)
namespace B
export SemiprimeD1StackRecoveryEntriesIndexedBounds (timeBound_le result_length runBound)
end B
namespace R
export SemiprimeD1StackRecoveryEntriesRead (time outerBytes normalizeTime)
end R
namespace L
export SemiprimeD1StackRecoveryEntriesLogger (chunk rowTime frameTime payload)
end L
/-- Actual nested vector always carries its physical final false sentinel. -/
theorem child_tape_positive (children:List (List (List Bool))):1 ≤(childTape children).length:=by
  unfold childTape
  rw [SemiprimeD1TensorTapeCodec.vectorBits_length]
  omega
/-- Actual selected encoded child row, including the default empty row, is bounded by actual input bytes. -/
theorem row_cache_length (children:List (List (List Bool))) (node:List Bool):
    (vectorBits ((children[bitValue node]?).getD [])).length ≤(childTape children).length:=by
  cases hn:children[bitValue node]? with
  | none=>exact child_tape_positive children
  | some row=>
    have h:=B.result_length (children.map vectorBits) node
    rw [List.getElem?_map,hn,Option.map_some,Option.getD_some] at h
    exact h
/-- Actual selected coefficient or EOF default is a literal input payload, independent of every subtree clock. -/
theorem child_length (children:List (List (List Bool))) (node index:List Bool):
    (selectedChild children node index).length ≤(childTape children).length:=
  (B.result_length ((children[bitValue node]?).getD []) index).trans (row_cache_length children node)
/-- Physical peek and optional missing-row sentinel push take at most two actual steps. -/
theorem normalize_time (row:List Bool):R.normalizeTime row ≤2:=by cases row <;> simp only [R.normalizeTime] <;> decide
/-- Both actually executed binary-index sources and their real returns fit an actual-byte quadratic. -/
theorem read_time (children:List (List (List Bool))) (r:Row):
    R.time children r ≤3000000*((childTape children).length+fieldMass r+1)^2:=by
  let C:=(childTape children).length
  let S:=C+fieldMass r+1
  have h0:(r 0).length ≤fieldMass r:=by unfold fieldMass;omega
  have h1:(r 1).length ≤fieldMass r:=by unfold fieldMass;omega
  have hr:=row_cache_length children (r 0)
  have ho:=B.timeBound_le (children.map vectorBits) (r 0)
  have hi:=B.timeBound_le ((children[bitValue (r 0)]?).getD []) (r 1)
  have hqo:C+(r 0).length+1 ≤S:=by dsimp [S];omega
  have hqi:(vectorBits ((children[bitValue (r 0)]?).getD [])).length+(r 1).length+1 ≤S:=by dsimp [S,C];omega
  have ho':SemiprimeD1StackRecoveryEntriesIndexedExecution.timeBound (children.map vectorBits) (r 0) ≤1000000*S^2:=
    ho.trans (Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left hqo 2))
  have hi':SemiprimeD1StackRecoveryEntriesIndexedExecution.timeBound ((children[bitValue (r 0)]?).getD []) (r 1) ≤1000000*S^2:=
    hi.trans (Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left hqi 2))
  have hn:=normalize_time (R.outerBytes children (r 0))
  have hs:1 ≤S^2:=Nat.pow_pos (by dsimp [S];omega)
  unfold R.time
  change _ ≤3000000*S^2
  omega
/-- Exact number of physically framed bytes in one acquired four-field entry chunk. -/
theorem chunk_length (r:Row) (child:List Bool):
    (L.chunk r child).length=2*((r 2).length+(r 3).length+(r 4).length+child.length)+5:=by
  change (true::SemiprimeSourceHistogramKeyBits.frame (r 2)
    (SemiprimeSourceHistogramKeyBits.frame (r 3) (SemiprimeSourceHistogramKeyBits.frame (r 4)
      (SemiprimeSourceHistogramKeyBits.frame child [])))).length=_
  simp only [List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  omega
/-- Actual per-row logger cost is linear in its actual acquired fields, independent of history/output length. -/
theorem logger_time (children:List (List (List Bool))) (r:Row):
    L.rowTime r (selectedChild children (r 0) (r 1)) ≤100*((childTape children).length+fieldMass r+1):=by
  have hc:=child_length children (r 0) (r 1)
  have hl:=chunk_length r (selectedChild children (r 0) (r 1))
  unfold L.rowTime L.frameTime fieldMass
  omega
/-- Every physically logged entry chunk has a linear actual-input byte cap. -/
theorem chunk_bound (children:List (List (List Bool))) (r:Row):
    (L.chunk r (selectedChild children (r 0) (r 1))).length ≤5*((childTape children).length+fieldMass r+1):=by
  have hc:=child_length children (r 0) (r 1)
  rw [chunk_length]
  unfold fieldMass
  omega
/-- The seven actual metadata/cache/payload drains have no old-history term. -/
theorem clear_mass (children:List (List (List Bool))) (r:Row):
    clearMass r (selectedRow children r) (selectedChild children (r 0) (r 1)) ≤fieldMass r+2*(childTape children).length:=by
  have hr:=row_cache_length children (r 0)
  have hc:=child_length children (r 0) (r 1)
  unfold clearMass fieldMass selectedRow
  omega
/-- SAME actual complete row step is bounded by a fixed quadratic in acquired source/child bytes. -/
theorem row_time (children:List (List (List Bool))) (r:Row):
    SemiprimeD1StackRecoveryEntriesLoop.rowTime children r ≤10000000*((childTape children).length+fieldMass r+1)^2:=by
  have hp:SemiprimeD1StackRecoveryEntriesFields.time r=8*fieldMass r+40:=rfl
  have hr:=read_time children r
  have hl:=logger_time children r
  have hc:=clear_mass children r
  let S:=(childTape children).length+fieldMass r+1
  have hpos:1 ≤S:=by dsimp [S];omega
  have hself:S ≤S^2:=by simpa only [pow_one] using Nat.pow_le_pow_right hpos (by decide:1 ≤2)
  unfold SemiprimeD1StackRecoveryEntriesLoop.rowTime
  rw [hp]
  change _ ≤10000000*S^2
  change R.time children r ≤3000000*S^2 at hr
  change L.rowTime r (selectedChild children (r 0) (r 1)) ≤100*S at hl
  have hrest:8*fieldMass r+40+clearMass r (selectedRow children r) (selectedChild children (r 0) (r 1))+8 ≤100*S:=by dsimp [S];omega
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesCapacities
