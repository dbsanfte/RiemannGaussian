/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationRow
/-! # Own physical-byte polynomial for the actual activation iteration
Every bound below closes clocks from the literal component executions. All
capacities are proof estimates; no capacity/clock enters source control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationBounds
open SemiprimeD1StackChildGroupFactory SemiprimeD1StackChildGroupFactoryActivationView
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace RowSource
export SemiprimeD1StackChildGroupFactoryActivationRow (timeBound)
end RowSource
/-- Selected field and unread suffix can never exceed their actual source row. -/
theorem colour_result_lengths (coordinate:Nat) (colours:List (List Bool)):
    (SemiprimeD1StackChildGroupFactoryColour.result coordinate colours).1.length≤(vectorBits colours).length ∧
    (SemiprimeD1StackChildGroupFactoryColour.result coordinate colours).2.length≤(vectorBits colours).length:=by
  induction coordinate generalizing colours with
  | zero=>
    cases colours with
    | nil=>simp [SemiprimeD1StackChildGroupFactoryColour.result,vectorBits]
    | cons w ws=>
      simp only [SemiprimeD1StackChildGroupFactoryColour.result,vectorBits,List.length_cons,
        SemiprimeSourceHistogramKeyBits.frame_length]
      omega
  | succ n ih=>
    cases colours with
    | nil=>simp [SemiprimeD1StackChildGroupFactoryColour.result,vectorBits]
    | cons w ws=>
      have h:=ih ws
      simp only [SemiprimeD1StackChildGroupFactoryColour.result,vectorBits,List.length_cons,
        SemiprimeSourceHistogramKeyBits.frame_length] at h ⊢
      omega
/-- One actual row's SAME-program trace has a fixed quadratic byte bound. -/
theorem timeBound_le (i:Inputs) (key selected unread:List Bool) (coordinate:Nat)
    (environment catalogue:List (List Bool×List Bool)) (colours:List (List Bool)) (S:Nat)
    (he:i.environment=SemiprimeD1StackOwnerLookup.records environment [])
    (hc:i.catalogue=SemiprimeD1StackOwnerLookup.records catalogue [])
    (hi:i.colourIndex=List.replicate coordinate true)
    (hr:SemiprimeD1StackPacketRowsAcquire.payload selected catalogue=SemiprimeD1PacketRows.serialize colours)
    (hs:1≤S) (hk:key.length+1≤S) (hid:selected.length+1≤S) (hu:unread.length+1≤S)
    (henv:i.environment.length+1≤S) (hcat:i.catalogue.length+1≤S)
    (hcoord:coordinate+1≤S) (hcol:(vectorBits colours).length+1≤S) (hg:i.group.length+1≤S):
    RowSource.timeBound i key selected unread coordinate environment catalogue colours≤100000000*S^2:=by
  have hen:(SemiprimeD1StackOwnerLookup.records environment []).length+1≤S:=by simpa only [he] using henv
  have hca:(SemiprimeD1StackOwnerLookup.records catalogue []).length+1≤S:=by simpa only [hc] using hcat
  have hm:=(Nat.mul_le_mul hk hen)
  have hl:=SemiprimeD1StackOwnerLookupBounds.time_le key environment
  unfold SemiprimeD1StackOwnerLookupBounds.runBound at hl
  have hlookup:SemiprimeD1StackOwnerLookupExecution.loopTime key environment+1≤100*S^2:=by
    nlinarith
  have hrow:=SemiprimeD1StackPacketRowsClock.timeBound_le selected selected catalogue colours colours hr hr rfl
  have hsize:(SemiprimeSourceHistogramKeyBits.frame selected selected).length+
      (SemiprimeD1StackOwnerLookup.records catalogue []).length+1≤4*S:=by
    rw [SemiprimeSourceHistogramKeyBits.frame_length]
    omega
  have hp:=Nat.pow_le_pow_left hsize 2
  unfold SemiprimeD1StackPacketRowsClock.polynomial SemiprimeD1StackPacketRowsClock.inputSize at hrow
  have hpaired:SemiprimeD1StackPacketRowsExecution.timeBound selected selected catalogue colours colours≤1600000*S^2:=by
    nlinarith
  have hlengths:=colour_result_lengths coordinate colours
  have hcolour:=SemiprimeD1StackChildGroupFactoryColour.time_le coordinate colours
  have hequal:=SemiprimeD1StackWordEqualExecution.executionTime_le
    ((SemiprimeD1StackChildGroupFactoryColour.result coordinate colours).1++[]) i.group
  simp only [List.append_nil] at hequal
  have hadd:=(SemiprimeBitArithmetic.addBits_counts key [true] false).2.2.2.2
  simp only [List.length_cons,List.length_nil] at hadd
  have hmax:max key.length 1≤S:=max_le (by omega) hs
  have hs2:S≤S^2:=Nat.le_pow (by decide:0<(2:Nat))
  dsimp only [RowSource.timeBound,
    SemiprimeD1StackChildGroupFactoryActivationLookup.budget,
    SemiprimeD1StackChildGroupFactoryActivationRows.budget,
    SemiprimeD1StackChildGroupFactoryActivationLog.budget,
    SemiprimeD1StackChildGroupFactoryActivationCleanup.budget,
    SemiprimeD1StackChildGroupFactoryActivationIncrement.budget]
  simp only [List.length_cons,List.length_nil,List.append_nil,hi,List.length_replicate,
    SemiprimeSourceHistogramKeyBits.frame_length]
  omega
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryActivationBounds
