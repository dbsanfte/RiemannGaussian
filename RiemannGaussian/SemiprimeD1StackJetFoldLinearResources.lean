/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldResources
/-! # Actual all111-role storage is also polynomial per actual fold node -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldLinearResources
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldWords SemiprimeD1StackJetFoldSpec
open SemiprimeD1StackJetFoldContext SemiprimeD1StackJetFoldBounds SemiprimeD1StackJetFoldResources
open SemiprimeD1StackJetFoldInputBounds SemiprimeD1StackJetFoldOperatorBounds
/-- Actual retained original inputs and acquired counters are part of the physical metadata inventory. -/
theorem ready_inventory (axes:List Nat) (precision:List Bool) (modes:Modes):
    readyCells axes precision modes ≤ metaSize (context axes precision)
      (acquiredHeader axes precision (modeTape modes))+(modeTape modes).length:=by
  dsimp only [readyCells,inputCells,metaSize,context,acquiredHeader]
  omega
/-- All ready input/cached bytes are linear in actual fold nodes and actual largest field/value capacity. -/
theorem readyCells_le (axes:List Nat) (precision:List Bool) (modes:Modes):
    readyCells axes precision modes ≤5*(resource axes precision modes+1)*workNodes modes:=by
  let S:=resource axes precision modes
  have hm:metaSize (context axes precision) (acquiredHeader axes precision (modeTape modes)) ≤ S:=meta_le _ _ _
  have ht:childMax modes ≤ S:=max_le_capacity _ _ _
  have hbytes:=modeTape_length modes S ht
  have hn:=nodes_positive modes
  have hS:S ≤(S+1)*workNodes modes:=by
    have h:S+1 ≤(S+1)*workNodes modes:=by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (S+1) hn
    omega
  have hi:=ready_inventory axes precision modes
  change _ ≤5*(S+1)*workNodes modes
  nlinarith only [hm,hbytes,hS,hi]
/-- One actual linear byte factor fits the fixed physical operator polynomial. -/
theorem linear_round (S:Nat):S+1 ≤ roundCap S:=by
  calc
    _ ≤(S+1)^6:=linear_le_sixth S
    _ ≤ roundCap S:=by unfold roundCap;simpa only [Nat.one_mul] using
      Nat.mul_le_mul_right ((S+1)^6) (by decide:1 ≤1000000000000)
/-- Fixed complete-storage allowance before all contexts, coefficient values and actual mode counts. -/
def memoryBound (axes:List Nat) (precision:List Bool) (modes:Modes):Nat:=
  2000*roundCap (resource axes precision modes)*workNodes modes
/-- Every ready/source initialized byte and the complete same-program clock fit this linear-node storage allowance. -/
theorem memory_cap (axes:List Nat) (precision:List Bool) (modes:Modes):
    112*(readyCells axes precision modes+runBound axes precision modes) ≤ memoryBound axes precision modes:=by
  have hi:=readyCells_le axes precision modes
  have hl:=linear_round (resource axes precision modes)
  have hinput:readyCells axes precision modes ≤5*roundCap (resource axes precision modes)*workNodes modes:=by
    exact hi.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 5 hl))
  unfold runBound memoryBound
  nlinarith only [hinput,Nat.zero_le (roundCap (resource axes precision modes)*workNodes modes)]
/-- All111allocated data roles and real returns at every actual ready prefix are polynomial per actual fold node. -/
theorem ready_prefix_linear (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes)
    (fuel:Nat) (out:C.State Stack Label) (hr:C.run program fuel (ready axes precision (modeTape modes))=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ memoryBound axes precision modes:=
  (ready_prefix_cells axes hp precision modes fuel out hr).trans (memory_cap axes precision modes)
/-- The original-header path includes the same actual ready inventory and has the same per-node all-role bound. -/
theorem source_prefix_linear (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes)
    (fuel:Nat) (out:C.State Stack Label)
    (hr:C.run program fuel (initial (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)) precision (modeTape modes))=some out):
    (∑k:Stack,(out.data k).length)+out.frames.length ≤ memoryBound axes precision modes:=by
  have hi:inputCells axes precision modes ≤ readyCells axes precision modes:=by unfold readyCells;omega
  exact (prefix_cells axes hp precision modes fuel out hr).trans
    ((Nat.mul_le_mul_left 112 (Nat.add_le_add_right hi _)).trans (memory_cap axes precision modes))
end RiemannGaussian.SemiprimeD1StackJetFoldLinearResources
