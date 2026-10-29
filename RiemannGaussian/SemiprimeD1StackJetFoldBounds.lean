/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldBudgetBounds
/-! # Closed own actual full/cache-entry source bounds, linear per actual term
Only actual original metadata/value dimensions and actual binary child-field
bytes enter the polynomial factor. Physical mode count enters linearly.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldBounds
open SemiprimeD1StackJetFold SemiprimeD1StackJetFoldWords SemiprimeD1StackJetFoldSpec
open SemiprimeD1StackJetFoldContext SemiprimeD1StackJetFoldExecution
open SemiprimeD1StackJetFoldInputBounds SemiprimeD1StackJetFoldOperatorBounds SemiprimeD1StackJetFoldBudgetBounds
/-- Original physical metadata, actual rank/precision VALUES, and actual largest supplied binary child field. -/
def resource (axes:List Nat) (precision:List Bool) (modes:Modes):Nat:=
  capacity (context axes precision) (acquiredHeader axes precision (modeTape modes)) modes
/-- Fixed actual source allowance, polynomial per actual combined sum/product fold node. -/
def runBound (axes:List Nat) (precision:List Bool) (modes:Modes):Nat:=10*roundCap (resource axes precision modes)*workNodes modes
/-- Closed explicit degree-six physical-value/field factor with a linear actual-node factor. -/
theorem runBound_formula (axes:List Nat) (precision:List Bool) (modes:Modes):
    runBound axes precision modes=10000000000000*(resource axes precision modes+1)^6*workNodes modes:=by
  unfold runBound roundCap
  ring
/-- Whole actual original-header source, with the SAME-program per-actual-node allowance. -/
theorem source_run_bounded (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes):
    ∃time ≤ runBound axes precision modes,SemiprimeD1StackCalls.run program time
      (initial (SemiprimeD1TensorTapeCodec.vectorBits (axes.map SemiprimeD1StackUnaryDivmod.unary)) precision (modeTape modes))=
        some (done axes precision modes):=by
  obtain ⟨time,ht,hr⟩:=source_run axes hp precision modes
  exact ⟨time,ht.trans (timeBound_le axes hp precision modes),hr⟩
/-- The SAME-program actually acquired-cache entry charges every subsequent copy/fold/cleanup/return/halt. -/
theorem ready_run_bounded (axes:List Nat) (hp:∀q∈axes,0 < q) (precision:List Bool) (modes:Modes):
    ∃time ≤ runBound axes precision modes,SemiprimeD1StackCalls.run program time
      (ready axes precision (modeTape modes))=some (done axes precision modes):=by
  obtain ⟨time,ht,hr⟩:=ready_run axes hp precision modes
  have hready:readyTimeBound axes precision modes ≤timeBound axes precision modes:=by unfold timeBound;omega
  exact ⟨time,ht.trans (hready.trans (timeBound_le axes hp precision modes)),hr⟩
/-- Literal64-group product/mode-sum work is linear in the actual number of modes. -/
theorem runBound_sixtyfour (axes:List Nat) (precision:List Bool) (modes:Modes) (h64:∀g∈modes,g.length=64):
    runBound axes precision modes=10000000000000*(resource axes precision modes+1)^6*(66*modes.length+1):=by
  rw [runBound_formula,nodes_sixtyfour modes h64]
/-- Actual dense child outputs have a mode-count-independent physical field/value resource. -/
def denseResource (axes:List Nat) (precision:List Bool):Nat:=
  metaSize (context axes precision) (acquiredHeader axes precision [])+2*denseBytes (context axes precision)+1
/-- Derived dense-input resource cap uses no supplied intermediate/output bound. -/
theorem resource_dense (axes:List Nat) (precision:List Bool) (modes:Modes)
    (hd:∀g∈modes,∀x∈g,Dense (context axes precision) x):
    resource axes precision modes ≤denseResource axes precision:=
  dense_capacity _ _ _ hd
/-- Same actual source clock for dense child vectors, with no mode count inside the polynomial factor. -/
theorem runBound_dense (axes:List Nat) (precision:List Bool) (modes:Modes)
    (hd:∀g∈modes,∀x∈g,Dense (context axes precision) x):
    runBound axes precision modes ≤10000000000000*(denseResource axes precision+1)^6*workNodes modes:=by
  rw [runBound_formula]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (Nat.add_le_add_right (resource_dense axes precision modes hd) 1) 6))
/-- Every actual stopped output is internally dense at the acquired rank and precision. -/
theorem output_length (axes:List Nat) (precision:List Bool) (modes:Modes):
    ((done axes precision modes).data output).length ≤denseBytes (context axes precision):=by
  rw [output_words]
  exact dense_tape_length _ _ (sum_dense _ _)
end RiemannGaussian.SemiprimeD1StackJetFoldBounds
