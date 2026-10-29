/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedMomentReadoutPrimitives
/-! # Actual whole low/high extraction block, including copies and physical cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedMomentReadoutBlock
open SemiprimeD1StackPackedMomentReadout SemiprimeD1StackPackedMomentReadoutEncoding
open SemiprimeD1StackPackedMomentReadoutPrimitives SemiprimeD1StackProcedureTrace
/-- Exactly two real operand copies, with no digit/result supplier. -/
theorem prepare_run (bits scalar : List Bool) (high : Bool) (u : Aux→List Bool) (hu : u .scalar=scalar) :
    Runs program ((5*(width bits).length+4)+(5*scalar.length+4))
      (ctl (.copyWidth high)) (bank (metadataResult bits) (fun _ => []) u)
      (afterScalar high) (bank (metadataResult bits) (D.store scalar (width bits) [] [] [] []) u) := by
  let m:=metadataResult bits
  have h0:=copy_call (.width high) (ctl (.copyWidth high)) (ctl (.copyScalar high)) rfl
    (bank m (D.store [] [] [] [] [] []) u) (width bits) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update _ (digit .width) (_++[])) at h0
  rw [List.append_nil,bank_digit,digit_width] at h0
  have h1:=copy_call (.scalar high) (ctl (.copyScalar high)) (afterScalar high) rfl
    (bank m (D.store [] (width bits) [] [] [] []) u) scalar [] hu rfl rfl
  change Runs program _ _ _ _ (Function.update _ (digit .input) (_++[])) at h1
  rw [List.append_nil,bank_digit,digit_input] at h1
  simpa only [empty_digit] using join h0 h1
/-- The literal high-digit index seed costs one real push; the low digit has no seed. -/
def seedTime (high : Bool) : ℕ := if high then 1 else 0
/-- Actual finite selector installs exactly EMPTY or the literal singleton TRUE. -/
theorem index_run (bits scalar : List Bool) (high : Bool) (u : Aux→List Bool) :
    Runs program (seedTime high) (afterScalar high)
      (bank (metadataResult bits) (D.store scalar (width bits) [] [] [] []) u)
      (ctl (.acquire high)) (bank (metadataResult bits) (D.store scalar (width bits) (index high) [] [] []) u) := by
  cases high
  · exact runs_refl program _ _
  · have h:=seed_index (bank (metadataResult bits) (D.store scalar (width bits) [] [] [] []) u)
    change Runs program _ _ _ _ (Function.update _ (digit .index) [true]) at h
    rw [bank_digit,digit_index] at h
    exact h
/-- Exact actual output-save and erasure clock. -/
def saveTime (bits scalar : List Bool) (high : Bool) : ℕ :=
  (5*(moment bits scalar high).length+4)+((moment bits scalar high).length+1)
/-- The physically produced digit is really copied and then erased from its six-word source. -/
theorem save_run (bits scalar : List Bool) (high : Bool) (u : Aux→List Bool) (ht : u (target high)=[]) :
    Runs program (saveTime bits scalar high) (ctl (.copyOutput high))
      (bank (metadataResult bits) (D.store [] [] [] [] [] (moment bits scalar high)) u)
      (afterClear high) (bank (metadataResult bits) (fun _ => [])
        (Function.update u (target high) (moment bits scalar high))) := by
  have h0:=copy_call (.output high) (ctl (.copyOutput high)) (ctl (.clearOutput high)) rfl
    (bank (metadataResult bits) (D.store [] [] [] [] [] (moment bits scalar high)) u)
    (moment bits scalar high) [] rfl ht rfl
  change Runs program _ _ _ _ (Function.update _ (aux (target high)) (_++[])) at h0
  rw [List.append_nil,bank_aux] at h0
  exact join h0 (clear_output bits (Function.update u (target high) (moment bits scalar high)) (moment bits scalar high) high)
/-- Exact own instruction count for one complete low/high extraction block. -/
def blockTime (bits scalar : List Bool) (high : Bool) : ℕ :=
  ((5*(width bits).length+4)+(5*scalar.length+4))+seedTime high+
    digitTime bits scalar high+saveTime bits scalar high
/-- One real extraction block from all22 actual words, retaining every foreign field. -/
theorem block_run (bits scalar : List Bool) (high : Bool) (u : Aux→List Bool)
    (hu : u .scalar=scalar) (ht : u (target high)=[]) :
    Runs program (blockTime bits scalar high) (ctl (.copyWidth high))
      (bank (metadataResult bits) (fun _ => []) u) (afterClear high)
      (bank (metadataResult bits) (fun _ => []) (Function.update u (target high) (moment bits scalar high))) :=
  join (join (join (prepare_run bits scalar high u hu) (index_run bits scalar high u))
    (digit_call bits scalar high u)) (save_run bits scalar high u ht)
end RiemannGaussian.SemiprimeD1StackPackedMomentReadoutBlock
