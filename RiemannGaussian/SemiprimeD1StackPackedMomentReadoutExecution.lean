/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPackedMomentReadoutBlock
/-! # Whole actual count/sum readout and same acquired-metadata continuation -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackPackedMomentReadoutExecution
open SemiprimeD1StackPackedMomentReadout SemiprimeD1StackPackedMomentReadoutEncoding
open SemiprimeD1StackPackedMomentReadoutPrimitives SemiprimeD1StackPackedMomentReadoutBlock
open SemiprimeD1StackProcedureTrace
/-- The actual acquired-metadata path includes both full digit blocks and true halt. -/
def readyBound (bits scalar : List Bool) : ℕ := blockTime bits scalar false+blockTime bits scalar true+1
/-- Whole prepared-input source pays the real N-only metadata acquisition once. -/
def runBound (bits scalar : List Bool) : ℕ :=
  SemiprimeD1StackPackedRootMetadataExecution.polynomial bits+1+readyBound bits scalar
/-- Both actual count/sum blocks compose with all22 words and every outer frame retained. -/
theorem ready_trace (bits scalar : List Bool) :
    ∃t,t+1 ≤ readyBound bits scalar ∧ Runs program t (ctl (.copyWidth false)) (ready bits scalar).data
      (ctl .done) (result bits scalar) := by
  have h0:=block_run bits scalar false (words scalar [] []) rfl rfl
  rw [words_update] at h0
  change Runs program _ _ (ready bits scalar).data (ctl (.copyWidth true))
    (bank (metadataResult bits) (fun _ => []) (words scalar (moment bits scalar false) [])) at h0
  have h1:=block_run bits scalar true (words scalar (moment bits scalar false) []) rfl rfl
  rw [words_update] at h1
  change Runs program _ (ctl (.copyWidth true)) _ (ctl .done) (result bits scalar) at h1
  exact ⟨_,Nat.le_refl _,join h0 h1⟩
/-- The actual source begins with only N and the separately acquired scalar data words. -/
theorem source_trace (bits scalar : List Bool) :
    ∃t,t+1 ≤ runBound bits scalar ∧ Runs program t (ctl .start) (input bits scalar) (ctl .done) (result bits scalar) := by
  obtain ⟨tm,hm,h0⟩:=metadata_call bits scalar
  obtain ⟨tr,hr,h1⟩:=ready_trace bits scalar
  exact ⟨tm+tr,by unfold runBound;omega,join h0 h1⟩
/-- Complete real source halts with both compact moments and every radix helper empty. -/
theorem source_run (bits scalar : List Bool) :
    ∃t ≤ runBound bits scalar,SemiprimeD1StackCalls.run program t (initial bits scalar)=some (done bits scalar) := by
  obtain ⟨t,ht,h⟩:=source_trace bits scalar
  obtain ⟨out,he,ha⟩:=h [] (initial bits scalar) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits scalar) [] out ha
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
/-- The SAME actual metadata-cache entry needs no replay of original width acquisition. -/
theorem ready_run (bits scalar : List Bool) :
    ∃t ≤ readyBound bits scalar,SemiprimeD1StackCalls.run program t (ready bits scalar)=some (done bits scalar) := by
  obtain ⟨t,ht,h⟩:=ready_trace bits scalar
  obtain ⟨out,he,ha⟩:=h [] (ready bits scalar) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (result bits scalar) [] out ha
  exact ⟨t+1,ht,by rw [SemiprimeD1StackReturnLink.run_add,he,Option.bind_some];exact hh⟩
end RiemannGaussian.SemiprimeD1StackPackedMomentReadoutExecution
