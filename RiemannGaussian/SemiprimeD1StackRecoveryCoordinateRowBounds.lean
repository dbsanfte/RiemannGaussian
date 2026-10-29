/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinateCapacities
import RiemannGaussian.SemiprimeD1StackRecoveryCoordinatePhase
/-! # Actual per-phase own-clock polynomial
Every physical block lookup is paid by the sealed reader's actual source clock.
Only the one executed final row-history reverse contributes history-length cost.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryCoordinateRowBounds
open SemiprimeD1StackRecoveryCoordinateEncoding SemiprimeD1StackRecoveryCoordinateBlock
open SemiprimeD1StackRecoveryCoordinateCapacities SemiprimeD1StackRecoveryCoordinatePhase
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Sum of the actual per-block source clocks, without final row reversal. -/
def blockSum (key:List Bool):List (List (List Bool))→Nat
  | []=>0
  | words::rest=>blockTime key words+blockSum key rest
/-- Literal chunk-history length recurrence. -/
theorem chunks_cons_length (word:List Bool) (words:List (List Bool)):
    (chunks (word::words)).length=(chunk word).length+(chunks words).length:=by
  simp only [chunks,List.foldr_cons,List.length_append]
/-- Exact same-program row-loop cost: actual block steps plus one real final history reverse. -/
theorem block_budget_eq (key:List Bool) (blocks:List (List (List Bool))) (history:List Bool):
    B.budget key blocks history=blockSum key blocks+2*(chunks (row key blocks)).length+2*history.length+4:=by
  induction blocks generalizing history with
  | nil=>
    simp only [B.budget,blockSum,row,List.map_nil,chunks,List.foldr_nil,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
  | cons words blocks ih=>
    have hr:row key (words::blocks)=coefficient key words::row key blocks:=rfl
    rw [B.budget,ih,blockSum,hr,chunks_cons_length,List.length_append,List.length_reverse]
    omega
/-- Actual per-block sum has the physical input-byte quadratic at each actual block occurrence. -/
theorem block_sum_bound (key:List Bool) (blocks:List (List (List Bool))) (L:Nat)
    (hl:∀words∈blocks,(vectorBits words).length ≤L):
    blockSum key blocks ≤10000000*blocks.length*(L+key.length+1)^2:=by
  induction blocks with
  | nil=>simp only [blockSum,List.length_nil,Nat.mul_zero,Nat.zero_mul,Nat.le_refl]
  | cons words blocks ih=>
    have h0:=block_time key words L (hl words (List.mem_cons_self))
    have h1:=ih (fun ws hws=>hl ws (List.mem_cons_of_mem words hws))
    simp only [blockSum,List.length_cons,Nat.mul_add,Nat.add_mul,Nat.mul_one]
    omega
/-- All actual row lookup/logging and its final reverse fit a cubic in physical bank/query bytes. -/
theorem block_budget_bound (key:List Bool) (blocks:List (List (List Bool))) (L:Nat)
    (hl:(vectorBits (blocks.map vectorBits)).length ≤L):
    B.budget key blocks [] ≤100000000*(L+key.length+1)^3:=by
  let S:=L+key.length+1
  have hsum:=block_sum_bound key blocks L (fun words hw=>(block_length blocks words hw).trans hl)
  have hn:blocks.length ≤S:=(block_count blocks).trans (hl.trans (by dsimp [S];omega))
  have hrow: (chunks (row key blocks)).length ≤L:=by
    have h0:=row_length key blocks
    have h1:=chunks_length (row key blocks)
    omega
  have hsum':blockSum key blocks ≤10000000*S^3:=by
    calc
      _ ≤10000000*blocks.length*S^2:=hsum
      _ ≤10000000*S*S^2:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 10000000 hn)
      _=10000000*S^3:=by ring
  have hlin:S ≤S^3:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by dsimp [S];omega:1 ≤S) (by decide:1 ≤3)
  have hL:L+1 ≤S:=by dsimp [S];omega
  rw [block_budget_eq]
  simp only [List.length_nil,Nat.mul_zero,Nat.add_zero]
  change blockSum key blocks+2*(chunks (row key blocks)).length+4 ≤100000000*S^3
  omega
/-- Every whole actual phase has the same own cubic physical-byte cap, with no old report clock. -/
theorem phase_time (key:List Bool) (blocks:List (List (List Bool))) (L:Nat)
    (hl:(vectorBits (blocks.map vectorBits)).length ≤L):
    phaseTime key blocks ≤1000000000*(L+key.length+1)^3:=by
  have hb:=block_budget_bound key blocks L hl
  have hr:(phaseRow key blocks).length ≤L:=(row_length key blocks).trans hl
  have hlin:L+key.length+1 ≤(L+key.length+1)^3:=by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega:1 ≤L+key.length+1) (by decide:1 ≤3)
  unfold phaseTime
  rw [chunk_length]
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryCoordinateRowBounds
