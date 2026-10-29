/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarryTableExecution
/-! # Concrete carry-family whole bit clock and full114-role prefix cells -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicCarryTableBounds
open SemiprimeD1StackPublicCarryTable SemiprimeD1StackPublicCarryTableTrace
open SemiprimeD1StackPublicCarryTableExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace S
export SemiprimeD1StackStaticTableSpec (inputBytes)
end S
/-- Only original input/index bytes populate the actual51-role template bank. -/
theorem template_bytes (bits indexWord : List Bool) :
    S.inputBytes (inputTemplate bits indexWord)≤51*(bits.length+indexWord.length) := by
  change (∑k:P.Stack,(inputTemplate bits indexWord k).length)≤_
  calc
    _≤∑_k:P.Stack,(bits.length+indexWord.length):=Finset.sum_le_sum (fun k _=>template_cell_le bits indexWord k)
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,SemiprimeD1StackPublicCarry.stack_card,smul_eq_mul]
/-- Honest actual original input inventory; scope IDs and padding are fully paid. -/
def inventory (bits indexWord : List Bool) (words : List (List Bool)) : Nat :=
  bits.length+indexWord.length+(vectorBits words).length+2
/-- One fixed whole-source polynomial per actually materialized scalar leaf. -/
def runBound (bits indexWord : List Bool) (words : List (List Bool)) : Nat :=
  100000000000000000000*(inventory bits indexWord words)^2*2^words.length
/-- Fixed natural arithmetic for the51-role source; the lemma keeps the
kernel's closed role inventory separate from polynomial normalization. -/
theorem arithmetic_weight_bound (T n B scope I : Nat)
    (hT:T≤51*I^2) (hn:n≤I^2) (hB:B≤1000000000000*I^2) (hs:scope≤I^2) (hOne:1≤I^2) :
    11*scope+(51*(6*T+5)+7*n+B+51*(51*(T+n+B)+1)+20+20)+30≤
      100000000000000000000*I^2 := by omega
/-- Own complete carry-family bit time is polynomial in actual supplied input
BYTES times2^physicallyCountedArity. The native checker report is never substituted. -/
theorem timeBound_le (bits indexWord : List Bool) (words : List (List Bool)) :
    timeBound bits indexWord words≤ runBound bits indexWord words := by
  let I:=inventory bits indexWord words
  have hI:1≤ I:=by dsimp [I,inventory];omega
  have hI2:I≤ I^2:=by simpa only [pow_one] using Nat.pow_le_pow_right hI (by decide : 1≤2)
  have hn:=SemiprimeD1StackStaticTableBounds.scope_count_le words
  have hRaw:bits.length+words.length+indexWord.length+2≤ I:=by dsimp [I,inventory];omega
  have hbudget:budget bits indexWord words.length≤1000000000000*I^2:=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hRaw 2)
  have hT:=template_bytes bits indexWord
  have hT2:S.inputBytes (inputTemplate bits indexWord)≤51*I^2:=
    hT.trans (Nat.mul_le_mul_left _ (by dsimp [I,inventory] at *;omega))
  have hn2:words.length≤ I^2:=by dsimp [I,inventory] at *;omega
  have hb2:(vectorBits words).length≤ I^2:=by dsimp [I,inventory] at *;omega
  have hOne:1≤I^2:=by omega
  have hw:=arithmetic_weight_bound (S.inputBytes (inputTemplate bits indexWord)) words.length
    (budget bits indexWord words.length) (vectorBits words).length I hT2 hn2 hbudget hb2 hOne
  unfold timeBound SemiprimeD1StackStaticTableBounds.runBound
    SemiprimeD1StackStaticTableDFS.weight SemiprimeD1StackStaticTableLeaf.leafBound
  have hroles:static.roles.length=51:=roles_length
  rw [SemiprimeD1StackPublicCarry.stack_card,hroles]
  exact Nat.mul_le_mul_right (2^words.length) hw
/-- Full actual original-N/index/scope execution with the closed same-source clock. -/
theorem source_run_bounded (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool)) :
    ∃t≤ runBound bits indexWord words,SemiprimeD1StackCalls.run program t
      (initial bits indexWord (vectorBits words))=some (done bits indexWord words) := by
  obtain ⟨t,ht,hr⟩:=source_run bits indexWord hb words
  exact ⟨t,ht.trans (timeBound_le bits indexWord words),hr⟩
/-- The genuine fixed114-role finite machine, with the same complete source clock. -/
noncomputable def machineTable (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool)) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits indexWord (vectorBits words)))
      (some (SemiprimeD1StackCalls.configuration (done bits indexWord words))) (runBound bits indexWord words) := by
  let h:=tableInTime bits indexWord hb words
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (timeBound_le bits indexWord words)⟩
/-- All114 source roles and every actual nested return cell at EVERY prefix. -/
theorem prefix_cells (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool))
    (fuel : Nat) (finish : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits indexWord (vectorBits words))=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      115*(51*(bits.length+indexWord.length)+(vectorBits words).length+runBound bits indexWord words+1) := by
  have hs:=SemiprimeD1StackStaticTableBounds.prefix_cells static (inputTemplate bits indexWord)
    (template_raw bits indexWord) (answer bits indexWord) (budget bits indexWord)
    (actual_trace bits indexWord hb) words fuel finish hr
  rw [SemiprimeD1StackPublicCarry.stack_card] at hs
  change (∑k:Stack,(finish.data k).length)+finish.frames.length≤
    115*(S.inputBytes (inputTemplate bits indexWord)+(vectorBits words).length+timeBound bits indexWord words+1) at hs
  have hT:=template_bytes bits indexWord
  have ht:=timeBound_le bits indexWord words
  change timeBound bits indexWord words≤_ at ht
  omega
/-- Same full114-role and actual-return prefix certificate on the ACTUAL compiled machine. -/
theorem machine_prefix_cells (bits indexWord : List Bool) (hb : bits≠[]) (words : List (List Bool))
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits indexWord (vectorBits words))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      115*(51*(bits.length+indexWord.length)+(vectorBits words).length+runBound bits indexWord words+1) := by
  have hs:=SemiprimeD1StackStaticTableBounds.machine_prefix_cells static (inputTemplate bits indexWord)
    (template_raw bits indexWord) (answer bits indexWord) (budget bits indexWord)
    (actual_trace bits indexWord hb) words fuel cfg hr
  rw [SemiprimeD1StackPublicCarry.stack_card] at hs
  change (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
    115*(S.inputBytes (inputTemplate bits indexWord)+(vectorBits words).length+timeBound bits indexWord words+1) at hs
  have hT:=template_bytes bits indexWord
  have ht:=timeBound_le bits indexWord words
  change timeBound bits indexWord words≤_ at ht
  omega
end RiemannGaussian.SemiprimeD1StackPublicCarryTableBounds
