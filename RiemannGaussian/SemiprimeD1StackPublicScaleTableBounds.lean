/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicScaleTableExecution
/-! # Concrete scale-family whole bit clock and full332-role prefix cells -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicScaleTableBounds
open SemiprimeD1StackPublicScaleTable SemiprimeD1StackPublicScaleTableTrace
open SemiprimeD1StackPublicScaleTableExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace S
export SemiprimeD1StackStaticTableSpec (inputBytes)
end S
/-- Only original input/j/k/selector bytes populate the actual160-role template bank. -/
theorem template_bytes (bits stride frequency : List Bool) (inverse : Bool) :
    S.inputBytes (inputTemplate bits stride frequency inverse)≤160*(bits.length+stride.length+frequency.length+1) := by
  change (∑k:P.Stack,(inputTemplate bits stride frequency inverse k).length)≤_
  calc
    _≤∑_k:P.Stack,(bits.length+stride.length+frequency.length+1):=Finset.sum_le_sum (fun k _=>template_cell_le bits stride frequency inverse k)
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,SemiprimeD1StackPublicScale.stack_card,smul_eq_mul]
/-- Honest actual original input inventory; scope IDs and padding are fully paid. -/
def inventory (bits stride frequency : List Bool) (words : List (List Bool)) : Nat :=
  bits.length+stride.length+frequency.length+(vectorBits words).length+2
/-- One fixed whole-source polynomial per actually materialized scalar leaf. -/
def runBound (bits stride frequency : List Bool) (words : List (List Bool)) : Nat :=
  10^80*(inventory bits stride frequency words)^16*2^words.length
/-- Fixed natural arithmetic for the160-role source; the lemma keeps the
kernel's closed role inventory separate from polynomial normalization. -/
theorem arithmetic_weight_bound (T n B scope I : Nat)
    (hT:T≤160*I^16) (hn:n≤I^16) (hB:B≤10^70*I^16) (hs:scope≤I^16) (hOne:1≤I^16) :
    11*scope+(160*(6*T+5)+7*n+B+160*(160*(T+n+B)+1)+20+20)+30≤
      10^80*I^16 := by omega
/-- Own complete scale-family bit time is polynomial in actual supplied input
BYTES times2^physicallyCountedArity. The native checker report is never substituted. -/
theorem timeBound_le (bits stride frequency : List Bool) (inverse : Bool) (words : List (List Bool)) :
    timeBound bits stride frequency inverse words≤ runBound bits stride frequency words := by
  let I:=inventory bits stride frequency words
  have hI:1≤ I:=by dsimp [I,inventory];omega
  have hI2:I≤ I^16:=by simpa only [pow_one] using Nat.pow_le_pow_right hI (by decide : 1≤16)
  have hn:=SemiprimeD1StackStaticTableBounds.scope_count_le words
  have hRaw:bits.length+words.length+stride.length+frequency.length+2≤ I:=by dsimp [I,inventory];omega
  have hbudget:budget bits stride frequency words.length≤10^70*I^16:=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hRaw 16)
  have hT:=template_bytes bits stride frequency inverse
  have hT2:S.inputBytes (inputTemplate bits stride frequency inverse)≤160*I^16:=
    hT.trans (Nat.mul_le_mul_left _ (by dsimp [I,inventory] at *;omega))
  have hn2:words.length≤ I^16:=by dsimp [I,inventory] at *;omega
  have hb2:(vectorBits words).length≤ I^16:=by dsimp [I,inventory] at *;omega
  have hOne:1≤I^16:=by omega
  have hw:=arithmetic_weight_bound (S.inputBytes (inputTemplate bits stride frequency inverse)) words.length
    (budget bits stride frequency words.length) (vectorBits words).length I hT2 hn2 hbudget hb2 hOne
  unfold timeBound SemiprimeD1StackStaticTableBounds.runBound
    SemiprimeD1StackStaticTableDFS.weight SemiprimeD1StackStaticTableLeaf.leafBound
  have hroles:static.roles.length=160:=roles_length
  rw [SemiprimeD1StackPublicScale.stack_card,hroles]
  exact Nat.mul_le_mul_right (2^words.length) hw
/-- Full actual original-N/index/scope execution with the closed same-source clock. -/
theorem source_run_bounded (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool)) :
    ∃t≤ runBound bits stride frequency words,SemiprimeD1StackCalls.run program t
      (initial bits stride frequency inverse (vectorBits words))=some (done bits stride frequency inverse words) := by
  obtain ⟨t,ht,hr⟩:=source_run bits stride frequency inverse hj hk hc hN words
  exact ⟨t,ht.trans (timeBound_le bits stride frequency inverse words),hr⟩
/-- The genuine fixed332-role finite machine, with the same complete source clock. -/
noncomputable def machineTable (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool)) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits stride frequency inverse (vectorBits words)))
      (some (SemiprimeD1StackCalls.configuration (done bits stride frequency inverse words))) (runBound bits stride frequency words) := by
  let h:=tableInTime bits stride frequency inverse hj hk hc hN words
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (timeBound_le bits stride frequency inverse words)⟩
/-- All332 source roles and every actual nested return cell at EVERY prefix. -/
theorem prefix_cells (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (fuel : Nat) (finish : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits stride frequency inverse (vectorBits words))=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      333*(160*(bits.length+stride.length+frequency.length+1)+(vectorBits words).length+runBound bits stride frequency words+1) := by
  have hs:=SemiprimeD1StackStaticTableBounds.prefix_cells static (inputTemplate bits stride frequency inverse)
    (template_raw bits stride frequency inverse) (answer bits stride frequency inverse) (budget bits stride frequency)
    (actual_trace bits stride frequency inverse hj hk hc hN) words fuel finish hr
  rw [SemiprimeD1StackPublicScale.stack_card] at hs
  change (∑k:Stack,(finish.data k).length)+finish.frames.length≤
    333*(S.inputBytes (inputTemplate bits stride frequency inverse)+(vectorBits words).length+timeBound bits stride frequency inverse words+1) at hs
  have hT:=template_bytes bits stride frequency inverse
  have ht:=timeBound_le bits stride frequency inverse words
  change timeBound bits stride frequency inverse words≤_ at ht
  omega
/-- Same full332-role and actual-return prefix certificate on the ACTUAL compiled machine. -/
theorem machine_prefix_cells (bits stride frequency : List Bool) (inverse : Bool) (hj : stride=SemiprimeD1StackUnaryDivmod.unary stride.length)
    (hk : frequency=SemiprimeD1StackUnaryDivmod.unary frequency.length)
    (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits stride frequency inverse (vectorBits words))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      333*(160*(bits.length+stride.length+frequency.length+1)+(vectorBits words).length+runBound bits stride frequency words+1) := by
  have hs:=SemiprimeD1StackStaticTableBounds.machine_prefix_cells static (inputTemplate bits stride frequency inverse)
    (template_raw bits stride frequency inverse) (answer bits stride frequency inverse) (budget bits stride frequency)
    (actual_trace bits stride frequency inverse hj hk hc hN) words fuel cfg hr
  rw [SemiprimeD1StackPublicScale.stack_card] at hs
  change (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
    333*(S.inputBytes (inputTemplate bits stride frequency inverse)+(vectorBits words).length+timeBound bits stride frequency inverse words+1) at hs
  have hT:=template_bytes bits stride frequency inverse
  have ht:=timeBound_le bits stride frequency inverse words
  change timeBound bits stride frequency inverse words≤_ at ht
  omega
end RiemannGaussian.SemiprimeD1StackPublicScaleTableBounds
