/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicTransformTableExecution
/-! # Concrete transform-family whole bit clock and full420-role prefix cells -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2040000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicTransformTableBounds
open SemiprimeD1StackPublicTransformTable SemiprimeD1StackPublicTransformTableTrace
open SemiprimeD1StackPublicTransformTableExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace S
export SemiprimeD1StackStaticTableSpec (inputBytes)
end S
/-- Only original N/two-flag bytes populate the actual204-role template bank. -/
theorem template_bytes (bits : List Bool) (second inverse : Bool) :
    S.inputBytes (inputTemplate bits second inverse)≤204*(bits.length+1) := by
  change (∑k:P.Stack,(inputTemplate bits second inverse k).length)≤_
  calc
    _≤∑_k:P.Stack,(bits.length+1):=Finset.sum_le_sum (fun k _=>template_cell_le bits second inverse k)
    _= _:=by simp only [Finset.sum_const,Finset.card_univ,SemiprimeD1StackPublicTransform.stack_card,smul_eq_mul]
/-- Honest actual original input inventory; scope IDs and padding are fully paid. -/
def inventory (bits : List Bool) (words : List (List Bool)) : Nat :=
  bits.length+(vectorBits words).length+3
/-- One fixed whole-source polynomial per actually materialized scalar leaf. -/
def runBound (bits : List Bool) (words : List (List Bool)) : Nat :=
  10^100*(inventory bits words)^18*2^words.length
/-- Fixed natural arithmetic for the204-role source; the lemma keeps the
kernel's closed role inventory separate from polynomial normalization. -/
theorem arithmetic_weight_bound (T n B scope I : Nat)
    (hT:T≤204*I^18) (hn:n≤I^18) (hB:B≤10^90*I^18) (hs:scope≤I^18) (hOne:1≤I^18) :
    11*scope+(204*(6*T+5)+7*n+B+204*(204*(T+n+B)+1)+20+20)+30≤
      10^100*I^18 := by omega
/-- Own complete transform-family bit time is polynomial in actual supplied input
BYTES times2^physicallyCountedArity. The native checker report is never substituted. -/
theorem timeBound_le (bits : List Bool) (second inverse : Bool) (words : List (List Bool)) :
    timeBound bits second inverse words≤ runBound bits words := by
  let I:=inventory bits words
  have hI:1≤ I:=by dsimp [I,inventory];omega
  have hI2:I≤ I^18:=by simpa only [pow_one] using Nat.pow_le_pow_right hI (by decide : 1≤18)
  have hn:=SemiprimeD1StackStaticTableBounds.scope_count_le words
  have hRaw:bits.length+words.length+1≤ I:=by dsimp [I,inventory];omega
  have hbudget:budget bits words.length≤10^90*I^18:=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hRaw 18)
  have hT:=template_bytes bits second inverse
  have hT2:S.inputBytes (inputTemplate bits second inverse)≤204*I^18:=
    hT.trans (Nat.mul_le_mul_left _ (by dsimp [I,inventory] at *;omega))
  have hn2:words.length≤ I^18:=by dsimp [I,inventory] at *;omega
  have hb2:(vectorBits words).length≤ I^18:=by dsimp [I,inventory] at *;omega
  have hOne:1≤I^18:=by omega
  have hw:=arithmetic_weight_bound (S.inputBytes (inputTemplate bits second inverse)) words.length
    (budget bits words.length) (vectorBits words).length I hT2 hn2 hbudget hb2 hOne
  unfold timeBound SemiprimeD1StackStaticTableBounds.runBound
    SemiprimeD1StackStaticTableDFS.weight SemiprimeD1StackStaticTableLeaf.leafBound
  have hroles:static.roles.length=204:=roles_length
  rw [SemiprimeD1StackPublicTransform.stack_card,hroles]
  exact Nat.mul_le_mul_right (2^words.length) hw
/-- Full actual original-N/two-flag/scope execution with the closed same-source clock. -/
theorem source_run_bounded (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool)) :
    ∃t≤ runBound bits words,SemiprimeD1StackCalls.run program t
      (initial bits second inverse (vectorBits words))=some (done bits second inverse words) := by
  obtain ⟨t,ht,hr⟩:=source_run bits second inverse hc hN words
  exact ⟨t,ht.trans (timeBound_le bits second inverse words),hr⟩
/-- The genuine fixed420-role finite machine, with the same complete source clock. -/
noncomputable def machineTable (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool)) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits second inverse (vectorBits words)))
      (some (SemiprimeD1StackCalls.configuration (done bits second inverse words))) (runBound bits words) := by
  let h:=tableInTime bits second inverse hc hN words
  exact ⟨h.toEvalsTo,h.steps_le_m.trans (timeBound_le bits second inverse words)⟩
/-- All420 source roles and every actual nested return cell at EVERY prefix. -/
theorem prefix_cells (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (fuel : Nat) (finish : SemiprimeD1StackCalls.State Stack Label)
    (hr : SemiprimeD1StackCalls.run program fuel (initial bits second inverse (vectorBits words))=some finish) :
    (∑k:Stack,(finish.data k).length)+finish.frames.length≤
      421*(204*(bits.length+1)+(vectorBits words).length+runBound bits words+1) := by
  have hs:=SemiprimeD1StackStaticTableBounds.prefix_cells static (inputTemplate bits second inverse)
    (template_raw bits second inverse) (answer bits second inverse) (budget bits)
    (actual_trace bits second inverse hc hN) words fuel finish hr
  rw [SemiprimeD1StackPublicTransform.stack_card] at hs
  change (∑k:Stack,(finish.data k).length)+finish.frames.length≤
    421*(S.inputBytes (inputTemplate bits second inverse)+(vectorBits words).length+timeBound bits second inverse words+1) at hs
  have hT:=template_bytes bits second inverse
  have ht:=timeBound_le bits second inverse words
  change timeBound bits second inverse words≤_ at ht
  omega
/-- Same full420-role and actual-return prefix certificate on the ACTUAL compiled machine. -/
theorem machine_prefix_cells (bits : List Bool) (second inverse : Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (hN : 0<SemiprimeBitArithmetic.bitValue bits) (words : List (List Bool))
    (fuel : Nat) (cfg : machine.Cfg)
    (hr : (fun q=>q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits second inverse (vectorBits words))))=some cfg) :
    (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
      421*(204*(bits.length+1)+(vectorBits words).length+runBound bits words+1) := by
  have hs:=SemiprimeD1StackStaticTableBounds.machine_prefix_cells static (inputTemplate bits second inverse)
    (template_raw bits second inverse) (answer bits second inverse) (budget bits)
    (actual_trace bits second inverse hc hN) words fuel cfg hr
  rw [SemiprimeD1StackPublicTransform.stack_card] at hs
  change (∑k:Stack,(cfg.stk (some k)).length)+(cfg.stk none).length≤
    421*(S.inputBytes (inputTemplate bits second inverse)+(vectorBits words).length+timeBound bits second inverse words+1) at hs
  have hT:=template_bytes bits second inverse
  have ht:=timeBound_le bits second inverse words
  change timeBound bits second inverse words≤_ at ht
  omega
end RiemannGaussian.SemiprimeD1StackPublicTransformTableBounds
