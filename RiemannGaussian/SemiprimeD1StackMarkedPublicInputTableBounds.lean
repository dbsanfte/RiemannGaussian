/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableExecution
/-! # Own polynomial-per-actual-assignment time and all144-role storage -/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableBounds
open SemiprimeD1StackMarkedPublicInputTable SemiprimeD1StackMarkedPublicInputTableTrace
open SemiprimeD1StackMarkedPublicInputTableExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
namespace G
export SemiprimeD1StackStaticWordTableSpec (inputBytes)
end G
/-- Actual source bytes only, including every byte of the retained binary scope vector. -/
def resource (bits indexWord bank : List Bool) : Nat := bits.length+indexWord.length+bank.length+2
/-- Fixed polynomial times the physically counted arity's actual full2^n visits. -/
def polynomial (bits indexWord : List Bool) (words : List (List Bool)) : Nat :=
  1000000000000000000000000*(resource bits indexWord (vectorBits words))^2*2^words.length
/-- The same actual scope scan/source/framing/cleanup budget has a fixed own rate. -/
theorem runBound_le (bits indexWord : List Bool) (side : Bool) (words : List (List Bool)) :
    runBound bits indexWord side words ≤ polynomial bits indexWord words := by
  let r := resource bits indexWord (vectorBits words)
  let i := G.inputBytes (inputTemplate bits indexWord side)
  let b := budget bits indexWord words.length
  have hr : 2 ≤ r := by dsimp [r,resource];omega
  have hn0 := SemiprimeD1StackStaticWordTableBounds.scope_count_le words
  have hn : words.length ≤ r := by dsimp [r,resource];omega
  have hbank : (vectorBits words).length ≤ r := by dsimp [r,resource];omega
  have hi : i ≤ 66*r := by
    have hh := template_total_le bits indexWord side
    dsimp only [i,r,resource]
    omega
  have hb : b ≤ 10000000000000000*r^2 := by
    have h : bits.length+words.length+indexWord.length+2 ≤ r := by dsimp [r,resource];omega
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 2)
  have hr2 : r ≤ r^2 := Nat.le_pow (by decide : 0<(2:Nat))
  unfold runBound SemiprimeD1StackStaticWordTableBounds.runBound
    SemiprimeD1StackStaticWordTableDFS.weight SemiprimeD1StackStaticWordTableLeaf.leafBound polynomial
  rw [show static.roles.length=66 from roles_length,SemiprimeD1StackMarkedPublicInputCompact.stack_card]
  change (11*(vectorBits words).length+
    (66*(6*i+5)+7*words.length+b+66*(66*(i+words.length+b)+1)+50*(i+words.length+b+1)+50+20)+
      4*(i+words.length+b)+40)*2^words.length ≤ (1000000000000000000000000*r^2)*2^words.length
  apply Nat.mul_le_mul_right
  nlinarith
/-- Entire actual whole144-role source, including all real calls/returns and halt. -/
theorem source_run_bounded (bits indexWord : List Bool) (side : Bool) (words : List (List Bool)) (hb : bits≠[]) :
    ∃ t ≤ polynomial bits indexWord words,
      SemiprimeD1StackCalls.run program t (initial bits indexWord side (vectorBits words))=
        some (done bits indexWord side words) := by
  obtain ⟨t,ht,hh⟩ := source_run bits indexWord side words hb
  exact ⟨t,ht.trans (runBound_le bits indexWord side words),hh⟩
/-- Genuine finite compiled execution from only actual original inputs and scope-bank bytes. -/
noncomputable def machineSource (bits indexWord : List Bool) (side : Bool) (words : List (List Bool)) (hb : bits≠[]) :
    StateTransition.EvalsToInTime machine.step
      (SemiprimeD1StackCalls.configuration (initial bits indexWord side (vectorBits words)))
      (some (SemiprimeD1StackCalls.configuration (done bits indexWord side words)))
      (polynomial bits indexWord words) := by
  apply SemiprimeD1StackCalls.evalsCorrect (SemiprimeD1StackStaticWordTable.counter .bank)
    (SemiprimeD1StackStaticWordTable.aux .output) .start program
  let hh := source_run_bounded bits indexWord side words hb
  exact ⟨⟨Classical.choose hh,(Classical.choose_spec hh).2⟩,(Classical.choose_spec hh).1⟩
/-- Every actual144-role prefix includes all retained templates, dirty shadows,
work, accumulated table output and genuine nested return-label cells. -/
theorem machine_cells (bits indexWord : List Bool) (side : Bool) (words : List (List Bool)) (hb : bits≠[])
    (fuel : Nat) (cfg : machine.Cfg)
    (hp : (fun q => q.bind machine.step)^[fuel]
      (some (SemiprimeD1StackCalls.configuration (initial bits indexWord side (vectorBits words))))=some cfg) :
    (∑ k : Stack, (cfg.stk (some k)).length)+(cfg.stk none).length ≤
      1000000000000000000000000000*(resource bits indexWord (vectorBits words))^2*2^words.length := by
  have hs := machine_prefix_cells bits indexWord side words hb fuel cfg hp
  have ht := runBound_le bits indexWord side words
  have hi := template_total_le bits indexWord side
  let r := resource bits indexWord (vectorBits words)
  have hr : 2 ≤ r := by dsimp [r,resource];omega
  have hr2 : r ≤ r^2 := Nat.le_pow (by decide : 0<(2:Nat))
  have hp2 : 1 ≤ (2:Nat)^words.length := by
    have hh : 0 < (2:Nat)^words.length := by positivity
    omega
  have hx : r ≤ r^2*2^words.length := by nlinarith
  have hi' : G.inputBytes (inputTemplate bits indexWord side) ≤ 66*r := by dsimp [r,resource];omega
  have hb' : (vectorBits words).length ≤ r := by dsimp [r,resource];omega
  unfold polynomial at ht
  change _ ≤ 1000000000000000000000000000*r^2*2^words.length
  change runBound bits indexWord side words ≤ 1000000000000000000000000*r^2*2^words.length at ht
  nlinarith
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableBounds

