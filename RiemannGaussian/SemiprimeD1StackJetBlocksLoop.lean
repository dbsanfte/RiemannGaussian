/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocksRow
/-! # Actual q-marker block traversal and a single-consumption byte bound
Every real coefficient field is consumed once. Padding costs only the actual
rank/output markers; trailing source fields remain available for final cleanup.+-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksLoop
open SemiprimeD1StackJetBlocks SemiprimeD1StackJetBlocksPrimitives SemiprimeD1StackJetBlocksView
open SemiprimeD1StackJetBlocksEncoding SemiprimeD1StackJetBlocksInner SemiprimeD1StackJetBlocksRow
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
local notation "ctl" => Label.local
/-- Actual coefficient byte mass of all emitted blocks, including literal empty padding. -/
def chunkMass (rank:Nat) :Nat→List (List Bool)→Nat
  | 0,_=>0
  | q+1,words=>wordMass (padded rank words)+chunkMass rank q (words.drop rank)
/-- A physical consumed prefix and its remaining suffix partition all coefficient bytes. -/
theorem mass_split (rank:Nat) (words:List (List Bool)) :
    wordMass (words.take rank)+wordMass (words.drop rank)=wordMass words :=by
  unfold wordMass
  rw [←List.sum_append,←List.map_append,List.take_append_drop]
/-- The entire q traversal never charges any actual coefficient word twice. -/
theorem chunkMass_le (rank q:Nat) (words:List (List Bool)) :chunkMass rank q words≤wordMass words :=by
  induction q generalizing words with
  | zero=>exact Nat.zero_le _
  | succ q ih=>
    have h:=ih (words.drop rank)
    have hs:=mass_split rank words
    rw [chunkMass,padded_mass]
    omega
/-- Own actual block-loop allowance; its terms are paid concrete primitive execution caps. -/
def loopBudget (rank:Nat) :Nat→List (List Bool)→Nat
  | 0,_=>1
  | q+1,words=>1+(100*wordMass (padded rank words)+100*(rank+1))+loopBudget rank q (words.drop rank)
/-- Complete actual q-marker loop, preserving the entire acquired context and both physical inputs. -/
theorem blocks_run (context:X.Stack→List Bool) (coefficients blocks history:List Bool) (rank q:Nat)
    (hr:context X.rankCache=List.replicate rank true) (words:List (List Bool)) :
    ∃t≤loopBudget rank q words,Runs program t (ctl .outer)
      (data context coefficients blocks (List.replicate q true) (vectorBits words) [] [] [] [] history)
      (ctl .finishSeed)
      (data context coefficients blocks [] (vectorBits (words.drop (q*rank))) [] [] [] []
        ((Codec.payload ((chunks rank q words).map vectorBits)).reverse++history)) :=by
  induction q generalizing words history with
  | zero=>
    refine ⟨1,Nat.le_refl _,?_⟩
    simp only [Nat.zero_mul,List.drop_zero]
    apply one_base program (ctl .outer) (ctl .finishSeed)
      (.pop (aux .todo) (ctl .finishSeed) (ctl .abort) (ctl .copyRank)) _ _ rfl
    · rfl
    · funext k;rcases k with k|k
      · rfl
      · cases k <;> rfl
  | succ q ih=>
    let before:=data context coefficients blocks (List.replicate (q+1) true) (vectorBits words) [] [] [] [] history
    have h0:=pop_run .outer (ctl .finishSeed) (ctl .abort) (ctl .copyRank) (aux .todo)
      before (true::List.replicate q true) rfl rfl
    change Runs program 1 (ctl .outer) before (ctl .copyRank)
      (Function.update before (aux .todo) (List.replicate q true)) at h0
    rw [show Function.update before (aux .todo) (List.replicate q true)=
      data context coefficients blocks (List.replicate q true) (vectorBits words) [] [] [] [] history
      from data_todo _ _ _ _ _ _ _ _ _ _ _] at h0
    obtain ⟨a,ha,h1⟩:=block_run context coefficients blocks (List.replicate q true) history rank hr words
    obtain ⟨b,hb,h2⟩:=ih ((Codec.chunk (vectorBits (padded rank words))).reverse++history) (words.drop rank)
    have h:=join (join h0 h1) h2
    have hd:(words.drop rank).drop (q*rank)=words.drop ((q+1)*rank):=by
      rw [List.drop_drop,Nat.succ_mul]
      congr 1
      omega
    rw [hd] at h
    refine ⟨1+a+b,by dsimp only [loopBudget];omega,?_⟩
    simpa only [chunks,List.map_cons,Codec.payload,List.foldr_cons,List.reverse_append,List.append_assoc] using h
/-- Exact recursive allowance is linear in consumed bytes and actual emitted rank markers. -/
theorem loopBudget_exact (rank q:Nat) (words:List (List Bool)) :
    loopBudget rank q words=100*chunkMass rank q words+q*(100*(rank+1)+1)+1 :=by
  induction q generalizing words with
  | zero=>simp only [loopBudget,chunkMass,Nat.mul_zero,Nat.zero_mul,Nat.zero_add]
  | succ q ih=>
    rw [loopBudget,chunkMass,ih]
    ring
/-- No computed offsets or repeated source scans occur in the actual block source's bound. -/
theorem loopBudget_le (rank q:Nat) (words:List (List Bool)) :
    loopBudget rank q words≤101*(wordMass words+q*(rank+1))+1 :=by
  rw [loopBudget_exact]
  have h:=chunkMass_le rank q words
  nlinarith
end RiemannGaussian.SemiprimeD1StackJetBlocksLoop
