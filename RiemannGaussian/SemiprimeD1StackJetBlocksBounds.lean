/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetBlocksExecution
/-! # Own whole-source and linear acquired-cache block extraction bounds
The ready source is linear in actual coefficient-vector bytes and emitted
q-by-rank fields. The complete source also pays actual context acquisition,
including rank and the precision VALUE, with fixed constants for every family.+-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackJetBlocksBounds
open SemiprimeD1StackJetBlocks SemiprimeD1StackJetBlocksEncoding SemiprimeD1StackJetBlocksInner
open SemiprimeD1StackJetBlocksLoop SemiprimeD1StackJetBlocksReady SemiprimeD1StackJetBlocksExecution
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Exact real outer-log bytes: raw coefficient bits plus every coefficient/block frame. -/
theorem history_length (rank q:Nat) (words:List (List Bool)) :
    (Codec.payload ((chunks rank q words).map vectorBits)).length=
      4*chunkMass rank q words+4*q*rank+4*q :=by
  induction q generalizing words with
  | zero=>simp only [chunks,List.map_nil,Codec.payload,List.foldr_nil,List.length_nil,chunkMass,
      Nat.mul_zero,Nat.zero_mul,Nat.zero_add]
  | succ q ih=>
    change (Codec.chunk (vectorBits (padded rank words))++
      Codec.payload ((chunks rank q (words.drop rank)).map vectorBits)).length=_
    rw [List.length_append,Codec.chunk_length,ih]
    have hv:(vectorBits (padded rank words)).length=2*wordMass (padded rank words)+2*rank+1:=by
      simpa only [wordMass,padded_length] using SemiprimeD1StackNetworkRowsEncoding.vector_length (padded rank words)
    rw [hv]
    dsimp only [chunkMass]
    ring
/-- A suffix vector contains no more actual physical bytes than its complete input. -/
theorem drop_vector_length_le (d:Nat) (words:List (List Bool)) :
    (vectorBits (words.drop d)).length≤(vectorBits words).length :=by
  have hm:=mass_split d words
  have hl:(words.drop d).length≤words.length:=by simp only [List.length_drop];omega
  rw [SemiprimeD1StackNetworkRowsEncoding.vector_length,SemiprimeD1StackNetworkRowsEncoding.vector_length]
  change 2*wordMass (words.drop d)+2*(words.drop d).length+1≤2*wordMass words+2*words.length+1
  omega
/-- Acquired-cache extraction is linear in actual input bytes and actual output field count. -/
theorem readyBound_linear (rank q:Nat) (words:List (List Bool)) :
    readyBound rank q words≤1000*((vectorBits words).length+q*(rank+1)+1) :=by
  have hl:=loopBudget_le rank q words
  have hd:=drop_vector_length_le (q*rank) words
  have hc:=chunkMass_le rank q words
  have hv:=SemiprimeD1StackNetworkRowsEncoding.vector_length words
  change (vectorBits words).length=2*wordMass words+2*words.length+1 at hv
  unfold readyBound
  rw [history_length]
  nlinarith
/-- Four-input whole-source resource, paying decoded bounded control dimensions explicitly. -/
def resource (axes:List Nat) (precision:List Bool) (q:Nat) (words:List (List Bool)) :Nat :=
  SemiprimeD1StackJetContextBounds.resource axes precision+(vectorBits words).length+q*(axes.prod+1)+1
/-- Own SAMEwhole-source fixed quadratic; precision VALUE is already inside the context resource. -/
theorem timeBound_le (axes:List Nat) (hp:∀r∈axes,0<r) (precision:List Bool) (q:Nat)
    (words:List (List Bool)) :timeBound axes precision q words≤10000*(resource axes precision q words+1)^2 :=by
  have hx:=SemiprimeD1StackJetContextBounds.budget_polynomial axes hp precision
  have hr:=readyBound_linear axes.prod q words
  have ha:SemiprimeD1StackJetContextBounds.resource axes precision≤resource axes precision q words:=by
    unfold resource;omega
  have hb:(vectorBits words).length+q*(axes.prod+1)+1≤resource axes precision q words:=by
    unfold resource;omega
  have hc:1000*(SemiprimeD1StackJetContextBounds.resource axes precision+1)^2≤
      1000*(resource axes precision q words+1)^2:=by gcongr
  unfold timeBound
  nlinarith
/-- Entire actual four-input program with a uniform fixed polynomial cap on its OWNclock. -/
theorem source_run_bounded (axes:List Nat) (hp:∀r∈axes,0<r) (precision:List Bool) (q:Nat)
    (words:List (List Bool)) :
    ∃t≤10000*(resource axes precision q words+1)^2,
      SemiprimeD1StackCalls.run program t (source axes precision q words)=
        some (done (contextResult axes precision) axes.prod q words) :=by
  obtain ⟨t,ht,he⟩:=source_run axes hp precision q words
  exact ⟨t,ht.trans (timeBound_le axes hp precision q words),he⟩
/-- Actual same ready-program extraction with a linear cap, without reacquiring any old context word. -/
theorem ready_run_linear (context:X.Stack→List Bool) (rank q:Nat)
    (hr:context X.rankCache=List.replicate rank true) (words:List (List Bool)) :
    ∃t≤1000*((vectorBits words).length+q*(rank+1)+1),
      SemiprimeD1StackCalls.run program t (ready context q words)=some (done context rank q words) :=by
  obtain ⟨t,ht,he⟩:=ready_run context rank q hr words
  exact ⟨t,ht.trans (readyBound_linear rank q words),he⟩
end RiemannGaussian.SemiprimeD1StackJetBlocksBounds
