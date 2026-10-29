/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyEncoding
/-! # Structural physical dictionary widths; no bound is supplied to the program -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyBytes
open SemiprimeD1StackSourceKeyFrequencyEncoding
open SemiprimeSourceHistogramKeyBits (frame_length)
/-- Actual retained-record count and every physical raw/counter/max width. -/
structure Sized (m W:Nat) (s:Summary) :Prop where
  /-- One actual override record per processed occurrence. -/
  count:s.rows.length=m
  /-- Raw payloads and growing binary counter words are physically bounded. -/
  words:∀r∈s.rows,r.1.length≤ W ∧ r.2.length≤ m
  /-- The retained maximum is an actual counter word. -/
  maximum:s.maximum.length≤ m
/-- A first-match read is either an actual stored word or empty zero. -/
theorem read_length_le (rows:Rows) (q:List Bool) (W:Nat) (h:∀r∈rows,r.2.length≤ W) :
    (read rows q).length≤ W :=by
  induction rows with
  | nil=>exact Nat.zero_le _
  | cons r rows ih=>
    unfold SemiprimeD1StackSourceKeyFrequencyEncoding.read coded
    simp only [List.map_cons,SemiprimeD1StackOwnerLookup.result]
    split
    · exact h r (by simp)
    · exact ih (fun r hr=>h r (by simp [hr]))
/-- Every unread suffix is an actually retained suffix of the complete dictionary, including its terminal tag. -/
theorem unread_length_le (rows:Rows) (raw:List Bool) :(unread rows raw).length≤(dictionary rows).length :=by
  induction rows with
  | nil=>exact Nat.zero_le _
  | cons r rows ih=>
    unfold unread coded
    simp only [List.map_cons,SemiprimeD1StackOwnerLookup.result]
    have hd:(dictionary (r::rows)).length=2*((encoded r.1).length+r.2.length)+3+(dictionary rows).length:=by
      simp only [dictionary,coded,List.map_cons,SemiprimeD1StackOwnerLookup.records,List.length_cons,frame_length]
      omega
    split
    · change (dictionary rows).length≤_
      omega
    · change (unread rows raw).length≤_
      omega
/-- Empty actual source has no record or counter bytes. -/
theorem empty_sized (W:Nat) :Sized 0 W empty :=by
  refine ⟨rfl,?_,le_rfl⟩
  intro r hr;cases hr
/-- The actual compact increment grows by at most one bit; retaining old records keeps every width charged. -/
theorem step_sized (m W:Nat) (s:Summary) (raw:List Bool) (h:Sized m W s) (hr:raw.length≤ W) :
    Sized (m+1) W (step s raw) :=by
  have hold:(read s.rows raw).length≤ m:=read_length_le s.rows raw m (fun r hh=>(h.words r hh).2)
  have hn:(nextCount s.rows raw).length≤ m+1:=by
    exact (SemiprimeD1StackSourceEnvironmentEncoding.successor_length _).trans (by omega)
  refine ⟨?_,?_,?_⟩
  · change s.rows.length+1=m+1;rw [h.count]
  · intro r hh
    rcases List.mem_cons.mp hh with he|he
    · subst r;exact ⟨hr,hn⟩
    · exact ⟨(h.words r he).1,(h.words r he).2.trans (by omega)⟩
  · change (nextMaximum s.maximum (nextCount s.rows raw)).length≤ m+1
    unfold nextMaximum
    split_ifs
    · exact hn
    · exact h.maximum.trans (by omega)
/-- Every physically retained old key and old counter contributes to this exact serialized dictionary bound. -/
theorem dictionary_length (m W:Nat) (s:Summary) (h:Sized m W s) :
    (dictionary s.rows).length≤ m*(2*(W+1+m)+3)+1 :=by
  have hp:∀row∈s.rows,2*((encoded row.1).length+row.2.length)+3≤2*(W+1+m)+3:=by
    intro row hr
    have hh:=h.words row hr
    simp only [encoded,List.length_append,List.length_singleton]
    omega
  have hg:∀rows:Rows,(∀row∈rows,2*((encoded row.1).length+row.2.length)+3≤2*(W+1+m)+3)→
      (dictionary rows).length≤rows.length*(2*(W+1+m)+3)+1:=by
    intro rows
    induction rows with
    | nil=>intro _;simp [dictionary,coded,SemiprimeD1StackOwnerLookup.records]
    | cons r rows ih=>
      intro hh
      have hr:=hh r (by simp)
      have ht:=ih (fun row hrow=>hh row (by simp [hrow]))
      have he:(dictionary (r::rows)).length=2*((encoded r.1).length+r.2.length)+3+(dictionary rows).length:=by
        simp only [dictionary,coded,List.map_cons,SemiprimeD1StackOwnerLookup.records,List.length_cons,frame_length]
        omega
      rw [he,List.length_cons]
      nlinarith
  have hh:=hg s.rows hp
  rw [h.count] at hh
  exact hh
/-- Every original raw word is bounded by the actually acquired vector bytes. -/
theorem raw_length_le (keys:List (List Bool)) (raw:List Bool) (h:raw∈keys) :
    raw.length≤(SemiprimeD1TensorTapeCodec.vectorBits keys).length :=by
  induction keys with
  | nil=>cases h
  | cons key keys ih=>
    rcases List.mem_cons.mp h with he|he
    · subst raw
      simp only [SemiprimeD1TensorTapeCodec.vectorBits,List.length_cons,frame_length]
      omega
    · have ht:=ih he
      simp only [SemiprimeD1TensorTapeCodec.vectorBits,List.length_cons,frame_length]
      omega
/-- Input framing physically pays the number of occurrences and every key byte. -/
theorem input_bounds (keys:List (List Bool)) :
    1≤ inputSize keys ∧ keys.length≤ inputSize keys ∧ ∀raw∈keys,raw.length≤ inputSize keys :=by
  have hv:=SemiprimeD1TensorTapeCodec.vectorBits_length keys
  refine ⟨by unfold inputSize;omega,by unfold inputSize;omega,?_⟩
  intro raw hr
  exact (raw_length_le keys raw hr).trans (by unfold inputSize;omega)
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyBytes
