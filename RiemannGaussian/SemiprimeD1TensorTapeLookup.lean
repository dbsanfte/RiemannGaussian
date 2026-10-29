/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1TensorTapeCodec

/-! # Sequential physical tensor-table tape lookup
The unselected subtree is actually traversed and discarded. No native table
pointer or random-access operation occurs in the lookup runtime.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeD1TensorTapeLookup
open SemiprimeD1TensorTables SemiprimeD1TensorTapeCodec

/-- Scan past one tagged table, including all unselected coefficient payloads. -/
def skip : ℕ → List Bool → Parsed
  | 0,[] => ⟨[],[],2⟩
  | 0,_::tail => let out:=parseVector tail; ⟨[],out.rest,out.clock+3⟩
  | _+1,[] => ⟨[],[],2⟩
  | n+1,_::tail =>
    let low:=skip n tail
    let high:=skip n low.rest
    ⟨[],high.rest,low.clock+high.clock+5⟩

/-- Actual assignment-bit-controlled sequential lookup, preserving the tail. -/
def read : ℕ → List Bool → List Bool → Parsed
  | 0,_,[] => ⟨[],[],2⟩
  | 0,_,_::tail => let out:=parseVector tail; ⟨out.words,out.rest,out.clock+3⟩
  | _+1,_,[] => ⟨[],[],2⟩
  | n+1,bits,_::tail =>
    if bits.head?.getD false then
      let low:=skip n tail
      let high:=read n bits.tail low.rest
      ⟨high.words,high.rest,low.clock+high.clock+7⟩
    else
      let low:=read n bits.tail tail
      let high:=skip n low.rest
      ⟨low.words,high.rest,low.clock+high.clock+7⟩

/-- Skipping an actual serialized table reaches its exact following tape. -/
theorem skip_correct {n : ℕ} (table : Table n) (tail : List Bool) :
    (skip n (tape table++tail)).rest=tail := by
  induction table generalizing tail with
  | leaf words => simpa only [tape,List.cons_append,skip] using (parseVector_correct words tail).2
  | fork low high ihl ihh =>
    simp only [tape,List.cons_append,List.append_assoc,skip,ihl,ihh]

/-- The actual fixed-scope table code cannot be a proper prefix of another. -/
theorem prefix_free {n : ℕ} (table other : Table n) (suffix : List Bool)
    (h : tape other=tape table++suffix) : suffix=[] := by
  have hl:=skip_correct table suffix
  have hr:=skip_correct other []
  simp only [List.append_nil] at hr
  rw [←h] at hl
  exact hl.symm.trans hr

/-- Physical sequential lookup preserves the literal original coefficient words. -/
theorem read_correct {n : ℕ} (table : Table n) (bits tail : List Bool) :
    (read n bits (tape table++tail)).words=(lookup table bits).words ∧
      (read n bits (tape table++tail)).rest=tail := by
  induction table generalizing bits tail with
  | leaf words =>
    have h:=parseVector_correct words tail
    simp only [tape,List.cons_append,read,lookup,SemiprimeD1JetAxes.copyVector_value,h.1,h.2,and_self]
  | @fork n low high ihl ihh =>
    have hl:=ihl bits.tail (tape high++tail)
    have hh:=ihh bits.tail tail
    simp only [tape,List.cons_append,List.append_assoc,read,lookup]
    split_ifs
    · simp only [skip_correct,hh.1,hh.2,and_self]
    · simp only [hl.1,hl.2,skip_correct,and_self]

/-- All unselected subtree scans and copied fields cost linear actual tape work. -/
theorem skip_clock {n : ℕ} (table : Table n) (tail : List Bool) :
    (skip n (tape table++tail)).clock ≤ 8*(tape table).length := by
  induction table generalizing tail with
  | leaf words =>
    have h:=parseVector_clock words tail
    simp only [tape,List.cons_append,skip,List.length_cons]
    omega
  | fork low high ihl ihh =>
    have hl:=ihl (tape high++tail)
    have hh:=ihh tail
    simp only [tape,List.cons_append,List.append_assoc,skip,skip_correct,List.length_cons,List.length_append]
    omega

/-- The selected and unselected branches are both actually paid, never free skips. -/
theorem read_clock {n : ℕ} (table : Table n) (bits tail : List Bool) :
    (read n bits (tape table++tail)).clock ≤ 8*(tape table).length := by
  induction table generalizing bits tail with
  | leaf words =>
    have h:=parseVector_clock words tail
    simp only [tape,List.cons_append,read,List.length_cons]
    omega
  | @fork n low high ihl ihh =>
    have hl:=ihl bits.tail (tape high++tail)
    have hh:=ihh bits.tail tail
    have hsl:=skip_clock low (tape high++tail)
    have hsh:=skip_clock high tail
    have hrl:=(read_correct low bits.tail (tape high++tail)).2
    simp only [tape,List.cons_append,List.append_assoc,read,skip_correct,List.length_cons,List.length_append]
    split_ifs
    · dsimp only
      omega
    · rw [hrl]
      dsimp only
      omega

/-- Closed serialization and sequential lookup, retaining both actual reports. -/
def fromTable {n : ℕ} (table : Table n) (bits : List Bool) : SemiprimeD1JetRingBits.Run :=
  let encoded:=serialize table
  let out:=read n bits encoded.bits
  ⟨out.words,encoded.clock+out.clock+4⟩

/-- No serialized bank or value advice is needed by the closed table endpoint. -/
theorem fromTable_words {n : ℕ} (table : Table n) (bits : List Bool) :
    (fromTable table bits).words=(lookup table bits).words := by
  have h:=(read_correct table bits []).1
  simpa only [fromTable,serialize_bits,List.append_nil] using h

/-- Setup copies and unselected scans are included in the full actual report. -/
theorem fromTable_clock {n : ℕ} (table : Table n) (bits : List Bool) :
    (fromTable table bits).clock ≤ 8*(n+2)*(tape table).length+4 := by
  have hs:=serialize_clock table
  have hr:=read_clock table bits []
  simp only [List.append_nil] at hr
  simp only [fromTable,serialize_bits]
  nlinarith

/-- Original canonical coefficient/degree caps bound the complete physical path. -/
theorem fromTable_good_clock (ctx : SemiprimeD1JetAxes.Context) {n : ℕ} (table : Table n)
    (hg : Good ctx table) (bits : List Bool) :
    (fromTable table bits).clock ≤
      8*(n+2)*((2*ctx.rank*(ctx.precision+1)+3)*2^n)+4 := by
  apply (fromTable_clock table bits).trans
  have h:=tape_length ctx table hg
  gcongr
  omega

/-- Literal tree depth is itself bounded by its acquired serialized storage. -/
theorem tape_depth {n : ℕ} (table : Table n) : n+1 ≤ (tape table).length := by
  induction table with
  | leaf words => simp only [tape,List.length_cons];omega
  | fork low high ihl ihh =>
    simp only [tape,List.length_cons,List.length_append]
    omega

/-- A quadratic actual-tape bound requires no caller-supplied degree cap. -/
theorem fromTable_storage_clock {n : ℕ} (table : Table n) (bits : List Bool) :
    (fromTable table bits).clock ≤ 8*((tape table).length+1)*(tape table).length+4 := by
  apply (fromTable_clock table bits).trans
  have h:=tape_depth table
  exact Nat.add_le_add_right (Nat.mul_le_mul_right _
    (Nat.mul_le_mul_left 8 (by omega : n+2 ≤ (tape table).length+1))) 4

end RiemannGaussian.SemiprimeD1TensorTapeLookup
