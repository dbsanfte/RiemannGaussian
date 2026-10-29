/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequency
import RiemannGaussian.SemiprimeD1PortOwnerKeys
/-! # Proof interpretation of raw-key dictionary overrides and all actual physical words -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyEncoding
open SemiprimeD1StackSourceKeyFrequency
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Each comparison key is the actual sentinel-copy result, including for an empty raw key. -/
def encoded (raw:List Bool) :List Bool :=raw++[true]
/-- Literal raw-byte identity is equivalent to the real numeric equality on sentinel keys. -/
theorem encoded_eq (a b:List Bool) :
    SemiprimeBitArithmetic.bitValue (encoded a)=SemiprimeBitArithmetic.bitValue (encoded b) ↔ a=b :=by
  constructor
  · intro h
    have hh:=SemiprimeSourceCompactWordIds.compact_value_injective (encoded a) (encoded b)
      (SemiprimeD1PortOwnerKeys.compact_sentinel a) (SemiprimeD1PortOwnerKeys.compact_sentinel b) h
    exact List.append_cancel_right hh
  · intro h;rw [h]
/-- Raw keys remain proof-side raw lists; only their physically generated sentinel bytes are stored in actual records. -/
abbrev Rows :=List (List Bool×List Bool)
/-- Fixed record grammar carries encoded raw keys and compact binary frequency payloads. -/
def coded (rows:Rows) :Rows :=rows.map (fun row=>(encoded row.1,row.2))
/-- Exact physical dictionary including every retained obsolete newest-first override. -/
def dictionary (rows:Rows) :List Bool :=SemiprimeD1StackOwnerLookup.records (coded rows) []
/-- The real first-match result, not an evaluator supplied to the machine. -/
def read (rows:Rows) (raw:List Bool) :List Bool :=
  (SemiprimeD1StackOwnerLookup.result (encoded raw) (coded rows) []).1
/-- Physical unread tail after the same actual first-match scan. -/
def unread (rows:Rows) (raw:List Bool) :List Bool :=
  (SemiprimeD1StackOwnerLookup.result (encoded raw) (coded rows) []).2
/-- A new count is the physical compact successor of the actual old payload, with absence encoding zero. -/
def nextCount (rows:Rows) (raw:List Bool) :List Bool :=SemiprimeD1StackSourceEnvironmentEncoding.successor (read rows raw)
/-- Only the actual strict comparison Boolean controls maximum replacement. -/
def nextMaximum (maximum count:List Bool) :List Bool :=
  if SemiprimeD1StackWordLessExecution.answer maximum count then count else maximum
/-- Mathematical state describes the already physically acquired dictionary and maximum. -/
structure Summary where
  /-- All newest-first retained override records. -/
  rows:Rows
  /-- Actual compact binary maximum. -/
  maximum:List Bool
/-- One literal row's interpretation: real increment, strict maximum and head override. -/
def step (s:Summary) (raw:List Bool) :Summary :=
  ⟨(raw,nextCount s.rows raw)::s.rows,nextMaximum s.maximum (nextCount s.rows raw)⟩
/-- Empty physical dictionary and zero maximum before the first parsed raw key. -/
def empty :Summary :=⟨[],[]⟩
/-- Original chronological order and every duplicate are retained by the physical fold. -/
def acquire (keys:List (List Bool)) :Summary :=keys.foldl step empty
/-- Complete literal21-role boundary store; fields are proof-side names for physical Boolean words. -/
structure Words where
  /-- Actual source word. -/
  source:List Bool:=[]
  /-- Actual reader word. -/
  reader:List Bool:=[]
  /-- Actual raw word. -/
  raw:List Bool:=[]
  /-- Actual dictionary word. -/
  dictionary:List Bool:=[]
  /-- Actual count word. -/
  count:List Bool:=[]
  /-- Actual maximum word. -/
  maximum:List Bool:=[]
  /-- Actual incScratch word. -/
  incScratch:List Bool:=[]
  /-- Actual incNext word. -/
  incNext:List Bool:=[]
  /-- Actual trimScratch word. -/
  trimScratch:List Bool:=[]
  /-- Actual frameScratch word. -/
  frameScratch:List Bool:=[]
  /-- Actual query word. -/
  query:List Bool:=[]
  /-- Actual lookupReader word. -/
  lookupReader:List Bool:=[]
  /-- Actual left word. -/
  left:List Bool:=[]
  /-- Actual right word. -/
  right:List Bool:=[]
  /-- Actual eqScratch word. -/
  eqScratch:List Bool:=[]
  /-- Actual comparison word. -/
  comparison:List Bool:=[]
  /-- Actual valid word. -/
  valid:List Bool:=[]
  /-- Actual discard word. -/
  discard:List Bool:=[]
  /-- Actual oldCount word. -/
  oldCount:List Bool:=[]
  /-- Actual fieldScratch word. -/
  fieldScratch:List Bool:=[]
  /-- Actual copyScratch word. -/
  copyScratch:List Bool:=[]
/-- No word in the fixed physical inventory is hidden or omitted. -/
def bank (w:Words) :Stack→List Bool
  | .inr .source=>w.source
  | .inr .reader=>w.reader
  | .inr .raw=>w.raw
  | .inr .dictionary=>w.dictionary
  | .inr .count=>w.count
  | .inr .maximum=>w.maximum
  | .inr .incScratch=>w.incScratch
  | .inr .incNext=>w.incNext
  | .inr .trimScratch=>w.trimScratch
  | .inr .frameScratch=>w.frameScratch
  | .inl (.inr .query)=>w.query
  | .inl (.inr .reader)=>w.lookupReader
  | .inl (.inl .left)=>w.left
  | .inl (.inl .right)=>w.right
  | .inl (.inl .scratch)=>w.eqScratch
  | .inl (.inl .output)=>w.comparison
  | .inl (.inr .valid)=>w.valid
  | .inl (.inr .discard)=>w.discard
  | .inl (.inr .output)=>w.oldCount
  | .inl (.inr .fieldScratch)=>w.fieldScratch
  | .inl (.inr .copyScratch)=>w.copyScratch
/-- A physical source write preserves every other actual word. -/
theorem update_source (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .source) xs=bank {w with source:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical reader write preserves every other actual word. -/
theorem update_reader (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .reader) xs=bank {w with reader:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical raw write preserves every other actual word. -/
theorem update_raw (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .raw) xs=bank {w with raw:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical dictionary write preserves every other actual word. -/
theorem update_dictionary (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .dictionary) xs=bank {w with dictionary:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical count write preserves every other actual word. -/
theorem update_count (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .count) xs=bank {w with count:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical maximum write preserves every other actual word. -/
theorem update_maximum (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .maximum) xs=bank {w with maximum:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical incScratch write preserves every other actual word. -/
theorem update_incScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .incScratch) xs=bank {w with incScratch:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical incNext write preserves every other actual word. -/
theorem update_incNext (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .incNext) xs=bank {w with incNext:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical trimScratch write preserves every other actual word. -/
theorem update_trimScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .trimScratch) xs=bank {w with trimScratch:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical frameScratch write preserves every other actual word. -/
theorem update_frameScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (aux .frameScratch) xs=bank {w with frameScratch:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical query write preserves every other actual word. -/
theorem update_query (w:Words) (xs:List Bool) :
    Function.update (bank w) (query) xs=bank {w with query:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical lookupReader write preserves every other actual word. -/
theorem update_lookupReader (w:Words) (xs:List Bool) :
    Function.update (bank w) (lookupStack (.inr .reader)) xs=bank {w with lookupReader:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical left write preserves every other actual word. -/
theorem update_left (w:Words) (xs:List Bool) :
    Function.update (bank w) (lookupStack (.inl .left)) xs=bank {w with left:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical right write preserves every other actual word. -/
theorem update_right (w:Words) (xs:List Bool) :
    Function.update (bank w) (lookupStack (.inl .right)) xs=bank {w with right:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical eqScratch write preserves every other actual word. -/
theorem update_eqScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (lookupStack (.inl .scratch)) xs=bank {w with eqScratch:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical comparison write preserves every other actual word. -/
theorem update_comparison (w:Words) (xs:List Bool) :
    Function.update (bank w) (lookupStack (.inl .output)) xs=bank {w with comparison:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical valid write preserves every other actual word. -/
theorem update_valid (w:Words) (xs:List Bool) :
    Function.update (bank w) (lookupStack (.inr .valid)) xs=bank {w with valid:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical discard write preserves every other actual word. -/
theorem update_discard (w:Words) (xs:List Bool) :
    Function.update (bank w) (lookupStack (.inr .discard)) xs=bank {w with discard:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical oldCount write preserves every other actual word. -/
theorem update_oldCount (w:Words) (xs:List Bool) :
    Function.update (bank w) (oldCount) xs=bank {w with oldCount:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical fieldScratch write preserves every other actual word. -/
theorem update_fieldScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (lookupStack (.inr .fieldScratch)) xs=bank {w with fieldScratch:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- A physical copyScratch write preserves every other actual word. -/
theorem update_copyScratch (w:Words) (xs:List Bool) :
    Function.update (bank w) (copyScratch) xs=bank {w with copyScratch:=xs} :=by
  funext k;rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- Clean loop boundary retains source, unread forward vector, dictionary and maximum. -/
def loopWords (source reader:List Bool) (s:Summary) :Words :=
  {source:=source,reader:=reader,dictionary:=dictionary s.rows,maximum:=s.maximum}
/-- Sole key-vector source; no count, dictionary or maximum is prepared as an input. -/
def source (keys:List (List Bool)) :C.State Stack Label :=initial (vectorBits keys)
/-- Actual stopped21-role bank with all18 other roles empty. -/
def result (keys:List (List Bool)) :Stack→List Bool :=bank (loopWords (vectorBits keys) [] (acquire keys))
/-- Literal actual halt also clears both flags and all real source-call returns. -/
def done (keys:List (List Bool)) :C.State Stack Label :=⟨none,none,none,result keys,[]⟩
/-- Whole physical input size counts every framing bit and terminator. -/
def inputSize (keys:List (List Bool)) :Nat :=(vectorBits keys).length+1
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyEncoding
