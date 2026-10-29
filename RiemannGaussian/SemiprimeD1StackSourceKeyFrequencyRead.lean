/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyEncoding
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyCalls
/-! # Paid sentinel-key acquisition and physical first-match frequency scan -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyRead
open SemiprimeD1StackSourceKeyFrequency SemiprimeD1StackSourceKeyFrequencyEncoding
open SemiprimeD1StackSourceKeyFrequencyPrimitives SemiprimeD1StackSourceKeyFrequencyCalls
open SemiprimeD1StackProcedureTrace
/-- Every retained old dictionary record and unread tail is paid by the real copy/read/drain. -/
def lookupClock (rows:Rows) (raw:List Bool) :Nat :=5*raw.length+7+5*(dictionary rows).length+4+
  SemiprimeD1StackOwnerLookupBounds.runBound (encoded raw) (coded rows)+1+(unread rows raw).length+1
/-- The old count is obtained from actual dictionary bytes, never from a supplied frequency. -/
theorem read_run (src reader raw:List Bool) (s:Summary) :
    ∃q≤lookupClock s.rows raw,Runs program q .encode
      (bank {loopWords src reader s with raw:=raw}) .successor
      (bank {loopWords src reader s with raw:=raw,query:=encoded raw,oldCount:=read s.rows raw}) :=by
  let w0:Words:={loopWords src reader s with raw:=raw}
  let w1:Words:={w0 with query:=encoded raw}
  let w2:Words:={w1 with lookupReader:=dictionary s.rows}
  let w3:Words:={w2 with lookupReader:=unread s.rows raw,oldCount:=read s.rows raw}
  let w4:Words:={w3 with lookupReader:=[]}
  have h0:=sentinel_call (bank w0) raw rfl rfl rfl
  rw [update_query] at h0
  change Runs program (5*raw.length+7) .encode (bank w0) .copyDictionary (bank w1) at h0
  have h1:=copy_call .dictionary .copyDictionary .lookup rfl (bank w1) (dictionary s.rows) [] rfl rfl rfl
  change Runs program (5*(dictionary s.rows).length+4) .copyDictionary (bank w1) .lookup
    (Function.update (bank w1) (lookupStack (.inr .reader)) (dictionary s.rows++[])) at h1
  rw [List.append_nil,update_lookupReader] at h1
  change Runs program (5*(dictionary s.rows).length+4) .copyDictionary (bank w1) .lookup (bank w2) at h1
  obtain ⟨q,hq,h2⟩:=lookup_call (bank w2) (encoded raw) (coded s.rows) (by
    intro k;rcases k with k|k <;> cases k <;> rfl)
  have he:Sum.elim (SemiprimeD1StackOwnerLookup.done (encoded raw) (coded s.rows) []).data
      (fun k=>bank w2 (aux k))=bank w3:=by
    funext k;rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> rfl
  rw [he] at h2
  have h3:=drain_loop .clearReader .successor (lookupStack (.inr .reader)) rfl (bank w3) (unread s.rows raw) rfl
  rw [update_lookupReader] at h3
  change Runs program ((unread s.rows raw).length+1) .clearReader (bank w3) .successor (bank w4) at h3
  refine ⟨_,?_,join (join (join h0 h1) h2) h3⟩
  unfold lookupClock
  omega
/-- Both actual framing delimiter and actual parser-valid singleton are consumed before lookup. -/
theorem parse_run (src raw tail:List Bool) (s:Summary) :
    Runs program (8*raw.length+9) .header
      (bank (loopWords src (true::SemiprimeSourceHistogramKeyBits.frame raw tail) s)) .encode
      (bank {loopWords src tail s with raw:=raw}) :=by
  let w0:=loopWords src (true::SemiprimeSourceHistogramKeyBits.frame raw tail) s
  let w1:Words:={w0 with reader:=SemiprimeSourceHistogramKeyBits.frame raw tail}
  let w2:Words:={w1 with reader:=tail,raw:=raw,valid:=[true]}
  let w3:Words:={w2 with valid:=[]}
  have h0:=pop_run .header .abort .eof .parse (aux .reader) (bank w0)
    (true::SemiprimeSourceHistogramKeyBits.frame raw tail) rfl rfl
  rw [update_reader] at h0
  change Runs program 1 .header (bank w0) .parse (bank w1) at h0
  have h1:=field_call .parse .valid rfl (bank w1) raw tail rfl rfl rfl rfl
  rw [update_reader,update_raw,update_valid] at h1
  change Runs program (8*raw.length+7) .parse (bank w1) .valid (bank w2) at h1
  have h2:=pop_run .valid .abort .abort .encode (lookupStack (.inr .valid)) (bank w2) [true] rfl rfl
  rw [update_valid] at h2
  change Runs program 1 .valid (bank w2) .encode (bank w3) at h2
  convert join (join h0 h1) h2 using 1 <;> first | omega | rfl
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyRead
