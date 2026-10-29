/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyEncoding
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyPrimitives
/-! # Paid two-field override framing and complete raw/count/query cleanup -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyStore
open SemiprimeD1StackSourceKeyFrequency SemiprimeD1StackSourceKeyFrequencyEncoding
open SemiprimeD1StackSourceKeyFrequencyPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Both preserved fields, actual record tag and all three EOF drains belong to this source. -/
def storeClock (raw count:List Bool) :Nat :=6*count.length+5+(6*(encoded raw).length+5)+1+
  (raw.length+1)+((encoded raw).length+1)+(count.length+1)
/-- One physical head insertion retains the entire old tail without a tail copy; all obsolete records remain charged. -/
theorem store_run (src reader raw count maximum:List Bool) (rows:Rows) :
    Runs program (storeClock raw count) .frameCount
      (bank {loopWords src reader ⟨rows,maximum⟩ with raw:=raw,query:=encoded raw,count:=count}) .header
      (bank (loopWords src reader ⟨(raw,count)::rows,maximum⟩)) :=by
  let w0:Words:={loopWords src reader ⟨rows,maximum⟩ with raw:=raw,query:=encoded raw,count:=count}
  let w1:Words:={w0 with dictionary:=frame count (dictionary rows)}
  let w2:Words:={w1 with dictionary:=frame (encoded raw) (frame count (dictionary rows))}
  let w3:Words:={w2 with dictionary:=true::w2.dictionary}
  let w4:Words:={w3 with raw:=[]}
  let w5:Words:={w4 with query:=[]}
  let w6:Words:={w5 with count:=[]}
  have h0:=frame_call .count .frameCount .frameKey rfl (bank w0) count (dictionary rows) rfl rfl rfl
  change Runs program (6*count.length+5) .frameCount (bank w0) .frameKey (Function.update (bank w0) (aux .dictionary) (frame count (dictionary rows))) at h0
  rw [update_dictionary] at h0
  have h1:=frame_call .key .frameKey .tag rfl (bank w1) (encoded raw) (frame count (dictionary rows)) rfl rfl rfl
  change Runs program (6*(encoded raw).length+5) .frameKey (bank w1) .tag (Function.update (bank w1) (aux .dictionary) (frame (encoded raw) (frame count (dictionary rows)))) at h1
  rw [update_dictionary] at h1
  have h2:=push_run .tag .clearRaw (aux .dictionary) true (bank w2) rfl
  rw [update_dictionary] at h2
  have h3:=drain_loop .clearRaw .clearQuery (aux .raw) rfl (bank w3) raw rfl
  rw [update_raw] at h3
  have h4:=drain_loop .clearQuery .clearCount query rfl (bank w4) (encoded raw) rfl
  rw [update_query] at h4
  have h5:=drain_loop .clearCount .header (aux .count) rfl (bank w5) count rfl
  rw [update_count] at h5
  exact join (join (join (join (join h0 h1) h2) h3) h4) h5
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyStore
