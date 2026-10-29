/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesOperations
/-! # Whole actual inner binary-owner scan and ordered pair log
Each real owner field is parsed, normalized by the real trim routine, framed
with the retained factor key and counted once. Parallel/repeated owners remain
separate emitted occurrences; all input/counter/factor caches survive.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrencesOwners
open SemiprimeD1StackSourceOccurrences SemiprimeD1StackSourceOccurrencesPrimitives
open SemiprimeD1StackSourceOccurrencesView SemiprimeD1StackSourceOccurrencesEncoding
open SemiprimeD1StackSourceOccurrencesOperations SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1StackNetworkOwnerIndexEncoding (pairBytes payload)
local notation "ctl" => Label.local
/-- Exact original ordered compact-owner/factor pairs for one actual physical inner row. -/
def rowPairs (words:List (List Bool)) (factor:List Bool) :List (List Bool×List Bool) :=
  words.map (fun word=>(normal word,factor))
/-- Conservative sum of the actual paid owner parse/trim/emission bounds plus the final false-tag pop. -/
def ownerBudget (factor:List Bool) (words:List (List Bool)) :Nat :=
  (words.map (fun word=>100*(word.length+factor.length+1))).sum+1
/-- One actual owner field goes through real parse/validation/trim/frame/reversal/count steps. -/
theorem owner_step (source number reader tail counter factor hist factors occurrences word:List Bool) :
    ∃q≤100*(word.length+factor.length+1),Runs program q (ctl .ownerTag)
      (data source number reader (true::frame word tail) [] [] counter [] factor hist factors occurrences)
      (ctl .ownerTag) (data source number reader tail [] [] counter [] factor
        ((pairBytes (normal word,factor)).reverse++hist) factors (true::occurrences)) :=by
  let b0:=data source number reader (true::frame word tail) [] [] counter [] factor hist factors occurrences
  let b1:=data source number reader (frame word tail) [] [] counter [] factor hist factors occurrences
  let parsed:=data source number reader tail word [] counter [] factor hist factors occurrences
  let normalized:=data source number reader tail [] [] counter (normal word) factor hist factors occurrences
  have h0:Runs program 1 (ctl .ownerTag) b0 (ctl .ownerField) b1:=by
    apply one_base program (ctl .ownerTag) (ctl .ownerField)
      (.pop .row (ctl .abort) (ctl .clearFactor) (ctl .ownerField)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  have h1:=field_call .owner .ownerField .ownerValid rfl b1 word tail rfl rfl rfl rfl
  have he1:Function.update (Function.update (Function.update b1 (fieldInput .owner) tail)
      (fieldOutput .owner) word) .valid [true]=Function.update parsed .valid [true]:=by
    funext k;cases k <;> simp [b1,parsed,fieldInput,fieldOutput,fieldStack,data,Function.update]
  rw [he1] at h1
  have h2:Runs program 1 (ctl .ownerValid) (Function.update parsed .valid [true]) (ctl (.normalizeReverse .owner)) parsed:=by
    apply one_base program (ctl .ownerValid) (ctl (.normalizeReverse .owner))
      (.pop .valid (ctl .abort) (ctl .abort) (ctl (.normalizeReverse .owner))) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  obtain ⟨a,ha,h3⟩:=normalize_run .owner parsed word rfl rfl rfl rfl rfl
  have he3:Function.update (Function.update parsed .word []) (trimStack .owner .output) (normal word)=normalized:=by
    dsimp only [parsed,normalized,trimStack]
    rw [data_word,data_ownerKey]
  rw [he3] at h3
  have h4:=emit_pair normalized (normal word) factor hist occurrences rfl rfl rfl rfl rfl rfl
  have he4:Function.update (emitAfter normalized (normal word) factor hist) .occurrences (true::occurrences)=
      data source number reader tail [] [] counter [] factor ((pairBytes (normal word,factor)).reverse++hist)
        factors (true::occurrences):=by
    funext k;cases k <;> simp [emitAfter,normalized,data,Function.update]
  rw [he4] at h4
  have h:=join (join (join (join h0 h1) h2) h3) h4
  refine ⟨1+(8*word.length+7)+1+a+(10*factor.length+11*(normal word).length+22),?_,h⟩
  have hn:=normal_length word
  omega
/-- Whole actual inner row loop retains every occurrence in exact original order. -/
theorem owners_loop (source number reader counter factor hist factors occurrences:List Bool) (words:List (List Bool)) :
    ∃q≤ownerBudget factor words,Runs program q (ctl .ownerTag)
      (data source number reader (vectorBits words) [] [] counter [] factor hist factors occurrences)
      (ctl .clearFactor) (data source number reader [] [] [] counter [] factor
        ((payload (rowPairs words factor)).reverse++hist) factors (List.replicate words.length true++occurrences)) :=by
  induction words generalizing hist occurrences with
  | nil=>
    refine ⟨1,by simp only [ownerBudget,List.map_nil,List.sum_nil,Nat.zero_add];omega,?_⟩
    apply one_base program (ctl .ownerTag) (ctl .clearFactor)
      (.pop .row (ctl .abort) (ctl .clearFactor) (ctl .ownerField)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons word words ih=>
    obtain ⟨a,ha,h0⟩:=owner_step source number reader (vectorBits words) counter factor hist factors occurrences word
    obtain ⟨b,hb,h1⟩:=ih ((pairBytes (normal word,factor)).reverse++hist) (true::occurrences)
    have hm:List.replicate words.length true++true::occurrences=List.replicate (words.length+1) true++occurrences:=by
      calc
        _=(List.replicate words.length true++List.replicate 1 true)++occurrences:=by
          simp only [List.replicate_succ,List.replicate_zero,List.append_assoc,List.singleton_append]
        _= _:=by rw [←List.replicate_add]
    rw [hm] at h1
    refine ⟨a+b,?_,?_⟩
    · simp only [ownerBudget,List.map_cons,List.sum_cons] at hb ⊢
      omega
    · have h:=join h0 h1
      rw [show vectorBits (word::words)=true::frame word (vectorBits words) from rfl]
      simpa only [rowPairs,List.map_cons,payload,List.foldr_cons,List.reverse_append,List.append_assoc,List.length_cons] using h
/-- Exact sum of actual owner-field and retained factor-key widths. -/
theorem ownerBudget_eq (factor:List Bool) (words:List (List Bool)) :
    ownerBudget factor words=100*(words.map List.length).sum+100*factor.length*words.length+100*words.length+1 :=by
  induction words with
  | nil=>simp only [ownerBudget,List.map_nil,List.sum_nil,List.length_nil,Nat.mul_zero,Nat.zero_add]
  | cons word words ih=>
    have hc:ownerBudget factor (word::words)=100*(word.length+factor.length+1)+ownerBudget factor words:=by
      simp only [ownerBudget,List.map_cons,List.sum_cons]
      omega
    rw [hc,ih]
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    ring
/-- The whole inner scan is paid by the actual physical row bytes and actual retained factor-key width. -/
theorem ownerBudget_le (factor:List Bool) (words:List (List Bool)) :
    ownerBudget factor words≤1000*(factor.length+1)*(vectorBits words).length :=by
  have hl:=SemiprimeD1StackNetworkRowsEncoding.vector_length words
  have hn:words.length≤(vectorBits words).length:=by omega
  have hb:(words.map List.length).sum≤(vectorBits words).length:=by omega
  have hz:1≤(vectorBits words).length:=by omega
  have hp:100*factor.length*words.length≤100*factor.length*(vectorBits words).length:=by gcongr
  have he:1000*(factor.length+1)*(vectorBits words).length=
      1000*(factor.length*(vectorBits words).length)+1000*(vectorBits words).length:=by ring
  rw [ownerBudget_eq,he]
  simp only [Nat.mul_assoc] at hp ⊢
  omega
end RiemannGaussian.SemiprimeD1StackSourceOccurrencesOwners
