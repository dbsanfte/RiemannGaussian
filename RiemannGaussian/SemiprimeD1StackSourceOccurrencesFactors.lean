/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesOwners
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesCounter
/-! # Whole original factor traversal and paid namespace-key successors
The actual factor counter advances for EVERY row, including an empty row.
Every field, normalization, retained factor-key copy, pair and marker is paid
by this same finite source; there is no arity or routing getter operand.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrencesFactors
open SemiprimeD1StackSourceOccurrences SemiprimeD1StackSourceOccurrencesPrimitives
open SemiprimeD1StackSourceOccurrencesView SemiprimeD1StackSourceOccurrencesEncoding
open SemiprimeD1StackSourceOccurrencesOperations SemiprimeD1StackSourceOccurrencesOwners
open SemiprimeD1StackSourceOccurrencesCounter SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeD1StackNetworkOwnerIndexEncoding (payload)
local notation "ctl" => Label.local
/-- One actual factor row allowance in paid allocated counter width and actual physical inner-row bytes. -/
def factorBudget (n F:Nat) (row:List (List Bool)) :Nat :=
  10000*(n+F+2)*((vectorBits row).length+1)
/-- A real complete factor row emits all ordered occurrences and advances its binary key, even when the row is empty. -/
theorem factor_step (source number tail hist factors occurrences:List Bool) (n F f:Nat) (hf:f<F) (row:List (List Bool)) :
    ∃q≤factorBudget n F row,Runs program q (ctl .factorTag)
      (data source number (true::frame (vectorBits row) tail) [] [] [] (counterWord n F (n+f)) [] [] hist factors occurrences)
      (ctl .factorTag) (data source number tail [] [] [] (counterWord n F (n+(f+1))) [] []
        ((payload (rowPairs row (Keys.numberKey (n+f)))).reverse++hist) factors
        (List.replicate row.length true++occurrences)) :=by
  let counter:=counterWord n F (n+f)
  let key:=Keys.numberKey (n+f)
  let bytes:=vectorBits row
  let b0:=data source number (true::frame bytes tail) [] [] [] counter [] [] hist factors occurrences
  let b1:=data source number (frame bytes tail) [] [] [] counter [] [] hist factors occurrences
  let parsed:=data source number tail bytes [] [] counter [] [] hist factors occurrences
  let copied:=data source number tail bytes counter [] counter [] [] hist factors occurrences
  let normalized:=data source number tail bytes [] [] counter [] key hist factors occurrences
  let logged:=data source number tail [] [] [] counter [] key
    ((payload (rowPairs row key)).reverse++hist) factors (List.replicate row.length true++occurrences)
  let cleared:=data source number tail [] [] [] counter [] []
    ((payload (rowPairs row key)).reverse++hist) factors (List.replicate row.length true++occurrences)
  have h0:Runs program 1 (ctl .factorTag) b0 (ctl .rowField) b1:=by
    apply one_base program (ctl .factorTag) (ctl .rowField)
      (.pop .reader (ctl .abort) (ctl .finishSeed) (ctl .rowField)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  have h1:=field_call .row .rowField .rowValid rfl b1 bytes tail rfl rfl rfl rfl
  have he1:Function.update (Function.update (Function.update b1 (fieldInput .row) tail) (fieldOutput .row) bytes) .valid [true]=
      Function.update parsed .valid [true]:=by
    funext k;cases k <;> simp [b1,parsed,fieldInput,fieldOutput,fieldStack,data,Function.update]
  rw [he1] at h1
  have h2:Runs program 1 (ctl .rowValid) (Function.update parsed .valid [true]) (ctl .copyFactor) parsed:=by
    apply one_base program (ctl .rowValid) (ctl .copyFactor)
      (.pop .valid (ctl .abort) (ctl .abort) (ctl .copyFactor)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  have h3:=copy_call .factor .copyFactor (.normalizeReverse .factor) rfl parsed counter [] rfl rfl rfl
  simp only [List.append_nil] at h3
  change Runs program (5*counter.length+4) _ parsed _ (Function.update parsed .word counter) at h3
  have he3:Function.update parsed .word counter=copied:=data_word _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [he3] at h3
  obtain ⟨a,ha,h4⟩:=normalize_run .factor copied counter rfl rfl rfl rfl rfl
  have he4:Function.update (Function.update copied .word []) (trimStack .factor .output) (normal counter)=normalized:=by
    dsimp only [copied,normalized,trimStack]
    rw [data_word,data_factorKey,counter_key n F f (by omega)]
  rw [he4] at h4
  obtain ⟨b,hb,h5⟩:=owners_loop source number tail counter key hist factors occurrences row
  have h6:=drain_loop .clearFactor (ctl (.increment .factor)) .factorKey rfl logged key rfl
  have he6:Function.update logged .factorKey []=cleared:=data_factorKey _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [he6] at h6
  obtain ⟨c,hc,h7⟩:=counter_transfer .factor cleared n F (n+f) (by omega) rfl rfl rfl
  have he7:Function.update cleared .counter (counterWord n F (n+f+1))=
      data source number tail [] [] [] (counterWord n F (n+(f+1))) [] []
        ((payload (rowPairs row key)).reverse++hist) factors (List.replicate row.length true++occurrences):=by
    dsimp only [cleared]
    rw [data_counter,show n+f+1=n+(f+1) from by omega]
  rw [he7] at h7
  have h:=join (join (join (join (join (join (join h0 h1) h2) h3) h4) h5) h6) h7
  refine ⟨1+(8*bytes.length+7)+1+(5*counter.length+4)+a+b+(key.length+1)+c,?_,h⟩
  have hl:counter.length=n+F+1:=counter_length n F (n+f) (by omega)
  have hk:key.length≤n+F+1:=by
    have hn:=normal_length counter
    have he:normal counter=key:=counter_key n F f (by omega)
    rw [he,hl] at hn
    exact hn
  have hob:=ownerBudget_le key row
  have hmul:=Nat.mul_le_mul_right (vectorBits row).length (Nat.add_le_add_right hk 1)
  have hbound:b≤1000*(n+F+2)*(vectorBits row).length:=by
    have h0:=hb.trans hob
    have h1:=Nat.mul_le_mul_left 1000 hmul
    nlinarith only [h0,h1]
  dsimp only [factorBudget,bytes]
  rw [hl] at ha ⊢
  nlinarith only [ha,hc,hk,hbound]
/-- Actual full outer factor-loop allowance, including the real final FALSEvector-tag pop. -/
def factorsBudget (n F:Nat) (rows:List (List (List Bool))) :Nat :=(rows.map (factorBudget n F)).sum+1
/-- The actual factor scan preserves exact original order, counts every local occurrence and advances all empty rows. -/
theorem factors_loop (source number hist factors occurrences:List Bool) (n F f:Nat) (rows:List (List (List Bool)))
    (hf:f+rows.length≤F) :
    ∃q≤factorsBudget n F rows,Runs program q (ctl .factorTag)
      (data source number (inputTape rows) [] [] [] (counterWord n F (n+f)) [] [] hist factors occurrences)
      (ctl .finishSeed) (data source number [] [] [] [] (counterWord n F (n+f+rows.length)) [] []
        ((payload (pairsFrom n f rows)).reverse++hist) factors
        (List.replicate (rows.map List.length).sum true++occurrences)) :=by
  induction rows generalizing f hist occurrences with
  | nil=>
    refine ⟨1,by simp only [factorsBudget,List.map_nil,List.sum_nil,Nat.zero_add];omega,?_⟩
    apply one_base program (ctl .factorTag) (ctl .finishSeed)
      (.pop .reader (ctl .abort) (ctl .finishSeed) (ctl .rowField)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons row rows ih=>
    obtain ⟨a,ha,h0⟩:=factor_step source number (inputTape rows) hist factors occurrences n F f (by simp only [List.length_cons] at hf;omega) row
    obtain ⟨b,hb,h1⟩:=ih (hist:=((payload (rowPairs row (Keys.numberKey (n+f)))).reverse++hist))
      (occurrences:=List.replicate row.length true++occurrences) (f:=f+1) (by simp only [List.length_cons] at hf;omega)
    have hcount:List.replicate (rows.map List.length).sum true++(List.replicate row.length true++occurrences)=
        List.replicate (row.length+(rows.map List.length).sum) true++occurrences:=by
      rw [←List.append_assoc,←List.replicate_add]
      congr 2
      omega
    rw [hcount] at h1
    have hcounter:n+(f+1)+rows.length=n+f+(row::rows).length:=by simp only [List.length_cons];omega
    rw [hcounter] at h1
    refine ⟨a+b,?_,?_⟩
    · simp only [factorsBudget,List.map_cons,List.sum_cons] at hb ⊢
      omega
    · have h:=join h0 h1
      rw [show inputTape (row::rows)=true::frame (vectorBits row) (inputTape rows) from rfl]
      simpa only [pairsFrom,rowPairs,SemiprimeD1StackNetworkOwnerIndexEncoding.payload_append,List.reverse_append,List.append_assoc,
        List.map_cons,List.sum_cons] using h
end RiemannGaussian.SemiprimeD1StackSourceOccurrencesFactors
