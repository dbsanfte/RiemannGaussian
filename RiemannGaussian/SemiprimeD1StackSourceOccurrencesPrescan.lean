/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceOccurrencesSetup
/-! # Paid complete factor prescan and actual n+F+1 counter allocation
Every outer row field is genuinely parsed and drained, including the empty
inner vector. One factor marker and counter bit are physically pushed per row.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceOccurrencesPrescan
open SemiprimeD1StackSourceOccurrences SemiprimeD1StackSourceOccurrencesPrimitives
open SemiprimeD1StackSourceOccurrencesView SemiprimeD1StackSourceOccurrencesEncoding
open SemiprimeD1StackSourceOccurrencesSetup SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- One actual outer row tag, full Field parse/drain and two literal marker/bit pushes. -/
theorem pre_row (source number tail counter factors:List Bool) (row:List (List Bool)) :
    Runs program (9*(vectorBits row).length+12) (ctl .preTag)
      (data source number (true::frame (vectorBits row) tail) [] [] [] counter [] [] [] factors []) (ctl .preTag)
      (data source number tail [] [] [] (false::counter) [] [] [] (true::factors) []) :=by
  let bytes:=vectorBits row
  let b0:=data source number (true::frame bytes tail) [] [] [] counter [] [] [] factors []
  let b1:=data source number (frame bytes tail) [] [] [] counter [] [] [] factors []
  let b2:=data source number tail bytes [] [] counter [] [] [] factors []
  let b3:=data source number tail [] [] [] counter [] [] [] factors []
  let b4:=data source number tail [] [] [] (false::counter) [] [] [] factors []
  let b5:=data source number tail [] [] [] (false::counter) [] [] [] (true::factors) []
  have h0:Runs program 1 (ctl .preTag) b0 (ctl .preField) b1:=by
    apply one_base program (ctl .preTag) (ctl .preField)
      (.pop .reader (ctl .abort) (ctl .copyInit) (ctl .preField)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  have h1:=field_call .row .preField .preValid rfl b1 bytes tail rfl rfl rfl rfl
  have he:Function.update (Function.update (Function.update b1 (fieldInput .row) tail)
      (fieldOutput .row) bytes) .valid [true]=Function.update b2 .valid [true]:=by
    funext k;cases k <;> simp [b1,b2,fieldInput,fieldOutput,fieldStack,data,Function.update]
  rw [he] at h1
  have h2:Runs program 1 (ctl .preValid) (Function.update b2 .valid [true]) (ctl .preDrain) b2:=by
    apply one_base program (ctl .preValid) (ctl .preDrain)
      (.pop .valid (ctl .abort) (ctl .abort) (ctl .preDrain)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  have h3:=drain_loop .preDrain (ctl .prePushBit) .row rfl b2 bytes rfl
  have he3:Function.update b2 .row []=b3:=data_row _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [he3] at h3
  have h4:Runs program 1 (ctl .prePushBit) b3 (ctl .preCount) b4:=by
    apply one_base program (ctl .prePushBit) (ctl .preCount) (.push .counter false (ctl .preCount)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  have h5:Runs program 1 (ctl .preCount) b4 (ctl .preTag) b5:=by
    apply one_base program (ctl .preCount) (ctl .preTag) (.push .factors true (ctl .preTag)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  have h:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  convert h using 1; dsimp only [bytes]; omega
/-- Actual prescan clock, summing complete physical row-field bytes and one real EOF pop. -/
def prescanTime (rows:List (List (List Bool))) :Nat :=
  (rows.map (fun row=>9*(vectorBits row).length+12)).sum+1
/-- Every factor row is parsed once and counted once, while both actual input tapes remain retained. -/
theorem pre_loop (source number:List Bool) (rows:List (List (List Bool))) (counter factors:List Bool) :
    Runs program (prescanTime rows) (ctl .preTag)
      (data source number (inputTape rows) [] [] [] counter [] [] [] factors []) (ctl .copyInit)
      (data source number [] [] [] [] (List.replicate rows.length false++counter) [] [] []
        (List.replicate rows.length true++factors) []) :=by
  induction rows generalizing counter factors with
  | nil=>
    apply one_base program (ctl .preTag) (ctl .copyInit)
      (.pop .reader (ctl .abort) (ctl .copyInit) (ctl .preField)) _ _ rfl
    · rfl
    · funext k;cases k <;> rfl
  | cons row rows ih=>
    have h0:=pre_row source number (inputTape rows) counter factors row
    have h1:=ih (false::counter) (true::factors)
    have hc:List.replicate rows.length false++false::counter=List.replicate (rows.length+1) false++counter:=by
      calc
        _=(List.replicate rows.length false++List.replicate 1 false)++counter:=by
          simp only [List.replicate_succ,List.replicate_zero,List.append_assoc,List.singleton_append]
        _= _:=by rw [←List.replicate_add]
    have hf:List.replicate rows.length true++true::factors=List.replicate (rows.length+1) true++factors:=by
      calc
        _=(List.replicate rows.length true++List.replicate 1 true)++factors:=by
          simp only [List.replicate_succ,List.replicate_zero,List.append_assoc,List.singleton_append]
        _= _:=by rw [←List.replicate_add]
    rw [hc,hf] at h1
    have h:=join h0 h1
    rw [show inputTape (row::rows)=true::frame (vectorBits row) (inputTape rows) from rfl]
    simpa only [prescanTime,List.map_cons,List.sum_cons,Nat.add_assoc,List.length_cons] using h
/-- Own actual whole source prefix includes the real n allocation, complete retained row copy and full factor prescan. -/
def acquisitionTime (n:Nat) (rows:List (List (List Bool))) :Nat :=
  7*n+5*(inputTape rows).length+prescanTime rows+10
/-- Actual n-only marker allocation plus complete original row prescan constructs its own width and F cache. -/
theorem source_prescan (n:Nat) (rows:List (List (List Bool))) :
    Runs program (acquisitionTime n rows) (ctl .start) (initial (inputTape rows) (List.replicate n true)).data (ctl .copyInit)
      (data (inputTape rows) (List.replicate n true) [] [] [] []
        (List.replicate (n+rows.length+1) false) [] [] [] (List.replicate rows.length true) []) :=by
  let number:=List.replicate n true
  let zero:=List.replicate (n+1) false
  let bank:=data (inputTape rows) number [] [] [] [] zero [] [] [] [] []
  have h0:=source_width (inputTape rows) n
  have h1:=copy_call .rows .preCopy .preTag rfl bank (inputTape rows) [] rfl rfl rfl
  simp only [List.append_nil] at h1
  change Runs program (5*(inputTape rows).length+4) _ bank _ (Function.update bank .reader (inputTape rows)) at h1
  have he1:Function.update bank .reader (inputTape rows)=
      data (inputTape rows) number (inputTape rows) [] [] [] zero [] [] [] [] []:=data_reader _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [he1] at h1
  have h2:=pre_loop (inputTape rows) number rows zero []
  have he2:List.replicate rows.length false++zero=List.replicate (n+rows.length+1) false:=by
    dsimp only [zero]
    rw [←List.replicate_add]
    congr 1
    omega
  simp only [he2,List.append_nil] at h2
  have h:=join (join h0 h1) h2
  unfold acquisitionTime
  convert h using 1; omega
end RiemannGaussian.SemiprimeD1StackSourceOccurrencesPrescan
