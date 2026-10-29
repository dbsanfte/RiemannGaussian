/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogue
/-! # Complete physical views of shared N/scope and actual five-field inputs -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackFullFactorCatalogueView
open SemiprimeD1StackFullFactorCatalogue
/-- Original binary N followed by the five acquired raw descriptor fields, proof notation only. -/
def raw (bits:List Bool) (words:Fin 5→List Bool) :Fin 6→List Bool:=
  ![bits,words 0,words 1,words 2,words 3,words 4]
/-- Actual original descriptor catalogue output role. -/
def catalogueOutput :V.Stack:=V.kernelStack (SemiprimeD1StackCartesian4.aux 2)
/-- Complete1454-role store with BOTH unused N/scope shadows empty and real validity bytes. -/
def data (fibre:F.Stack→List Bool) (catalogue:V.Stack→List Bool) (words:Fin 5→List Bool)
    (hist out:List Bool) (validBytes:List Bool:=[]) :Stack→List Bool:=
  Sum.elim fibre (Sum.elim catalogue (Sum.elim (D.cleanData (raw [] words) [] hist out) (fun _=>validBytes)))
/-- Actual retained source projection, with no normalization of its acquired metadata. -/
theorem data_source (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag:List Bool) (k:F.Stack) :data f v w hist out flag (sourceStack k)=f k:=rfl
/-- Actual original descriptor catalogue projection. -/
theorem data_catalogue (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag:List Bool) (k:V.Stack) :data f v w hist out flag (catalogueStack k)=v k:=rfl
/-- The record source reads actual N and scope DIRECTLY from the physical source. -/
theorem data_descriptor (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag:List Bool) (k:D.Stack) :
    data f v w hist out flag (descriptorStack k)=D.cleanData (raw (f F.originalInput) w) (f F.output) hist out k:=by
  cases k with
  | inl k=>
    cases k with
    | source i=>fin_cases i <;> rfl
    | bank | history | output | tagReader | copyScratch=>rfl
  | inr k=>rfl
/-- The actual tag and coordinate cache holds exactly the physically parsed field. -/
theorem data_cache (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag:List Bool) (i:Fin 5) :data f v w hist out flag (cache i)=w i:=by
  rw [cache_private]
  fin_cases i <;> rfl
/-- The actual parser validity word is separate from every source and work role. -/
theorem data_valid (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag:List Bool) :data f v w hist out flag valid=flag:=rfl
/-- Both reusable parser/N-copy work words are physically empty at interfaces. -/
theorem data_scratch (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag:List Bool) :data f v w hist out flag scratch=[]:=rfl
/-- Actual reverse logger operands; both unused consuming fields are genuinely empty. -/
theorem data_logger (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag:List Bool) (k:Log.Stack) :
    data f v w hist out flag (loggerStack k)=SemiprimeD1StackVertexRecordStream.data [] [] hist out k:=by
  cases k <;> rfl
/-- Physical source writes preserve catalogue, fields, accumulators and validity bytes. -/
theorem update_source (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag value:List Bool) (k:F.Stack) :
    Function.update (data f v w hist out flag) (sourceStack k) value=
      data (Function.update f k value) v w hist out flag:=by
  unfold data sourceStack
  rw [Sum.update_elim_inl]
/-- Actual descriptor consumption changes exactly the catalogue reader suffix. -/
theorem update_catalogue (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag value:List Bool) (k:V.Stack) :
    Function.update (data f v w hist out flag) (catalogueStack k) value=
      data f (Function.update v k value) w hist out flag:=by
  unfold data catalogueStack
  rw [Sum.update_elim_inr,Sum.update_elim_inl]
/-- Actual one-field write/erasure preserves N, binary scope and every other original field. -/
theorem raw_update (w:Fin 5→List Bool) (hist out value:List Bool) (i:Fin 5) :
    Function.update (D.cleanData (raw [] w) [] hist out) (D.source (fieldPart i)) value=
      D.cleanData (raw [] (Function.update w i value)) [] hist out:=by
  funext k
  cases k with
  | inl k=>
    cases k with
    | source j=>fin_cases i <;> fin_cases j <;> rfl
    | bank | history | output | tagReader | copyScratch=>rfl
  | inr k=>rfl
/-- Real parser writes and drains act only on their one actual field cache. -/
theorem update_cache (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag value:List Bool) (i:Fin 5) :
    Function.update (data f v w hist out flag) (cache i) value=
      data f v (Function.update w i value) hist out flag:=by
  rw [cache_private]
  unfold data
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inl,raw_update]
/-- Actual validity push/pop changes only its single allocated Unit role. -/
theorem update_valid (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag value:List Bool) :
    Function.update (data f v w hist out flag) valid value=data f v w hist out value:=by
  unfold data valid
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inr]
  congr 1
/-- Actual history write in the clean descriptor block, before including other source inventories. -/
theorem raw_history (w:Fin 5→List Bool) (hist out value:List Bool) :
    Function.update (D.cleanData (raw [] w) [] hist out) D.history value=
      D.cleanData (raw [] w) [] value out:=by
  funext k;cases k with
  | inl k=>cases k <;> rfl
  | inr k=>rfl
/-- Actual final-output write in the clean descriptor block. -/
theorem raw_output (w:Fin 5→List Bool) (hist out value:List Bool) :
    Function.update (D.cleanData (raw [] w) [] hist out) D.output value=
      D.cleanData (raw [] w) [] hist value:=by
  funext k;cases k with
  | inl k=>cases k <;> rfl
  | inr k=>rfl
/-- Physical history writes change no acquired source, raw descriptor or caller output byte. -/
theorem update_history (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag value:List Bool) :
    Function.update (data f v w hist out flag) history value=data f v w value out flag:=by
  change Function.update (data f v w hist out flag) (.inr (.inr (.inl D.history))) value=_
  unfold data
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inl,raw_history]
/-- Actual sentinel/final reversal writes only the shared output accumulator. -/
theorem update_output (f:F.Stack→List Bool) (v:V.Stack→List Bool) (w:Fin 5→List Bool)
    (hist out flag value:List Bool) :
    Function.update (data f v w hist out flag) output value=data f v w hist value flag:=by
  change Function.update (data f v w hist out flag) (.inr (.inr (.inl D.output))) value=_
  unfold data
  rw [Sum.update_elim_inr,Sum.update_elim_inr,Sum.update_elim_inl,raw_output]
/-- No descriptor, scope, validity or output sentinel is supplied at original initialization. -/
theorem empty_outer (f:F.Stack→List Bool) :data f (fun _=>[]) (fun _=>[]) [] []=Sum.elim f (fun _=>[]):=by
  funext k;rcases k with k|k|k|k
  · rfl
  · rfl
  · cases k with
    | inl k=>cases k with
      | source i=>fin_cases i <;> rfl
      | bank | history | output | tagReader | copyScratch=>rfl
    | inr k=>rfl
  · rfl
/-- Standard binary-only initialization is the exact empty-work physical store. -/
theorem input_data (bits:List Bool) :input bits=data (F.initial bits []).data (fun _=>[]) (fun _=>[]) [] []:=by
  rw [empty_outer];rfl
end RiemannGaussian.SemiprimeD1StackFullFactorCatalogueView
