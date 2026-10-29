/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceAlphabet64Rows
/-! # Whole physical chronological candidate stream with one final catalogue log -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceAlphabet64Loop
open SemiprimeD1StackSourceAlphabet64 SemiprimeD1StackSourceAlphabet64Encoding
open SemiprimeD1StackSourceAlphabet64Rows SemiprimeD1StackSourceAlphabet64Primitives
open SemiprimeD1StackSourceAlphabet64Calls SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
/-- Physical actual loop boundary has no row-local work, only its reader and reverse catalogue history. -/
def boundary (base:Stack→List Bool) (reader hist:List Bool) :Stack→List Bool :=
  view base reader [] [] [] [] [] [] [] [] [] [] hist
/-- Actual dictionary-entry bytes without the final false catalogue sentinel. -/
def stream (a:Nat) (ws:List (List Bool)) :List Bool :=ws.foldr (fun word tail=>chunk a word++tail) []
/-- Stream construction is literally the old generic pair-record grammar, not merely equivalent decoded keys. -/
theorem stream_records (a:Nat) (ws:List (List Bool)) :
    stream a ws++[false]=SemiprimeD1StackOwnerLookup.records (ws.map (fun word=>(compact word,row a word))) [] :=by
  induction ws with
  | nil=>rfl
  | cons word ws ih=>
    change ((true::frame (compact word) (frame (row a word) []))++stream a ws)++[false]=_
    rw [List.append_assoc,ih,List.cons_append,SemiprimeD1TensorTapeCodec.frame_append,
      SemiprimeD1TensorTapeCodec.frame_append,List.nil_append]
    rfl
/-- Real parser validity bit is physically consumed, restoring the actual caller flag word. -/
theorem valid_run (base:Stack→List Bool) (reader word hist:List Bool) (hv:base (aux .valid)=[]) :
    let bank:=view base reader word [] [] [] [] [] [] [] [] [] hist
    Runs program 1 .valid (Function.update bank (aux .valid) [true]) .saveWord bank :=by
  dsimp only
  apply one_base program _ _ (.pop (aux .valid) .abort .abort .saveWord) _ _ rfl
  · rfl
  · change Function.update (Function.update (view base reader word [] [] [] [] [] [] [] [] [] hist)
      (aux .valid) [true]) (aux .valid) []=_
    rw [Function.update_idem]
    have he:view base reader word [] [] [] [] [] [] [] [] [] hist (aux .valid)=[]:=hv
    rw [←he]
    exact Function.update_eq_self _ _
/-- One full physically parsed vector row calls the real compact-ID/colour-framing path. -/
theorem row_run (base:Stack→List Bool) (a:Nat) (word tail hist:List Bool) (hlen:word.length=6*a)
    (hc:base (aux .copyScratch)=[]) (hl:base (aux .trimLeft)=[]) (hr:base (aux .trimRight)=[])
    (hs:base (aux .frameScratch)=[]) (hf:base (aux .fieldScratch)=[]) (hv:base (aux .valid)=[]) :
    ∃q ≤ 2000*(a+1),Runs program q .header (boundary base (true::frame word tail) hist) .header
      (boundary base tail ((chunk a word).reverse++hist)) :=by
  have h0:Runs program 1 .header (boundary base (true::frame word tail) hist) .parse
      (boundary base (frame word tail) hist):=by
    apply one_base program _ _ (.pop (aux .reader) .abort .finishSeed .parse) _ _ rfl
    · rfl
    · exact update_reader _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have h1:=parse_call (boundary base (frame word tail) hist) word tail rfl rfl hf hv
  dsimp only [boundary] at h1
  rw [update_reader,update_raw] at h1
  have h2:=valid_run base tail word hist hv
  dsimp only at h2
  obtain ⟨r,hrBound,h3⟩:=word_run base a word tail hist hlen hc hl hr hs
  have hall:=compose (compose (compose h0 h1) h2) h3
  refine ⟨_,?_,hall⟩
  rw [hlen]
  omega
/-- Whole literal vector traversal visits each actual assignment once in its original forward order. -/
theorem rows_run (base:Stack→List Bool) (a:Nat) (ws:List (List Bool)) (hist:List Bool)
    (hw:∀w∈ws,w.length=6*a)
    (hc:base (aux .copyScratch)=[]) (hl:base (aux .trimLeft)=[]) (hr:base (aux .trimRight)=[])
    (hs:base (aux .frameScratch)=[]) (hf:base (aux .fieldScratch)=[]) (hv:base (aux .valid)=[]) :
    ∃q ≤ 2000*(a+1)*ws.length+1,
      Runs program q .header (boundary base (SemiprimeD1TensorTapeCodec.vectorBits ws) hist) .finishSeed
        (boundary base [] ((stream a ws).reverse++hist)) :=by
  induction ws generalizing hist with
  | nil=>
    refine ⟨1,by omega,?_⟩
    change Runs program 1 .header (boundary base [false] hist) .finishSeed (boundary base [] hist)
    apply one_base program _ _ (.pop (aux .reader) .abort .finishSeed .parse) _ _ rfl
    · rfl
    · exact update_reader _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | cons word ws ih=>
    obtain ⟨r,hrBound,h0⟩:=row_run base a word (SemiprimeD1TensorTapeCodec.vectorBits ws) hist
      (hw word List.mem_cons_self) hc hl hr hs hf hv
    obtain ⟨s,hsBound,h1⟩:=ih ((chunk a word).reverse++hist) (fun w hm=>hw w (List.mem_cons_of_mem _ hm))
    have he:(stream a ws).reverse++((chunk a word).reverse++hist)=(stream a (word::ws)).reverse++hist:=by
      change _=(chunk a word++stream a ws).reverse++hist
      rw [List.reverse_append,List.append_assoc]
    rw [he] at h1
    exact ⟨r+s,by simp only [List.length_cons];nlinarith only [hrBound,hsBound],compose h0 h1⟩
end RiemannGaussian.SemiprimeD1StackSourceAlphabet64Loop
