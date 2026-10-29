/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyRead
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyMaximum
import RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyStore
/-! # Complete same-program raw-key-only frequency acquisition with its own clock -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyExecution
open SemiprimeD1StackSourceKeyFrequency SemiprimeD1StackSourceKeyFrequencyEncoding
open SemiprimeD1StackSourceKeyFrequencyPrimitives SemiprimeD1StackSourceKeyFrequencyRead
open SemiprimeD1StackSourceKeyFrequencyMaximum SemiprimeD1StackSourceKeyFrequencyStore
open SemiprimeD1StackProcedureTrace
open SemiprimeD1TensorTapeCodec (vectorBits)
/-- Own row clock includes actual byte parsing, dictionary scan, binary increment, comparison and override insertion. -/
def rowTime (s:Summary) (raw:List Bool) :Nat :=8*raw.length+9+lookupClock s.rows raw+
  (40*((read s.rows raw).length+1)+2)+maximumClock s.maximum (nextCount s.rows raw)+storeClock raw (nextCount s.rows raw)
/-- One actual forward input row updates its exact acquired count and maximum. -/
theorem row_run (src raw tail:List Bool) (s:Summary) :
    ∃q≤rowTime s raw,Runs program q .header
      (bank (loopWords src (true::SemiprimeSourceHistogramKeyBits.frame raw tail) s)) .header
      (bank (loopWords src tail (step s raw))) :=by
  have h0:=parse_run src raw tail s
  obtain ⟨q,hq,h1⟩:=read_run src tail raw s
  obtain ⟨u,hu,h2⟩:=successor_run src tail raw s
  have h3:=maximum_run src tail raw (nextCount s.rows raw) s
  have h4:=store_run src tail raw (nextCount s.rows raw) (nextMaximum s.maximum (nextCount s.rows raw)) s.rows
  refine ⟨_,?_,join (join (join (join h0 h1) h2) h3) h4⟩
  unfold rowTime
  omega
/-- Source clock follows the SAME physical chronological fold, with no supplied count/answer or previous report clock. -/
def scanTime :List (List Bool)→Summary→Nat
  | [],_=>1
  | raw::keys,s=>rowTime s raw+scanTime keys (step s raw)
/-- All duplicates are actually visited; only the source's terminating false is consumed at the end. -/
theorem scan_run (src:List Bool) (keys:List (List Bool)) (s:Summary) :
    ∃q≤ scanTime keys s,Runs program q .header (bank (loopWords src (vectorBits keys) s)) .eof
      (bank (loopWords src [] (keys.foldl step s))) :=by
  induction keys generalizing s with
  | nil=>
    have h:=pop_run .header .abort .eof .parse (aux .reader) (bank (loopWords src [false] s)) [false] rfl rfl
    rw [update_reader] at h
    exact ⟨1,le_rfl,h⟩
  | cons raw keys ih=>
    obtain ⟨q,hq,h0⟩:=row_run src raw (vectorBits keys) s
    obtain ⟨u,hu,h1⟩:=ih (step s raw)
    exact ⟨q+u,Nat.add_le_add hq hu,join h0 h1⟩
/-- Every actual whole-entry step, including source copy, terminal checks and final halt. -/
def runBound (keys:List (List Bool)) :Nat :=1+(5*(vectorBits keys).length+4)+scanTime keys empty+1+1
/-- Actual key-vector-only front door establishes its own physical dictionary and maximum. -/
theorem source_trace (keys:List (List Bool)) :
    ∃q≤runBound keys-1,Runs program q .start (source keys).data .done (result keys) :=by
  let w0:Words:={source:=vectorBits keys}
  let w1:Words:={w0 with dictionary:=[false]}
  let w2:Words:={w1 with reader:=vectorBits keys}
  have hi:(source keys).data=bank w0:=by
    funext k;rcases k with k|k
    · rcases k with k|k <;> cases k <;> rfl
    · cases k <;> simp [source,initial,input,aux,bank,w0,Function.update]
  have h0:=push_run .start .copyStream (aux .dictionary) false (bank w0) rfl
  rw [update_dictionary] at h0
  have h1:=copy_call .stream .copyStream .header rfl (bank w1) (vectorBits keys) [] rfl rfl rfl
  change Runs program (5*(vectorBits keys).length+4) .copyStream (bank w1) .header (Function.update (bank w1) (aux .reader) (vectorBits keys++[])) at h1
  rw [List.append_nil,update_reader] at h1
  obtain ⟨q,hq,h2⟩:=scan_run (vectorBits keys) keys empty
  have h3:=peek_run .eof .done .abort .abort (aux .reader) (result keys) [] rfl rfl
  rw [hi]
  refine ⟨_,?_,join (join (join h0 h1) h2) h3⟩
  unfold runBound
  omega
/-- Whole literal halt is included; no native frequency/max evaluation supplies a machine operand. -/
theorem source_run (keys:List (List Bool)) :
    ∃q≤runBound keys,SemiprimeD1StackCalls.run program q (source keys)=some (done keys) :=by
  obtain ⟨q,hq,hr⟩:=source_trace keys
  obtain ⟨finish,hf,hAt⟩:=hr [] (source keys) ⟨rfl,rfl,rfl⟩
  have hp:0<runBound keys:=by unfold runBound;omega
  refine ⟨q+1,by omega,?_⟩
  rw [SemiprimeD1StackReturnLink.run_add,hf,Option.bind_some]
  exact halt_run program .done rfl (result keys) [] finish hAt
/-- Genuine compiled21-role whole acquisition uses the same own actual transition clock. -/
noncomputable def frequencyInTime (keys:List (List Bool)) :
    StateTransition.EvalsToInTime machine.step (SemiprimeD1StackCalls.configuration (source keys))
      (some (SemiprimeD1StackCalls.configuration (done keys))) (runBound keys) :=by
  apply SemiprimeD1StackCalls.evalsCorrect (aux .source) (aux .maximum) .start program
  let h:=source_run keys
  exact ⟨⟨Classical.choose h,(Classical.choose_spec h).2⟩,(Classical.choose_spec h).1⟩
end RiemannGaussian.SemiprimeD1StackSourceKeyFrequencyExecution
