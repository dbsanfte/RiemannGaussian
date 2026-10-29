/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackExprDotComponents

/-! # Actual word-read, literal framing and complete acquired dot term
The selected value comes only from the real preserving vector reader. Every
subtree, tag, scratch cleanup and return remains in the executed finite program.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackExprDotTerm
open SemiprimeD1StackExprDot SemiprimeD1StackExprDotComponents SemiprimeD1StackProcedureTrace
open SemiprimeD1StackExprDotSpec (wordAt)
open SemiprimeD1StackUnaryDivmod (unary)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => SemiprimeD1StackExprDot.Label.control

/-- The actual cached reader obtains the selected word, including zero default,
and preserves the full source vector. No selected word or getter is an operand. -/
theorem read_call (c : Cache) (words : List (List Bool)) (j : ℕ) (hc : c.words=vectorBits words)
    (out : List Bool) :
    Runs program (SemiprimeD1StackJetReadExecution.totalTime (unary j) words+1)
      (ctl .readCall) (bank c {remaining:=unary j,index:=unary j,output:=out})
      (ctl .frameCall) (bank c {remaining:=unary j,word:=wordAt words j,output:=out}) := by
  apply SemiprimeD1StackProcedureCallsTrace.included_call program readStack Label.read readStack_injective
    Read.program .start (fun _=>rfl) (ctl .readCall) (ctl .frameCall) rfl
    (SemiprimeD1StackJetReadExecution.totalTime (unary j) words)
    (Read.state (some .start) none none (vectorBits words) [] (unary j) [] [] [] [] [])
    (Read.state none none none (vectorBits words) [] [] [] [] (wordAt words j) [] [])
    (bank c {remaining:=unary j,index:=unary j,output:=out})
    (bank c {remaining:=unary j,word:=wordAt words j,output:=out})
  · rfl
  · rfl
  · rfl
  · rfl
  · simpa only [unary,List.length_replicate,wordAt] using
      SemiprimeD1StackJetReadExecution.source_run (unary j) words
  · constructor
    · intro k;cases k <;> simp [readStack,bank,Read.state,Read.store,hc]
    · intro k _;rfl
  · constructor
    · intro k;cases k <;> simp [readStack,bank,Read.state,Read.store,hc]
    · intro k hk
      cases k <;> first | rfl | exact False.elim (hk .index rfl) | exact False.elim (hk .output rfl)

/-- The acquired raw word is actually framed onto the power/term suffix. -/
theorem frame_call (c : Cache) (remaining word out : List Bool) :
    Runs program (6*word.length+5) (ctl .frameCall) (bank c {remaining:=remaining,word:=word,output:=out})
      (ctl .literal0) (bank c {remaining:=remaining,word:=word,output:=frame word out}) := by
  apply included_call program frameStack Label.frame frameStack_injective SemiprimeD1StackFrame.code 0
    (fun _=>rfl) (ctl .frameCall) (ctl .literal0) rfl (6*word.length+4)
    (SemiprimeD1StackFrame.state 0 none word out []) (SemiprimeD1StackFrame.done word (frame word out))
    (bank c {remaining:=remaining,word:=word,output:=out})
    (bank c {remaining:=remaining,word:=word,output:=frame word out})
  · rfl
  · rfl
  · exact SemiprimeD1StackFrame.frame_words word out none
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k <;> rfl
    · intro k hk
      cases k <;> first | rfl | exact False.elim (hk 1 rfl)

/-- One actual constructor-bit push changes only the physical output stack. -/
theorem push_run (c : Cache) (w : Work) (pc next : Control) (b : Bool)
    (hcode : program (ctl pc)=.base (.push .output b (ctl next))) :
    Runs program 1 (ctl pc) (bank c w) (ctl next) (bank c {w with output:=b::w.output}) := by
  apply one_base program (ctl pc) (ctl next) (.push .output b (ctl next)) _ _ hcode
  · rfl
  · funext k;cases k <;> rfl

/-- Actual 00 literal and 11 multiplication tags complete the term syntax. -/
theorem tags_run (c : Cache) (remaining word out : List Bool) :
    Runs program 4 (ctl .literal0) (bank c {remaining:=remaining,word:=word,output:=frame word out})
      (ctl .clearWord) (bank c {remaining:=remaining,word:=word,output:=true::true::false::false::frame word out}) := by
  have h0:=push_run c {remaining:=remaining,word:=word,output:=frame word out} .literal0 .literal1 false rfl
  have h1:=push_run c {remaining:=remaining,word:=word,output:=false::frame word out} .literal1 .mul0 false rfl
  have h2:=push_run c {remaining:=remaining,word:=word,output:=false::false::frame word out} .mul0 .mul1 true rfl
  have h3:=push_run c {remaining:=remaining,word:=word,output:=true::false::false::frame word out} .mul1 .clearWord true rfl
  exact runs_trans program _ _ _ _ _ _ _ _
    (runs_trans program _ _ _ _ _ _ _ _ (runs_trans program _ _ _ _ _ _ _ _ h0 h1) h2) h3

/-- The framer-preserved word is erased by real pops before the next term. -/
theorem clear_word (c : Cache) (remaining word out : List Bool) :
    Runs program (word.length+1) (ctl .clearWord) (bank c {remaining:=remaining,word:=word,output:=out})
      (ctl .loop) (bank c {remaining:=remaining,output:=out}) := by
  have h:=SemiprimeD1StackPhysicalLoops.drain program (ctl .clearWord) (ctl .loop)
    Stack.word rfl (bank c {remaining:=remaining,output:=out}) word
  have hi : Function.update (bank c {remaining:=remaining,output:=out}) Stack.word word=
      bank c {remaining:=remaining,word:=word,output:=out} := by
    funext k;cases k <;> simp [Function.update,bank]
  have ho : Function.update (bank c {remaining:=remaining,output:=out}) Stack.word []=
      bank c {remaining:=remaining,output:=out} := Function.update_eq_self _ _
  rw [hi,ho] at h
  exact h

/-- Actual local budget, retaining both physical product loops, every copied
base/word byte and ALL scratch draining; it is not an old/native report. -/
def budget (c : Cache) (words : List (List Bool)) (stride frequency j : ℕ) : ℕ :=
  (5*j+4)+(5*(j*(2*frequency+3)+1)+1)+(5*((j*frequency)*(2*stride+3)+1)+1)+
    (SemiprimeD1StackExprPowerExecution.totalTime c.base (unary (stride*(j*frequency)))+1)+
    (stride*(j*frequency)+1)+(5*j+4)+
    (SemiprimeD1StackJetReadExecution.totalTime (unary j) words+1)+
    (6*(wordAt words j).length+5)+4+((wordAt words j).length+1)

/-- COMPLETE one-term acquisition. The only cache hypotheses identify original
physical input metadata/vector tapes; no resolved word/exponent/clock is given. -/
theorem term_run (c : Cache) (words : List (List Bool)) (stride frequency j : ℕ)
    (hs : c.stride=unary stride) (hf : c.frequency=unary frequency) (hc : c.words=vectorBits words)
    (out : List Bool) :
    ∃t ≤ budget c words stride frequency j,Runs program t (ctl .copyProduct)
      (bank c {remaining:=unary j,output:=out}) (ctl .loop)
      (bank c {remaining:=unary j,output:=SemiprimeD1StackExprDotSpec.term c.base words stride frequency j out}) := by
  have h0:=copy_product c (unary j) out
  obtain ⟨t1,ht1,h1⟩:=product_first c j frequency hf out
  obtain ⟨t2,ht2,h2⟩:=product_second c j stride frequency hs out
  have h3:=power_call c j (stride*(j*frequency)) out
  have h4:=clear_exponent c (unary j) (unary (stride*(j*frequency)))
    (SemiprimeD1StackExprPowerSpec.result (stride*(j*frequency)) c.base out)
  have h5:=copy_index c (unary j) (SemiprimeD1StackExprPowerSpec.result (stride*(j*frequency)) c.base out)
  have h6:=read_call c words j hc (SemiprimeD1StackExprPowerSpec.result (stride*(j*frequency)) c.base out)
  have h7:=frame_call c (unary j) (wordAt words j)
    (SemiprimeD1StackExprPowerSpec.result (stride*(j*frequency)) c.base out)
  have h8:=tags_run c (unary j) (wordAt words j)
    (SemiprimeD1StackExprPowerSpec.result (stride*(j*frequency)) c.base out)
  have h9:=clear_word c (unary j) (wordAt words j) (SemiprimeD1StackExprDotSpec.term c.base words stride frequency j out)
  simp only [unary,List.length_replicate] at h0 h4 h5
  have h01:=runs_trans program _ _ _ _ _ _ _ _ h0 h1
  have h012:=runs_trans program _ _ _ _ _ _ _ _ h01 h2
  have h0123:=runs_trans program _ _ _ _ _ _ _ _ h012 h3
  have h01234:=runs_trans program _ _ _ _ _ _ _ _ h0123 h4
  have h012345:=runs_trans program _ _ _ _ _ _ _ _ h01234 h5
  have h0123456:=runs_trans program _ _ _ _ _ _ _ _ h012345 h6
  have h01234567:=runs_trans program _ _ _ _ _ _ _ _ h0123456 h7
  have h012345678:=runs_trans program _ _ _ _ _ _ _ _ h01234567 h8
  have h:=runs_trans program _ _ _ _ _ _ _ _ h012345678 h9
  refine ⟨_,?_,h⟩
  unfold budget
  omega

end RiemannGaussian.SemiprimeD1StackExprDotTerm
