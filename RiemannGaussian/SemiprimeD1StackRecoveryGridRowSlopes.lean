/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryGridSite
import RiemannGaussian.SemiprimeD1StackRecoveryGridRepeats
/-! # Actual slope acquisition, chronological occurrence framing and oriented row folds -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryGridRowSlopes
open SemiprimeD1StackRecoveryGrid SemiprimeD1StackRecoveryGridView SemiprimeD1StackRecoveryGridCalls
open SemiprimeD1StackRecoveryGridOperationInput
open SemiprimeD1StackProcedureTrace
namespace Call
export SemiprimeD1StackRecoveryGridSite (result runBound site_call nonempty_preserved written_nonempty signed_getReg)
end Call
namespace Repeat
export SemiprimeD1StackRecoveryGridRepeats (buffers repeats_run rows)
end Repeat
/-- Actual reciprocal of the fitted node-minus-q word. -/
def reciprocal (w:Words) (width:List Bool) :Words:=Call.result .reciprocal w width
/-- Actual original slope alpha/(node-q), normalized and twice physically fitted. -/
def slope (w:Words) (width:List Bool) :Words:=Call.result .slope (reciprocal w width) width
/-- Own clock of the two actual slope operations. -/
def slopeBound (w:Words) (width:List Bool) :Nat:=
  Call.runBound .reciprocal w width+Call.runBound .slope (reciprocal w width) width
attribute [local irreducible] slopeBound Call.runBound
/-- Whole actual slope acquisition uses only actual retained bases and alpha. -/
theorem slope_run (w:Words) (width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hd:w.registers (.denBase,false)≠[]) (ha:w.registers (.alpha,false)≠[]) :
    ∃q≤ slopeBound w width,Runs program q (.local .reciprocal) (bank w) (.local .repeat) (bank (slope w width)):=by
  obtain ⟨p,hp,h0⟩:=Call.site_call .reciprocal (.local .reciprocal) (.local .slope) w width rfl hr hs hd hd
  have ha1:=Call.nonempty_preserved .reciprocal w width .alpha ha
  have hr1:=Call.written_nonempty .reciprocal w width
  obtain ⟨q,hq,h1⟩:=Call.site_call .slope (.local .slope) (.local .repeat) (reciprocal w width) width rfl hr hs ha1 hr1
  change Runs program p _ _ _ (bank (reciprocal w width)) at h0
  change Runs program q _ _ _ (bank (slope w width)) at h1
  refine ⟨p+q,?_,PTrace.join h0 h1⟩
  unfold slopeBound
  omega
/-- Exact newly framed chronological repeated slopes, preserving the existing physical tail without recopying it. -/
def repeated (w:Words) (word:SemiprimeRationalBits.RationalWord) (m:Nat) :Words:=
  {w with auxiliary:=Function.update w.auxiliary .slopes (Repeat.rows word m (w.auxiliary .slopes))}
/-- Whole repetition clock pays the actual m-marker copy and every two-Frame occurrence. -/
def repeatBound (word:SemiprimeRationalBits.RationalWord) (m:Nat) :Nat:=
  (5*m+4)+(m*(6*((signed word).length+word.denominator.length)+12)+1)
/-- The actual m-copy and physical framing loop acquire every slope occurrence exactly once. -/
theorem repeat_run (w:Words) (word:SemiprimeRationalBits.RationalWord) (m:Nat)
    (hm:w.product .product=List.replicate m true) (hz:w.auxiliary .repeatTodo=[])
    (hs:w.auxiliary .copyScratch=[]) (hf:w.auxiliary .frameScratch=[])
    (hn:w.registers (.slope,false)=signed word) (hd:w.registers (.slope,true)=word.denominator) :
    Runs program (repeatBound word m) (.local .repeat) (bank w) (.local .numeratorFold) (bank (repeated w word m)):=by
  have h0:=PTrace.copy_call .repeat (.local .repeat) (.local .repeats) rfl (bank w) (List.replicate m true) [] hm hz hs
  change Runs program _ _ _ _ (Function.update (bank w) (aux .repeatTodo) (List.replicate m true++[])) at h0
  rw [List.append_nil,update_auxiliary] at h0
  have he:Repeat.buffers w (List.replicate m true) (w.auxiliary .slopes)=
      {w with auxiliary:=Function.update w.auxiliary .repeatTodo (List.replicate m true)}:=by
    dsimp only [Repeat.buffers,SemiprimeD1StackRecoveryGridRepeats.buffers]
    congr 1
    funext k
    cases k <;> rfl
  rw [←he] at h0
  have h1:=Repeat.repeats_run w word m (w.auxiliary .slopes) hn hd hf
  have hf:Repeat.buffers w [] (Repeat.rows word m (w.auxiliary .slopes))=repeated w word m:=by
    dsimp only [Repeat.buffers,SemiprimeD1StackRecoveryGridRepeats.buffers,repeated]
    congr 1
    funext k
    cases k <;> first | rfl | exact hz.symm
  rw [hf] at h1
  simpa only [repeatBound,List.length_replicate] using PTrace.join h0 h1
/-- Actual numerator fold uses power FIRST and previously acquired tail SECOND. -/
def numerator (w:Words) (width:List Bool) :Words:=Call.result .numeratorFold w width
/-- Actual denominator fold uses power FIRST and previously acquired tail SECOND. -/
def folded (w:Words) (width:List Bool) :Words:=Call.result .denominatorFold (numerator w width) width
/-- Own exact pair of actual row-fold clocks. -/
def foldBound (w:Words) (width:List Bool) :Nat:=
  Call.runBound .numeratorFold w width+Call.runBound .denominatorFold (numerator w width) width
attribute [local irreducible] foldBound
/-- Both true original right-fold multiplications run even when actual multiplicity is zero. -/
theorem fold_run (w:Words) (width:List Bool)
    (hr:w.rational=emptyRational width) (hs:w.auxiliary .copyScratch=[])
    (hn:w.registers (.numPower,false)≠[]) (hgn:w.registers (.gridNum,false)≠[])
    (hd:w.registers (.denPower,false)≠[]) (hgd:w.registers (.gridDen,false)≠[]) :
    ∃q≤ foldBound w width,Runs program q (.local .numeratorFold) (bank w)
      (.local (.clearTransient false 0)) (bank (folded w width)):=by
  obtain ⟨p,hp,h0⟩:=Call.site_call .numeratorFold (.local .numeratorFold) (.local .denominatorFold) w width rfl hr hs hn hgn
  have hd1:=Call.nonempty_preserved .numeratorFold w width .denPower hd
  have hgd1:=Call.nonempty_preserved .numeratorFold w width .gridDen hgd
  obtain ⟨q,hq,h1⟩:=Call.site_call .denominatorFold (.local .denominatorFold) (.local (.clearTransient false 0))
    (numerator w width) width rfl hr hs hd1 hgd1
  change Runs program p _ _ _ (bank (numerator w width)) at h0
  change Runs program q _ _ _ (bank (folded w width)) at h1
  refine ⟨p+q,?_,PTrace.join h0 h1⟩
  unfold foldBound
  omega
end RiemannGaussian.SemiprimeD1StackRecoveryGridRowSlopes
