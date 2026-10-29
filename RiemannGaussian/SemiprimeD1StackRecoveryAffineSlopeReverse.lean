/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeFrame
/-! # One real traversal reverses rows while retaining every original Grid word -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeReverse
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineSlopeBuffers SemiprimeD1StackProcedureTrace
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join pop_run peek_run)
end T
/-- Paid source clock of one actual signed/denominator row, including all caller/EOF steps. -/
def rowTime (x:SemiprimeRationalBits.RationalWord):Nat:=15*((signed x).length+x.denominator.length)+30
/-- Exact physical row consumption, retained-operand frames, and both cache drains. -/
theorem row_run (w:Words) (x:SemiprimeRationalBits.RationalWord) (tail reversed:List Bool)
    (hn:w.registers (.slope,false)=[]) (hd:w.registers (.slope,true)=[])
    (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]) :
    Runs program (rowTime x) (.local .reverseLoop)
      (bank (buffers w (SemiprimeD1StackRecoveryGridView.slopeRow x tail) reversed))
      (.local .reverseLoop)
      (bank (buffers w tail (SemiprimeD1StackRecoveryGridView.slopeRow x reversed))):=by
  have h0:=SemiprimeD1StackRecoveryAffineSlopeParse.tagged_run w x tail reversed hn hd hs hv
  have h1:=SemiprimeD1StackRecoveryAffineSlopeFrame.frame_run w x tail reversed hs
  have h2:=SemiprimeD1StackRecoveryAffineSlopeFrame.clear_run w x tail
    (SemiprimeD1StackRecoveryGridView.slopeRow x reversed) hn hd
  have h:=T.join (T.join h0 h1) h2
  convert h using 1
  unfold rowTime
  omega
/-- Reversing rows is a proof invariant, never a runtime list argument. -/
def reverseRows:List SemiprimeRationalBits.RationalWord→List Bool→List Bool
  | [],tail=>tail
  | x::xs,tail=>reverseRows xs (SemiprimeD1StackRecoveryGridView.slopeRow x tail)
/-- Sum of actual row clocks and the two final physical terminator/EOF inspections. -/
def runBound:List SemiprimeRationalBits.RationalWord→Nat
  | []=>2
  | x::xs=>rowTime x+runBound xs
/-- Every original row is parsed once and prepended once; no accumulated tail is copied. -/
theorem reverse_run (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (reversed:List Bool)
    (hn:w.registers (.slope,false)=[]) (hd:w.registers (.slope,true)=[])
    (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]) :
    Runs program (runBound xs) (.local .reverseLoop) (bank (buffers w (vector xs) reversed))
      (.local (.seedArray 0)) (bank (buffers w [] (reverseRows xs reversed))):=by
  induction xs generalizing reversed with
  | nil=>
    have h0:=T.pop_run (.local .reverseLoop) (.local .abort) (.local .reverseEOF)
      (.local (.field (.slope false false))) (aux .reader) (bank (buffers w (vector []) reversed)) [false] rfl rfl
    change Runs program 1 _ _ (.local .reverseEOF)
      (Function.update (bank (buffers w (vector []) reversed)) (aux .reader) []) at h0
    rw [update_reader] at h0
    have h1:=T.peek_run (.local .reverseEOF) (.local (.seedArray 0)) (.local .abort) (.local .abort)
      (aux .reader) (bank (buffers w [] reversed)) [] rfl rfl
    exact T.join h0 h1
  | cons x xs ih=>
    exact T.join (row_run w x (vector xs) reversed hn hd hs hv)
      (ih (SemiprimeD1StackRecoveryGridView.slopeRow x reversed))
/-- The streaming physical prepend order is exactly the reversed original row order. -/
theorem reverseRows_vector (xs ys:List SemiprimeRationalBits.RationalWord):
    reverseRows xs (vector ys)=vector (xs.reverse++ys):=by
  induction xs generalizing ys with
  | nil=>rfl
  | cons x xs ih=>
    change reverseRows xs (vector (x::ys))=_
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
/-- The complete output row tape keeps all raw sign/padding bytes in reversed row order. -/
theorem reverse_vector_run (w:Words) (xs:List SemiprimeRationalBits.RationalWord)
    (hn:w.registers (.slope,false)=[]) (hd:w.registers (.slope,true)=[])
    (hs:w.auxiliary .frameScratch=[]) (hv:w.auxiliary .scan=[]) :
    Runs program (runBound xs) (.local .reverseLoop) (bank (buffers w (vector xs) [false]))
      (.local (.seedArray 0)) (bank (buffers w [] (vector xs.reverse))):=by
  have h:=reverse_run w xs (vector []) hn hd hs hv
  rw [reverseRows_vector,List.append_nil] at h
  exact h
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeReverse
