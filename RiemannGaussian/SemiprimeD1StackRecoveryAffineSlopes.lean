/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeReverse
import RiemannGaussian.SemiprimeD1StackRecoveryAffineSeed
/-! # Paid acquired-slope copy, one row reversal, and literal empty-product seed -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopes
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryAffineSlopeBuffers SemiprimeD1StackProcedureTrace
namespace T
export SemiprimeD1StackRecoveryAffinePrimitives (join copy_call push_run)
end T
/-- Actual additional words after row reversal and ten literal ONE-seed pushes. -/
def result (w:Words) (xs:List SemiprimeRationalBits.RationalWord):Words:=
  {buffers w [] (vector xs.reverse) with added:=Function.update (buffers w [] (vector xs.reverse)).added .array oneArray}
/-- The source pays its single preserving copy, literal terminator, all row parsing/framing and seed pushes. -/
def runBound (xs:List SemiprimeRationalBits.RationalWord):Nat:=
  (5*(vector xs).length+4)+1+SemiprimeD1StackRecoveryAffineSlopeReverse.runBound xs+10
/-- No acquired slope list is supplied to code; this states the exact run from its already actual tape. -/
theorem source_run (w:Words) (xs:List SemiprimeRationalBits.RationalWord)
    (ht:w.auxiliary .slopes=vector xs) (hc:w.auxiliary .copyScratch=[])
    (hr:w.added .reader=[]) (hv:w.added .reverseSlopes=[]) (ha:w.added .array=[])
    (hn:w.registers (.slope,false)=[]) (hd:w.registers (.slope,true)=[])
    (hf:w.auxiliary .frameScratch=[]) (hs:w.auxiliary .scan=[]) :
    Runs program (runBound xs) (.local .copySlopes) (bank w)
      (.local .slopeLoop) (bank (result w xs)):=by
  have hself:buffers w [] []=w:=by simpa only [hr,hv] using buffers_self w
  have h0:=T.copy_call .slopes (.local .copySlopes) (.local .seedReverse) rfl
    (bank (buffers w [] [])) (vector xs) [] ht rfl hc
  change Runs program _ _ _ _ (Function.update (bank (buffers w [] [])) (aux .reader) (vector xs++[])) at h0
  rw [List.append_nil,update_reader] at h0
  have h1:=T.push_run (.local .seedReverse) (.local .reverseLoop) (aux .reverseSlopes) false
    (bank (buffers w (vector xs) [])) rfl
  change Runs program _ _ _ _ (Function.update (bank (buffers w (vector xs) [])) (aux .reverseSlopes) [false]) at h1
  rw [update_reversed] at h1
  have h2:=SemiprimeD1StackRecoveryAffineSlopeReverse.reverse_vector_run w xs hn hd hf hs
  have h3:=SemiprimeD1StackRecoveryAffineSeed.seed_run (buffers w [] (vector xs.reverse)) ha
  have h:=T.join (T.join (T.join h0 h1) h2) h3
  rw [hself] at h
  exact h
/-- Original104 cells are all retained exactly, independently of array size, q0 and W0. -/
theorem grid_retained (w:Words) (xs:List SemiprimeRationalBits.RationalWord) (slot:Q.Stack):
    bank (result w xs) (grid slot)=bank w (grid slot):=rfl
/-- Retained actual q survives slope acquisition and literal seeding. -/
theorem count_retained (w:Words) (xs:List SemiprimeRationalBits.RationalWord):
    (result w xs).added .retainedQ=w.added .retainedQ:=rfl
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopes
