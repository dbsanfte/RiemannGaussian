/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackChildTableEntryScalar
/-! # Individual scalar cost charges actual precision VALUE expansion -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildTableEntryScalarCost
open SemiprimeD1StackChildTableEntryEncoding SemiprimeD1StackChildTableEntryScalar
open SemiprimeBitArithmetic (bitValue)
/-- The actual reduced scalar has at most the actual NEWp value many bits. -/
theorem result_length (word p:List Bool):(SR.result word p).length≤bitValue p:=SemiprimeD1JetScalarBits.reduce_length _ _
/-- Full per-coefficient operand framing, real precision source, logging, real return and cleanup is linear in all paid scalar operands and precision VALUE. -/
theorem scalarTime_le (word p:List Bool):scalarTime word p≤100*(word.length+p.length+bitValue p+1):=by
  have hs:=SR.totalTime_le word p
  have hr:=result_length word p
  unfold scalarTime
  simp only [row,List.length_cons,SemiprimeSourceHistogramKeyBits.frame_length,List.length_nil]
  omega
end RiemannGaussian.SemiprimeD1StackChildTableEntryScalarCost
