/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineView
/-! # Exact original affine-array source boundary, without runtime coefficient advice
Every old native object below occurs only in output byte/value specifications.
The actual fixed program reads only the five original physical input words.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineEncoding
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
namespace E
export SemiprimeD1StackRecoveryGridEncoding (resultWords)
end E
/-- Original retained multiplicity, whose actual unary acquisition is proved from true geometry and height. -/
def retained (a M u:Nat) (t:Fin (2^(a+1))):Nat:=
  SemiprimeD1JetRecoveryGrid.nodeMultiplicity a (SemiprimeD1TaperedLoss.height M u) u t.val
/-- Exact old affine output coefficient words in original ascending coefficient order. -/
def array (a M u:Nat) (t:Fin (2^(a+1))) (width:List Bool):List SemiprimeRationalBits.RationalWord:=
  (SemiprimeAffineJetBits.build width (retained a M u t) (SemiprimeD1RecoveryGridBits.acquire width a M u t).grid.slopes).words.toList
/-- Actual ready bank after the SAME sealed whole Grid104; every additional role is EMPTY. -/
def original (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):Words:=
  {toWords:=E.resultWords a M u selected t width}
/-- Whole actual affine endpoint retains the entire original Grid104 bank literally. -/
def resultWords (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):Words:=
  {original a M u selected t width with added:=fun slot=>match slot with | .retainedQ=>List.replicate (retained a M u selected) true | .array=>vector (array a M u selected width) | _=>[]}
/-- Exact complete112-word physical stop specification, with all work/shadows counted and clear. -/
def result (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):Stack→List Bool:=
  bank (resultWords a M u selected t width)
/-- Real whole halt has both flags and its actual internal saved-return tape EMPTY. -/
def done (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):C.State Stack Label:=
  ⟨none,none,none,result a M u selected t width,[]⟩
/-- Not one old retained Grid word is normalized, recomputed, replaced or silently dropped at return. -/
theorem grid_retained (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool) (slot:Q.Stack):
    result a M u selected t width (grid slot)=SemiprimeD1StackRecoveryGridEncoding.result a M u selected t width slot:=rfl
/-- Retained q is an actual unary output, not an additional input answer. -/
theorem retained_output (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    result a M u selected t width (aux .retainedQ)=List.replicate (retained a M u selected) true:=rfl
/-- Actual array-vector bytes are exactly the authoritative native build bytes, including singleton empty product and q0 truncation. -/
theorem array_output (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool):
    result a M u selected t width (aux .array)=vector (array a M u selected width):=rfl
/-- Every one of the six additional parser/counter/move words is EMPTY at whole halt. -/
theorem work_clear (a M u:Nat) (selected:Fin (2^(a+1))) (t width:List Bool) (slot:Aux)
    (hq:slot≠.retainedQ) (ha:slot≠.array):result a M u selected t width (aux slot)=[]:=by
  cases slot <;> first | rfl | exact (hq rfl).elim | exact (ha rfl).elim
end RiemannGaussian.SemiprimeD1StackRecoveryAffineEncoding
