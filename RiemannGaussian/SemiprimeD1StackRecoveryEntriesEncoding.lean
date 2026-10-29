/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryEntries
import RiemannGaussian.SemiprimeD1StackRecoveryDenominatorEncoding
import RiemannGaussian.SemiprimeD1TensorTapeCodec
/-! # Actual two-tape row/child ABI and four-field entry output
All functions describe physical bytes in proofs. The finite program accepts
only those two tapes and contains no row/child getter, array or Entry object.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackRecoveryEntriesEncoding
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeSourceHistogramKeyBits (frame)
open SemiprimeBitArithmetic (bitValue)
namespace R
export SemiprimeD1StackRecoveryDenominatorEncoding (Row fields tape)
end R
/-- Proof-only four actual output payload fields: sign,magnitude,denominator,child. -/
abbrev Entry:=Fin 4 → List Bool
/-- Physical nested child tape, with all padding of every actual coefficient retained. -/
def childTape (children:List (List (List Bool))):List Bool:=vectorBits (children.map vectorBits)
/-- Exact mathematical defaulting physical coefficient interpretation. -/
def selectedChild (children:List (List (List Bool))) (node index:List Bool):List Bool:=
  (((children[bitValue node]?).getD [])[bitValue index]?).getD []
/-- Proof-side actual entry payload; neither this function nor the children list is in runtime control. -/
def entry (children:List (List (List Bool))) (r:R.Row):Entry:=![r 2,r 3,r 4,selectedChild children (r 0) (r 1)]
/-- Exact actual four framed output fields. -/
def fields (e:Entry) (tail:List Bool):List Bool:=frame (e 0) (frame (e 1) (frame (e 2) (frame (e 3) tail)))
/-- Literal entry stream preserves original row order and all duplicate/zero/missing-cache entries. -/
def records:List Entry → List Bool
  | []=>[false]
  | e::es=>true::fields e (records es)
/-- Exact actual output byte tape specification. -/
def outputTape (rows:List R.Row) (children:List (List (List Bool))):List Bool:=records (rows.map (entry children))
end RiemannGaussian.SemiprimeD1StackRecoveryEntriesEncoding
