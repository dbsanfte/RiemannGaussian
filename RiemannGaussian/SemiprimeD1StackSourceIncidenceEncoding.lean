/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackSourceIncidence
/-! # Exact physical input and output banks of the prepared incidence query
This structure is only a theorem-side interpretation of actual acquired bytes.
The fixed program, finite labels and flags have no such structure or list argument.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackSourceIncidenceEncoding
open SemiprimeD1StackSourceIncidence
/-- Proof-side names for the acquired prefix, occurrence stream and three retained binary count words. -/
structure Inputs where
  /-- The newest-first selected IDs whose dictionary has actually been acquired. -/
  ids:List (List Bool)
  /-- Arbitrary current selected word is retained by the query. -/
  chosen:List Bool
  /-- Arbitrary caller query is physically saved and restored. -/
  query:List Bool
  /-- Arbitrary retained selected-prefix input word. -/
  pfx:List Bool
  /-- Every actual original occurrence, including repeated descriptors. -/
  rows:List (List Bool×List Bool)
  /-- Actually acquired binary square count payload. -/
  square:List Bool
  /-- Actually acquired binary cube count payload. -/
  cube:List Bool
  /-- Actually acquired binary fourth count payload. -/
  fourth:List Bool
/-- Original complete acquired25-role bank, with no answer/found/scratch loaded. -/
def environment (i:Inputs) :SemiprimeD1StackSourceEnvironment.Stack→List Bool :=
  (SemiprimeD1StackSourceEnvironmentExecution.lookupReady i.ids i.chosen i.query i.pfx).data
/-- Literal acquired occurrence codec, one pair tag and two fields per occurrence, one final false. -/
def tape (i:Inputs) :List Bool :=SemiprimeD1StackOwnerLookup.records i.rows []
/-- Whole prepared query entry, supplied only the actual physical input words specified above. -/
def source (i:Inputs) :C.State Stack Label :=initial (environment i) (tape i) i.square i.cube i.fourth
/-- Complete47-word stopped bank retains all25 input environment fields and all four source words. -/
def result (i:Inputs) :Stack→List Bool :=
  Function.update (data (environment i) (tape i) i.square i.cube i.fourth) (aux .total)
    (SemiprimeD1StackSourceIncidenceSpec.total i.ids i.square i.cube i.fourth i.rows)
/-- Genuine final halt, both flags clear and real return stack empty. -/
def done (i:Inputs) :C.State Stack Label :=⟨none,none,none,result i,[]⟩
/-- Actual input byte budget includes dictionary/key/query/chosen/prefix and all actual occurrence/power bytes. -/
def inputSize (i:Inputs) :Nat :=
  (tape i).length+SemiprimeD1StackSourceEnvironmentBounds.cacheSize i.ids i.chosen i.query i.pfx+
    i.square.length+i.cube.length+i.fourth.length
/-- The input budget pays its actual literal nonempty cache terminal and unit allowance. -/
theorem inputSize_pos (i:Inputs) :0 < inputSize i :=by
  unfold inputSize SemiprimeD1StackSourceEnvironmentBounds.cacheSize
  omega
/-- Every intermediate sum's term-width increment is charged to these actual power words. -/
def rowWidth (i:Inputs) :Nat :=i.square.length+i.cube.length+i.fourth.length+1
end RiemannGaussian.SemiprimeD1StackSourceIncidenceEncoding
