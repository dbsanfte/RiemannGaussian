/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicCarry
/-! # Exact physical phase payload specifications
Payload and all word functions below are PROOF VIEWS ONLY. Neither this record,
a word-list/getter nor any expected target/guard/verdict is an executing input or
finite-control field. The final program still initially receives only N/raw/index.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 1000000
namespace RiemannGaussian.SemiprimeD1StackPublicCarryState
open SemiprimeD1StackPublicCarry
/-- Proof-side view of the fifteen actual Boolean data stacks; NOT machine control. -/
structure Payload where
  /-- Retained original raw assignment bytes. -/
  raw : List Bool := []
  /-- Exact actual unread assignment suffix. -/
  reader : List Bool := []
  /-- Actual literal three-marker cache. -/
  three : List Bool := []
  /-- Disposable physical counter work. -/
  todo : List Bool := []
  /-- Actual reverse history or cleared difference work. -/
  history : List Bool := []
  /-- Actual produced vector or subsequently framed carry record. -/
  vector : List Bool := []
  /-- Actual block counter, fresh right comparison copy or right sum. -/
  blockCount : List Bool := []
  /-- Actual block word, fresh left comparison copy or parsed target. -/
  blockOut : List Bool := []
  /-- Actual shared restoring scratch, empty between calls. -/
  scratch : List Bool := []
  /-- Actual acquired original coefficient word. -/
  coefficient : List Bool := []
  /-- Actual acquired original previous-carry word. -/
  previous : List Bool := []
  /-- Actual acquired original next-carry word. -/
  next : List Bool := []
  /-- Actual physically produced parser/comparison Boolean. -/
  valid : List Bool := []
  /-- Actual copied-modulus low-bit-replaced bound cache. -/
  bound : List Bool := []
  /-- Actual final computed carry verdict. -/
  output : List Bool := []
/-- Literal physical auxiliary-cell projection. -/
def get (p : Payload) : Aux→List Bool
  | .raw=>p.raw
  | .reader=>p.reader
  | .three=>p.three
  | .todo=>p.todo
  | .history=>p.history
  | .vector=>p.vector
  | .blockCount=>p.blockCount
  | .blockOut=>p.blockOut
  | .scratch=>p.scratch
  | .coefficient=>p.coefficient
  | .previous=>p.previous
  | .next=>p.next
  | .valid=>p.valid
  | .bound=>p.bound
  | .output=>p.output
/-- Proof-side description of ONE physical auxiliary write. -/
def set (p : Payload) (k : Aux) (word : List Bool) : Payload := match k with
  | .raw=>{p with raw:=word}
  | .reader=>{p with reader:=word}
  | .three=>{p with three:=word}
  | .todo=>{p with todo:=word}
  | .history=>{p with history:=word}
  | .vector=>{p with vector:=word}
  | .blockCount=>{p with blockCount:=word}
  | .blockOut=>{p with blockOut:=word}
  | .scratch=>{p with scratch:=word}
  | .coefficient=>{p with coefficient:=word}
  | .previous=>{p with previous:=word}
  | .next=>{p with next:=word}
  | .valid=>{p with valid:=word}
  | .bound=>{p with bound:=word}
  | .output=>{p with output:=word}
/-- Actual full 51-stack payload view, with original public/target data retained. -/
def view (context : T.Stack→List Bool) (p : Payload) : Stack→List Bool := Sum.elim context (get p)
/-- Exact auxiliary update at the written role. -/
theorem get_set (p : Payload) (k j : Aux) (word : List Bool) :
    get (set p k word) j=if j=k then word else get p j := by cases k <;> cases j <;> rfl
/-- Physical stack update and the proof-side record update coincide exactly. -/
theorem view_set (context : T.Stack→List Bool) (p : Payload) (k : Aux) (word : List Bool) :
    view context (set p k word)=Function.update (view context p) (.inr k) word := by
  funext j
  rcases j with j|j
  · rfl
  · by_cases h : j=k
    · subst j;simp [view,get_set,Function.update]
    · simp [view,get_set,Function.update,h]
/-- Exact three seed markers, physically pushed by the program. -/
def three : List Bool := [true,true,true]
/-- Original raw-input phase before the three literal count pushes. -/
def rawPayload (raw : List Bool) : Payload := {raw:=raw}
/-- Raw width is the ACTUAL acquired modulus WORD length. -/
def width (context : T.Stack→List Bool) : List Bool := context modulusRole
/-- Actual source target, produced by the original-input target procedure. -/
def target (context : T.Stack→List Bool) : List Bool := context targetRole
/-- Actual acquired radix-width cache, not a supplied offset answer. -/
def radix (context : T.Stack→List Bool) : List Bool := context radixRole
/-- Actual original coefficient word, produced by the real word-block calls. -/
def coefficient (context : T.Stack→List Bool) (raw : List Bool) : List Bool :=
  SemiprimeD1StackWordBlockExecution.result raw (width context)
/-- Actual original previous word, with exact raw high zeros/EOF padding. -/
def previous (context : T.Stack→List Bool) (raw : List Bool) : List Bool :=
  SemiprimeD1StackWordBlockExecution.result (raw.drop (width context).length) (width context)
/-- Actual original next word, in the third original block position. -/
def next (context : T.Stack→List Bool) (raw : List Bool) : List Bool :=
  SemiprimeD1StackWordBlockExecution.result ((raw.drop (width context).length).drop (width context).length) (width context)
/-- Exact actual cache role of each raw word. -/
def wordAux (k : Fin 3) : Aux := if k=0 then .coefficient else if k=1 then .previous else .next
/-- Actual original word cache role is auxiliary, not a native word getter. -/
theorem wordRole_eq (k : Fin 3) : wordRole k=.inr (wordAux k) := rfl
/-- The three actually acquired words, only as a correctness specification. -/
def word (context : T.Stack→List Bool) (raw : List Bool) (k : Fin 3) : List Bool :=
  if k=0 then coefficient context raw else if k=1 then previous context raw else next context raw
/-- The actual chronological raw-block list, not an execution input. -/
theorem blocks_three (context : T.Stack→List Bool) (raw : List Bool) :
    SemiprimeD1StackWordVectorSpec.blocks (width context) 3 raw=
      [coefficient context raw,previous context raw,next context raw] := rfl
/-- Exact original unread raw suffix after all three physical words. -/
def suffix (context : T.Stack→List Bool) (raw : List Bool) : List Bool := raw.drop (3*(width context).length)
/-- Actual physically produced vector, before the real field-reader consumes it. -/
def produced (context : T.Stack→List Bool) (raw : List Bool) : Payload :=
  {raw:=raw,reader:=suffix context raw,three:=three,
    vector:=SemiprimeD1TensorTapeCodec.vectorBits [coefficient context raw,previous context raw,next context raw]}
/-- Exact parsed operand-cache phase; every parser/work cell is empty. -/
def parsed (context : T.Stack→List Bool) (raw : List Bool) : Payload :=
  {raw:=raw,reader:=suffix context raw,three:=three,coefficient:=coefficient context raw,
    previous:=previous context raw,next:=next context raw}
/-- The actual copied-modulus LOW-BIT replacement, not native exponentiation. -/
def boundWord (context : T.Stack→List Bool) : List Bool := false::(width context).tail
/-- Actual parsed operands and the physically acquired bound cache. -/
def ready (context : T.Stack→List Bool) (raw : List Bool) : Payload :=
  {parsed context raw with bound:=boundWord context}
/-- Actual fresh bound chosen by each physical numeric guard. -/
def guardBound (context : T.Stack→List Bool) (k : Fin 3) : List Bool :=
  if k=0 then width context else boundWord context
/-- Actual executed WordLess answer, used ONLY to specify the resulting bit. -/
def guardAnswer (context : T.Stack→List Bool) (raw : List Bool) (k : Fin 3) : Bool :=
  SemiprimeD1StackWordLessExecution.answer (word context raw k) (guardBound context k)
/-- Actual integer equation, not modular equality. -/
def equationAnswer (context : T.Stack→List Bool) (raw : List Bool) : Bool :=
  SemiprimeD1StackCarryEquationExecution.answer (radix context) (coefficient context raw) (previous context raw)
    (target context) (next context raw)
/-- Exact computed strict guards AND integer equation, with no advised truth. -/
def answer (context : T.Stack→List Bool) (raw : List Bool) : Bool :=
  guardAnswer context raw 0 && (guardAnswer context raw 1 && (guardAnswer context raw 2 && equationAnswer context raw))
/-- Only retained raw/suffix/three/bound caches and actual output remain. -/
def clean (context : T.Stack→List Bool) (raw : List Bool) (out : Bool) : Payload :=
  {raw:=raw,reader:=suffix context raw,three:=three,bound:=boundWord context,output:=[out]}
end RiemannGaussian.SemiprimeD1StackPublicCarryState
