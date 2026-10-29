/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1FactorScopePairOriginal
/-! # Actual binary N plus physical factor key to ordered scope-ID vector
The complete entry acquires the N-only pair source once. The prepared copy
entry requires that same source already physically acquired, and preserves it
for repeated factors. Query-key acquisition remains a caller operation.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackFactorScopeFibre
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace P
export SemiprimeD1StackFactorScopePairs (Stack Label program input initial originalInput aux)
export SemiprimeD1StackFactorScopePairExecution (rows result done)
end P
namespace F
export SemiprimeD1StackOwnerFibre (Stack Label program initial done records values)
end F
/-- All137 actual Boolean roles, including the complete122-role source. -/
abbrev Stack :=P.Stack⊕(F.Stack⊕Unit)
/-- Direct inclusion of the complete original-N pair source. -/
def sourceStack : P.Stack→Stack :=Sum.inl
/-- Direct inclusion of the generic physical numeric-key filter. -/
def fibreStack (k : F.Stack) : Stack :=.inr (.inl k)
/-- Literal preserving-copy scratch, independent of both actual sources. -/
def scratch : Stack :=.inr (.inr ())
/-- Original binary N input role. -/
def originalInput : Stack :=sourceStack P.originalInput
/-- Retained actual factor-key/scope-ID pair catalogue. -/
def pairsOutput : Stack :=sourceStack (P.aux .output)
/-- Physical current factor key; its encoding/acquisition is the caller's work. -/
def query : Stack :=fibreStack (.inr .query)
/-- Actual selected scope-ID vector, in original ascending local-port order. -/
def output : Stack :=fibreStack (.inr .output)
/-- Source-preserving copy from retained pairs to the actual generic filter reader. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then pairsOutput else if k=1 then fibreStack (.inr .reader) else scratch
/-- Fixed complete and prepared entries, with no original count/ordinal in control. -/
inductive Label where
  | main | copy | filter | done
  | source (pc : P.Label) | fibre (pc : F.Label) | copyCode (pc : Fin 9)
  deriving Fintype
/-- Actual source call, preserving reader copy, generic filter call and halt. -/
def program : Label→C.Instruction Stack Label
  | .main=>.call (.source (.local .main)) .copy
  | .copy=>.call (.copyCode 0) .filter
  | .filter=>.call (.fibre .loop) .done
  | .done=>.base .halt
  | .source pc=>SemiprimeD1StackValidationLink.instruction sourceStack Label.source (P.program pc)
  | .fibre pc=>SemiprimeD1StackValidationLink.instruction fibreStack Label.fibre (F.program pc)
  | .copyCode pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copyCode (SemiprimeD1StackCopy.code pc)
/-- Complete two-component physical store, with the actual extra scratch empty. -/
def data (source : P.Stack→List Bool) (fibre : F.Stack→List Bool) : Stack→List Bool :=
  Sum.elim source (Sum.elim fibre (fun _=>[]))
/-- Only binary N and an actually acquired physical factor-key word enter. -/
def initial (bits key : List Bool) : C.State Stack Label :=
  ⟨some .main,none,none,data (P.input bits) (F.initial key []).data,[]⟩
/-- Genuine prepared entry AFTER the entire actual N-only pair acquisition. -/
def afterSource (bits key : List Bool) : Stack→List Bool :=data (P.result bits) (F.initial key []).data
/-- Mathematical exact retained pair bytes, not a runtime catalogue supplier. -/
def pairTape (bits : List Bool) : List Bool :=F.records ((P.rows bits).map SemiprimeD1FactorScopePairEncoding.pair) []
/-- The preserving copy has physically acquired the generic filter's reader. -/
def afterCopy (bits key : List Bool) : Stack→List Bool :=data (P.result bits) (F.initial key (pairTape bits)).data
/-- Every original source/cache byte and the physical query survive filtering. -/
def result (bits key : List Bool) : Stack→List Bool :=
  data (P.result bits) (F.done key ((P.rows bits).map SemiprimeD1FactorScopePairEncoding.pair) []).data
/-- Actual final flags and real return frames are cleared. -/
def done (bits key : List Bool) : C.State Stack Label :=⟨none,none,none,result bits key,[]⟩
/-- One fixed finite machine before every original input and factor key. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output .main program
/-- Every source, filter and scratch role is included. -/
theorem stack_card : Fintype.card Stack=137 :=by decide
/-- The literal copy uses three disjoint actual physical roles. -/
theorem copy_injective : Function.Injective copyStack :=by decide
end RiemannGaussian.SemiprimeD1StackFactorScopeFibre
