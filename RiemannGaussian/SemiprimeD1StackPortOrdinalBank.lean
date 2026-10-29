/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPortCatalogueBounds
import RiemannGaussian.SemiprimeD1StackOrdinalBankLoop
/-! # Actual original port occurrence tally to the canonical padded ordinal bank
The complete port producer runs once. Its physically pushed occurrence tally
is the actual ordinal-bank operand. All original port/edge/metadata caches are
retained; no numeric M, code catalogue or ID array is an input.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackPortOrdinalBank
namespace P
export SemiprimeD1StackPortCatalogue (Stack Label program originalInput aux input)
end P
namespace O
export SemiprimeD1StackOrdinalBank (Stack Label program count ids initial data)
end O
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace Link
export SemiprimeD1StackValidationLink (instruction)
end Link
/-- Fixed Boolean source and bank workspace roles before every N. -/
abbrev Stack := P.Stack ⊕ O.Stack
/-- Literal old complete port source inclusion. -/
def portStack : P.Stack→Stack := Sum.inl
/-- Actual acquired occurrence counter, kept distinct from original wire IDs. -/
def count : Stack := portStack (P.aux .occurrenceOrdinal)
/-- Bank count is the already acquired physical occurrence tally; all work roles are fresh. -/
def bankStack (key:O.Stack) : Stack := if key=O.count then count else .inr key
/-- Actual padded binary occurrence-ID vector output. -/
def ids : Stack := .inr O.ids
/-- Three static caller continuations, independent of graph/input dimensions. -/
inductive Control where
  | start | bank | halt
  deriving DecidableEq
instance : Fintype Control := Fintype.ofList [.start,.bank,.halt]
  (by intro k;cases k <;> simp)
/-- Literal source and nested ordinal procedure labels; only finiteness is needed. -/
abbrev Label := Control ⊕ (P.Label ⊕ O.Label)
/-- Actual original-N port acquisition followed by the actual tally-controlled bank. -/
def program : Label→C.Instruction Stack Label
  | .inr (.inl pc) => Link.instruction portStack (fun p=>.inr (.inl p)) (P.program pc)
  | .inr (.inr pc) => Link.instruction bankStack (fun p=>.inr (.inr p)) (O.program pc)
  | .inl .start => .call (.inr (.inl (.local .main))) (.inl .bank)
  | .inl .bank => .call (.inr (.inr (.inl .start))) (.inl .halt)
  | .inl .halt => .base .halt
/-- Only original binary N is present initially. -/
def input (bits:List Bool) : Stack→List Bool := Sum.elim (P.input bits) (fun _=>[])
/-- Actual source initial state; no tally or ID bank is preloaded. -/
def initial (bits:List Bool) : C.State Stack Label := ⟨some (.inl .start),none,none,input bits,[]⟩
/-- One fixed finite original-N machine. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (portStack P.originalInput) ids (.inl .start) program
/-- Source stacks are included without aliasing. -/
theorem portStack_injective : Function.Injective portStack := Sum.inl_injective
/-- The retained source tally is disjoint from all fresh actual bank work roles. -/
theorem bankStack_injective : Function.Injective bankStack := by
  intro a b h
  by_cases ha:a=O.count
  · subst a
    by_cases hb:b=O.count
    · exact hb.symm
    · simp only [bankStack,ite_true,ite_eq_right hb] at h
      cases h
  · by_cases hb:b=O.count
    · subst b
      simp only [bankStack,ite_eq_right ha,ite_true] at h
      cases h
    · simpa only [bankStack,ite_eq_right ha,ite_eq_right hb,Sum.inr.injEq] using h
/-- No infinite data alphabet hides a count, word list, graph or input-dependent label. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (portStack P.originalInput) ids (.inl .start) program
/-- Eighty-seven fixed Boolean roles; the unused fresh count role remains empty. -/
theorem stack_card : Fintype.card Stack=87 := by decide
end RiemannGaussian.SemiprimeD1StackPortOrdinalBank
