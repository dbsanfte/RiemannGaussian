/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackUnaryProductRaw
import RiemannGaussian.SemiprimeD1RecoveryNodeBits
/-! # Fixed literal recovery-width wiring before all acquired metadata
This module defines64 compile-time syntax locations. Neither a polynomial AST,
natural gate value nor evaluator callback is an input or runtime control value.
Every selected wire will be a literal physical stack address.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWidthCircuit
/-- Exactly64 static arithmetic result locations. -/
abbrev Gate:=Fin 64
/-- The six literal constants are fixed before all original metadata. -/
abbrev Literal:=Fin 6
/-- Literal instruction counts, independent of every input word. -/
def literalValue (k:Literal) :Nat:=match k.val with | 0=>1 | 1=>2 | 2=>3 | 3=>4 | 4=>10 | _=>20
/-- Literal constants occupy the first six distinct static registers. -/
def literalGate (k:Literal) :Gate:=⟨k.val,by omega⟩
/-- Fixed input/cache/register wires; no unbounded operand or source getter appears here. -/
inductive Source where | a | m | n | reg (gate:Gate) deriving DecidableEq,Fintype,Repr
/-- Compile-time source instruction forms, not a runtime AST or operand. -/
inductive Op where | literal (value:Literal) | add (left right:Source) | mul (left right:Source)
  deriving DecidableEq,Repr
/-- Complete fixed source wiring of the original nonnegative width polynomial. -/
def node (g:Gate) :Op:=match g.val with
  | 0=>.literal 0
  | 1=>.literal 1
  | 2=>.literal 2
  | 3=>.literal 3
  | 4=>.literal 4
  | 5=>.literal 5
  | 6=>.add (.a) (.reg 0)
  | 7=>.mul (.reg 3) (.m)
  | 8=>.mul (.n) (.reg 7)
  | 9=>.add (.n) (.reg 0)
  | 10=>.add (.reg 8) (.reg 0)
  | 11=>.mul (.reg 9) (.reg 10)
  | 12=>.add (.reg 11) (.reg 7)
  | 13=>.add (.reg 12) (.reg 0)
  | 14=>.mul (.reg 1) (.reg 13)
  | 15=>.add (.reg 14) (.reg 0)
  | 16=>.mul (.reg 15) (.reg 10)
  | 17=>.add (.reg 16) (.reg 0)
  | 18=>.add (.reg 7) (.a)
  | 19=>.add (.reg 18) (.reg 0)
  | 20=>.mul (.reg 6) (.reg 8)
  | 21=>.mul (.reg 19) (.reg 8)
  | 22=>.add (.reg 20) (.reg 21)
  | 23=>.add (.reg 22) (.reg 0)
  | 24=>.add (.reg 7) (.reg 0)
  | 25=>.mul (.reg 23) (.reg 24)
  | 26=>.add (.reg 7) (.reg 23)
  | 27=>.add (.reg 26) (.reg 2)
  | 28=>.mul (.reg 27) (.reg 7)
  | 29=>.add (.reg 25) (.reg 7)
  | 30=>.add (.reg 29) (.reg 23)
  | 31=>.add (.reg 30) (.reg 28)
  | 32=>.add (.reg 31) (.reg 0)
  | 33=>.mul (.reg 3) (.reg 6)
  | 34=>.mul (.reg 33) (.n)
  | 35=>.mul (.reg 34) (.m)
  | 36=>.mul (.reg 3) (.reg 19)
  | 37=>.mul (.reg 36) (.n)
  | 38=>.mul (.reg 37) (.m)
  | 39=>.add (.reg 7) (.reg 35)
  | 40=>.add (.reg 39) (.reg 38)
  | 41=>.add (.reg 40) (.reg 2)
  | 42=>.mul (.reg 7) (.reg 41)
  | 43=>.mul (.reg 33) (.m)
  | 44=>.add (.reg 35) (.reg 7)
  | 45=>.add (.reg 44) (.reg 42)
  | 46=>.add (.reg 45) (.reg 43)
  | 47=>.add (.reg 46) (.reg 0)
  | 48=>.mul (.reg 6) (.reg 7)
  | 49=>.mul (.reg 48) (.n)
  | 50=>.mul (.reg 6) (.reg 6)
  | 51=>.add (.reg 49) (.reg 50)
  | 52=>.add (.reg 51) (.a)
  | 53=>.add (.reg 52) (.reg 4)
  | 54=>.add (.reg 7) (.reg 42)
  | 55=>.add (.reg 54) (.reg 48)
  | 56=>.add (.reg 55) (.reg 0)
  | 57=>.add (.reg 53) (.reg 17)
  | 58=>.add (.reg 57) (.reg 32)
  | 59=>.add (.reg 58) (.reg 47)
  | 60=>.add (.reg 59) (.reg 56)
  | 61=>.add (.reg 60) (.reg 48)
  | 62=>.add (.reg 61) (.reg 42)
  | _=>.add (.reg 62) (.reg 5)
/-- Literal left wire, with an unused constant-site default chosen disjoint from every gate. -/
def left (g:Gate) :Source:=match node g with | .literal _=>.a | .add l _| .mul l _=>l
/-- Literal right wire is always an original input/cache or an earlier static gate. -/
def right (g:Gate) :Source:=match node g with | .literal _=>.m | .add _ r| .mul _ r=>r
/-- Fixed original/cache sources precede every gate; actual register wires strictly precede the destination. -/
def Earlier (g:Gate) :Source→Prop | .reg j=>j.val<g.val | _=>True
/-- Topological wire comparison is a literal decidable finite-source property. -/
instance (g:Gate) (s:Source) :Decidable (Earlier g s):=by
  cases s <;> unfold Earlier <;> infer_instance
/-- Every actual left wire is already physically available when its static gate is reached. -/
theorem left_earlier (g:Gate) :Earlier g (left g):=by fin_cases g <;> decide
/-- Every product's directly aliased right register is distinct from its fresh actual output. -/
theorem right_earlier (g:Gate) :Earlier g (right g):=by fin_cases g <;> decide
/-- All literal loads fit the same fixed20-location literal control. -/
theorem literal_bounds (k:Literal) :1≤ literalValue k ∧ literalValue k≤20:=by fin_cases k <;> decide
/-- Fixed gate wiring associates each literal with its unique actual result register. -/
theorem literal_node (k:Literal) :node (literalGate k)=.literal k:=by fin_cases k <;> rfl
/-- Literal-mode labels arise only at their fixed literal gate. -/
theorem node_literal (g:Gate) (k:Literal) (h:node g=.literal k) :g=literalGate k:=by
  fin_cases g <;> simp only [node,Op.literal.injEq,reduceCtorEq] at h
  all_goals subst k;rfl
end RiemannGaussian.SemiprimeD1StackRecoveryWidthCircuit
