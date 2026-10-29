/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackGuardedDotBounds
import RiemannGaussian.SemiprimeD1StackWordVectorBounds
/-! # Actual raw assignment -> physical word vector -> guarded numerical dot
No encoded operand vector, word-list/getter, grouped assignment, canonicality,
whole-source validity, evaluation result or backend/clock is initially supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackInputDotEvaluate
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace G
export SemiprimeD1StackGuardedDotEvaluate (Stack Label program initial output status)
end G
namespace W
export SemiprimeD1StackWordVector (Stack Label program initial store original countCache output)
end W
/-- Only physically prepared source/metadata tapes; NO operand vector field. -/
structure Args where
  /-- Actual physically encoded base-expression source bytes. -/
  base : List Bool
  /-- Actual physical unary stride-marker cache. -/
  stride : List Bool
  /-- Actual physical unary frequency-marker cache. -/
  frequency : List Bool
  /-- Actual retained count-marker cache, shared with BOTH producer and dot. -/
  count : List Bool
/-- Actual source/evaluator cache view. The executed initial vector is EMPTY;
the real vector producer physically populates that same cache-output stack. -/
def withVector (args : Args) (vector : List Bool) : SemiprimeD1StackExprDot.Cache :=
  ⟨args.base,args.stride,args.frequency,args.count,vector⟩
/-- All117 Boolean roles, including unused empty private aliases. -/
abbrev Stack := G.Stack⊕W.Stack
/-- SAME actual modulus is also the real WordBlock width template. -/
def modulusRole : G.Stack := .inl SemiprimeD1StackDotEvaluate.modulus
/-- SAME actual source/evaluator count cache drives the physical word producer. -/
def countRole : G.Stack := .inl (.inl .count)
/-- SAME actual produced-vector output is the guard/dot vector-cache input. -/
def vectorRole : G.Stack := .inl (.inl .cache)
/-- Physical raw assignment input is retained by the vector producer. -/
def rawRole : Stack := .inr W.original
/-- Actual unread raw suffix, retained after all required word blocks. -/
def suffixRole : Stack := .inr (.inl 0)
/-- Actual numerical result; [] if the computed guard rejects. -/
def output : Stack := .inl G.output
/-- Actual final guard status cell. -/
def status : Stack := .inl G.status
/-- Literal direct producer-consumer wiring; no vector copy/native transport. -/
def vectorStack (k : W.Stack) : Stack :=
  if k=.inl 1 then .inl modulusRole else if k=W.countCache then .inl countRole
  else if k=W.output then .inl vectorRole else .inr k
/-- Complete fixed source/caller locations, before all original inputs. -/
inductive Label where
  | start | compute | done | acquire (pc : W.Label) | guarded (pc : G.Label)
  deriving Fintype
/-- ONE closed code table: actual vector acquisition ONCE, then actual guard/dot. -/
def program : Label→C.Instruction Stack Label
  | .start=>.call (.acquire (.control .start)) .compute
  | .compute=>.call (.guarded .start) .done
  | .done=>.base .halt
  | .acquire pc=>SemiprimeD1StackValidationLink.instruction vectorStack Label.acquire (W.program pc)
  | .guarded pc=>SemiprimeD1StackValidationLink.instruction Sum.inl Label.guarded (G.program pc)
/-- Reached physical assignment/source payload view; private vector work is empty. -/
def store (guarded : G.Stack→List Bool) (reader raw : List Bool) : Stack→List Bool :=
  Sum.elim guarded (fun k=>if k=.inl 0 then reader else if k=W.original then raw else [])
/-- Only raw assignment and physical base/metadata/modulus/suffix enter. -/
def initial (raw : List Bool) (args : Args) (cached tail : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,store (G.initial (withVector args []) cached tail).data [] raw,[]⟩
/-- All actual ten producer data roles are separate despite direct sharing. -/
theorem vector_injective : Function.Injective vectorStack := by decide
/-- Actual fixed finite machine for prepared physical sources and RAW assignment. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine rawRole output .start program
/-- Every physical data and real-return alphabet is finite before all inputs. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ Label.start program
/-- No decoded assignment, word-list, count, source AST or getter occurs in control. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ Label.start program
/-- Exact complete physical data-role count. -/
theorem stack_card : Fintype.card Stack=117 := by decide
end RiemannGaussian.SemiprimeD1StackInputDotEvaluate
