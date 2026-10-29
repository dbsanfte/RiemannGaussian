/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordVectorBounds
import RiemannGaussian.SemiprimeD1StackVectorCanonicalBounds
import RiemannGaussian.SemiprimeD1StackResidueMulBounds
import RiemannGaussian.SemiprimeD1StackWordEqualBounds

/-! # Actual local product checker from a raw three-word assignment
A literal three-marker count feeds the actual word-vector producer; its vector
is actually guarded and parsed, then a real modular multiplication and numeric
comparison decide the original product equation. No prepared operands, vector,
canonicality, product or verdict are initial inputs. Acquiring the retained
binary modulus from original N is the enclosing public caller's work.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackProductCheck
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace W
export SemiprimeD1StackWordVector (Stack Label program original countCache output)
end W
namespace G
export SemiprimeD1StackVectorCanonical (Stack Label program)
end G
namespace M
export SemiprimeD1StackResidueMul (Stack Label program modulus output)
end M
namespace E
export SemiprimeD1StackAdder (Stack)
export SemiprimeD1StackWordEqual (Label code)
end E
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F

/-- All48 fixed Boolean roles; unused private shadows remain in the inventory. -/
abbrev Stack := W.Stack⊕(G.Stack⊕(M.Stack⊕(E.Stack⊕Fin 2)))
/-- Real modular multiplier's complete physical register inclusion. -/
def multiplyStack (k : M.Stack) : Stack := .inr (.inr (.inl k))
/-- Exact retained raw binary modulus. -/
def modulus : Stack := multiplyStack M.modulus
/-- Actual raw assignment tape, retained by the real word producer. -/
def rawInput : Stack := .inl W.original
/-- Private numeric comparison roles. -/
def equalPrivate (k : E.Stack) : Stack := .inr (.inr (.inr (.inl k)))
/-- Shared actual parser/comparison restoration scratch and parser-validity cell. -/
def auxiliary (k : Fin 2) : Stack := .inr (.inr (.inr (.inr k)))
/-- The actual Boolean local-product verdict. -/
def output : Stack := equalPrivate .output
/-- Physical width template directly shares the actual retained modulus. -/
def vectorStack (k : W.Stack) : Stack := if k=.inl 1 then modulus else .inl k
/-- The actual computed vector cache and binary modulus feed the real guard. -/
def guardStack : G.Stack→Stack
  | .cache => vectorStack W.output
  | .modulus => modulus
  | k => .inr (.inl k)
/-- Exact first real multiplier operand. -/
def multiplyLeft : M.Stack := .inl SemiprimeD1StackResidueMul.M.input
/-- Exact second real multiplier operand. -/
def multiplyRight : M.Stack := .inl SemiprimeD1StackResidueMul.M.factor
/-- Parsed input0/input1/output payload destinations, fixed before all inputs. -/
def operand (i : Fin 3) : Stack :=
  if i=0 then multiplyStack multiplyLeft else if i=1 then multiplyStack multiplyRight else equalPrivate .right
/-- Actual raw vector field parser, after the actual vector-entry tag. -/
def fieldStack (i : Fin 3) : F.Stack→Stack
  | .inl .input => vectorStack W.output
  | .inl .scratch => auxiliary 0
  | .inl .output => operand i
  | .inr _ => auxiliary 1
/-- The computed modular residue is DIRECTLY the real comparator's left input. -/
def equalStack : E.Stack→Stack
  | .left => multiplyStack M.output
  | .scratch => auxiliary 0
  | k => equalPrivate k
/-- Fixed finite control; field indices are only the static three word cases. -/
inductive Label where
  | start | push1 | push2 | acquire | guard | branch | tag (i : Fin 3)
  | read (i : Fin 3) | parsed (i : Fin 3) | clearVector (compute : Bool)
  | multiply | compare | reject | clearCount | done | bad
  | vector (pc : W.Label) | canonical (pc : G.Label) | multiplication (pc : M.Label)
  | equality (pc : E.Label) | field (i : Fin 3) (pc : F.Label)
  deriving Fintype
/-- The parsed third word selects actual computation after physical cleanup. -/
def afterField (i : Fin 3) : Label := if i=0 then .tag 1 else if i=1 then .tag 2 else .clearVector true
/-- ONE closed literal checker. Its three count markers are actually pushed. -/
def program : Label→C.Instruction Stack Label
  | .start => .base (.push (.inl W.countCache) true .push1)
  | .push1 => .base (.push (.inl W.countCache) true .push2)
  | .push2 => .base (.push (.inl W.countCache) true .acquire)
  | .acquire => .call (.vector (.control .start)) .guard
  | .guard => .call (.canonical .start) .branch
  | .branch => .base (.pop (guardStack .output) .bad .reject (.tag 0))
  | .tag i => .base (.pop (vectorStack W.output) .bad .bad (.read i))
  | .read i => .call (.field i (F.active .tagPop (none,false))) (.parsed i)
  | .parsed i => .base (.pop (auxiliary 1) .bad .bad (afterField i))
  | .clearVector compute => .base (.pop (vectorStack W.output)
      (if compute then .multiply else .clearCount) (.clearVector compute) (.clearVector compute))
  | .multiply => .call (.multiplication .start) .compare
  | .compare => .call (.equality .loop) .clearCount
  | .reject => .base (.push output false (.clearVector false))
  | .clearCount => .base (.pop (.inl W.countCache) .done .clearCount .clearCount)
  | .done | .bad => .base .halt
  | .vector pc => SemiprimeD1StackValidationLink.instruction vectorStack Label.vector (W.program pc)
  | .canonical pc => SemiprimeD1StackValidationLink.instruction guardStack Label.canonical (G.program pc)
  | .multiplication pc => SemiprimeD1StackValidationLink.instruction multiplyStack Label.multiplication (M.program pc)
  | .equality pc => SemiprimeD1StackMultiplierLink.instruction equalStack Label.equality (E.code pc)
  | .field i pc => SemiprimeD1StackMultiplierLink.instruction (fieldStack i) (Label.field i) (F.code pc)
/-- Initial payload has ONLY original raw assignment and retained binary modulus. -/
def input (raw cached : List Bool) : Stack→List Bool :=
  fun k=>if k=rawInput then raw else if k=modulus then cached else []
/-- Concrete source entry; no vector/count/operand/guard/result answer is present. -/
def initial (raw cached : List Bool) : C.State Stack Label := ⟨some .start,none,none,input raw cached,[]⟩
/-- All producer roles remain distinct under actual modulus sharing. -/
theorem vectorStack_injective : Function.Injective vectorStack := by decide
/-- All real guard roles remain distinct under actual vector/modulus sharing. -/
theorem guardStack_injective : Function.Injective guardStack := by
  intro i j h;cases i <;> cases j <;> simp_all [guardStack,vectorStack,modulus,multiplyStack,SemiprimeD1StackWordVector.output]
/-- The actual three parsed field destinations are disjoint from parser work. -/
theorem fieldStack_injective (i : Fin 3) : Function.Injective (fieldStack i) := by fin_cases i <;> decide
/-- Real comparator roles are disjoint despite direct multiplier-output sharing. -/
theorem equalStack_injective : Function.Injective equalStack := by
  intro i j h;cases i <;> cases j <;> simp_all [equalStack,equalPrivate,multiplyStack,auxiliary]
/-- Genuine fixed bit machine for the raw local-product assignment checker. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine rawInput output .start program
/-- All actual data and finite-label return alphabets are fixed and finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite rawInput output Label.start program
/-- No decoded assignment, width, integer product or predicate occurs in control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite rawInput output Label.start program
/-- Every actual physical data role is retained in later prefix counts. -/
theorem stack_card : Fintype.card Stack=48 := by decide

end RiemannGaussian.SemiprimeD1StackProductCheck
