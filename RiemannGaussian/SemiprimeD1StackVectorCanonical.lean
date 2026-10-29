/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWordLessExecution
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackCopy
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace

/-! # Actual canonical-word guard for a complete physical vector
The program copies the retained vector, parses actual framed words, copies the
binary modulus before each destructive comparison, and reads each real answer.
A rejected suffix is physically drained. No canonicality verdict is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVectorCanonical
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active initial)
end F
namespace W
export SemiprimeD1StackWordLess (Stack Label program store initial)
end W

/-- Ten fixed Boolean roles, with genuinely shared restored scratch. -/
inductive Stack where
  | cache | modulus | reader | word | scratch | valid | difference | copiedModulus | lessFlag | output
  deriving DecidableEq,Repr
instance : Fintype Stack := Fintype.ofList
  [.cache,.modulus,.reader,.word,.scratch,.valid,.difference,.copiedModulus,.lessFlag,.output]
  (by intro k;cases k <;> simp)
/-- Real preserving vector/modulus copy wiring. -/
def copyStack (modulus : Bool) (k : Fin 3) : Stack :=
  if k=0 then (if modulus then .modulus else .cache) else
  if k=1 then (if modulus then .copiedModulus else .reader) else .scratch
/-- Actual framed field parser consumes the live vector reader. -/
def fieldStack : F.Stack→Stack
  | .inl .input => .reader | .inl .scratch => .scratch | .inl .output => .word | .inr _ => .valid
/-- Actual complete numeric comparison consumes a word and a fresh modulus copy. -/
def lessStack : W.Stack→Stack
  | .inl .left => .word | .inl .right => .copiedModulus | .inl .scratch => .scratch
  | .inl .output => .difference | .inr _ => .lessFlag
/-- Fixed physical parser, guard and cleanup locations. -/
inductive Label where
  | start | loop | parse | parsed | copyModulus | compare | compared
  | accept | reject | clearReader | done | bad
  | copy (modulus : Bool) (pc : Fin 9) | field (pc : F.Label) | less (pc : W.Label)
  deriving DecidableEq,Fintype
/-- ONE closed program with actual canonicality-dependent control flow. -/
def program : Label→C.Instruction Stack Label
  | .start => .call (.copy false 0) .loop
  | .loop => .base (.pop .reader .bad .accept .parse)
  | .parse => .call (.field (F.active .tagPop (none,false))) .parsed
  | .parsed => .base (.pop .valid .bad .bad .copyModulus)
  | .copyModulus => .call (.copy true 0) .compare
  | .compare => .call (.less .start) .compared
  | .compared => .base (.pop .lessFlag .bad .reject .loop)
  | .accept => .base (.push .output true .done)
  | .reject => .base (.push .output false .clearReader)
  | .clearReader => .base (.pop .reader .done .clearReader .clearReader)
  | .done | .bad => .base .halt
  | .copy modulus pc => SemiprimeD1StackMultiplierLink.instruction (copyStack modulus) (Label.copy modulus)
      (SemiprimeD1StackCopy.code pc)
  | .field pc => SemiprimeD1StackMultiplierLink.instruction fieldStack Label.field (F.code pc)
  | .less pc => SemiprimeD1StackValidationLink.instruction lessStack Label.less (W.program pc)
/-- Reached clean payload view; actual scratch is empty between all real calls. -/
def store (cache cached reader word copied valid difference compared output : List Bool) : Stack→List Bool
  | .cache => cache | .modulus => cached | .reader => reader | .word => word | .scratch => []
  | .valid => valid | .difference => difference | .copiedModulus => copied | .lessFlag => compared | .output => output
/-- Original physical vector and binary modulus are the only input tapes. -/
def initial (cache cached : List Bool) : C.State Stack Label :=
  ⟨some .start,none,none,store cache cached [] [] [] [] [] [] [],[]⟩
/-- Actual copies never alias their source, destination or scratch. -/
theorem copyStack_injective (modulus : Bool) : Function.Injective (copyStack modulus) := by cases modulus <;> decide
/-- Actual parser roles are physically distinct. -/
theorem fieldStack_injective : Function.Injective fieldStack := by
  intro i j h
  rcases i with i|i <;> rcases j with j|j <;> cases i <;> cases j <;> simp_all [fieldStack]
/-- Actual comparison roles are physically distinct. -/
theorem lessStack_injective : Function.Injective lessStack := by
  intro i j h
  rcases i with i|i <;> rcases j with j|j <;> cases i <;> cases j <;> simp_all [lessStack]
/-- Fixed actual finite-machine word-vector guard. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine Stack.cache Stack.output .start program
/-- All physical data and real return-tag alphabets are finite before all inputs. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite Stack.cache Stack.output Label.start program
/-- No decoded word, natural, list or canonicality answer occurs in control. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite Stack.cache Stack.output Label.start program
/-- Every Boolean register is included in later storage bounds. -/
theorem stack_card : Fintype.card Stack=10 := by decide

end RiemannGaussian.SemiprimeD1StackVectorCanonical
