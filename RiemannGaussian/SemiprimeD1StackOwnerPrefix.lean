/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1OwnerPrefixBits
import RiemannGaussian.SemiprimeD1StackWordEqualExecution
import RiemannGaussian.SemiprimeD1TensorTapeFieldBytecode
import RiemannGaussian.SemiprimeD1StackProcedureTrace

/-! # Actual physical owner-prefix compatibility acquisition
The fixed finite program parses actual framed wire keys, copies the retained
query key, executes literal binary equality, and reads each original value bit.
Its two finite compatibility flags are COMPUTED; no prefix/count/allowed oracle
or numeric value is hidden in its instruction table or transient control.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackOwnerPrefix
namespace C
export SemiprimeD1StackCalls (Instruction State execute step run)
end C
namespace E
export SemiprimeD1StackWordEqual (Label code)
export SemiprimeD1StackAdder (Stack store)
end E
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
/-- Six literal caller roles, in addition to all four actual equality roles. -/
inductive Aux where | query | reader | fieldScratch | valid | copyScratch | output
  deriving DecidableEq,Repr
instance : Fintype Aux := Fintype.ofList [.query,.reader,.fieldScratch,.valid,.copyScratch,.output]
  (by intro k;cases k <;> simp)
/-- Every data role is a fixed Boolean tape before every wire and prefix. -/
abbrev Stack := E.Stack⊕Aux
/-- At most three computed Boolean flags occur in finite control. -/
inductive Label where
  | loop (low high : Bool) | parse (low high : Bool) | parsed (low high : Bool)
  | copyKey (low high : Bool) | compare (low high : Bool) | matched (low high : Bool)
  | value (low high same : Bool)
  | high (low high : Bool) | low (low : Bool) | done | abort
  | field (low high : Bool) (pc : F.Label)
  | copy (low high : Bool) (pc : Fin 9)
  | equal (low high : Bool) (pc : E.Label)
  deriving Fintype
/-- Literal parser operands share only its actual key output with equality. -/
def fieldStack : F.Stack→Stack
  | .inl .input=>.inr .reader
  | .inl .scratch=>.inr .fieldScratch
  | .inl .output=>.inl .left
  | .inr _=>.inr .valid
/-- Physical copy preserves query bytes; each comparison consumes its own copy. -/
def copyStack (k : Fin 3) : Stack :=
  if k=0 then .inr .query else if k=1 then .inl .right else .inr .copyScratch
/-- ONE fixed finite instruction table; all key matching executes actual code. -/
def program : Label→C.Instruction Stack Label
  | .loop low high=>.base (.pop (.inr .reader) (.high low high) (.high low high) (.parse low high))
  | .parse low high=>.call (.field low high (F.active .tagPop (none,false))) (.parsed low high)
  | .parsed low high=>.base (.pop (.inr .valid) .abort .abort (.copyKey low high))
  | .copyKey low high=>.call (.copy low high 0) (.compare low high)
  | .compare low high=>.call (.equal low high .loop) (.matched low high)
  | .matched low high=>.base (.pop (.inl .output) .abort (.value low high false) (.value low high true))
  | .value low high same=>.base (.pop (.inr .reader) .abort
      (.loop low (high && !same)) (.loop (low && !same) high))
  | .high low high=>.base (.push (.inr .output) high (.low low))
  | .low low=>.base (.push (.inr .output) low .done)
  | .done | .abort=>.base .halt
  | .field low high pc=>SemiprimeD1StackMultiplierLink.instruction fieldStack (Label.field low high) (F.code pc)
  | .copy low high pc=>SemiprimeD1StackMultiplierLink.instruction copyStack (Label.copy low high) (SemiprimeD1StackCopy.code pc)
  | .equal low high pc=>SemiprimeD1StackMultiplierLink.instruction Sum.inl (Label.equal low high) (E.code pc)
/-- Mathematical projection of physical data; never an executed source getter. -/
def data (query reader left right comparison valid output : List Bool) : Stack→List Bool
  | .inl k=>E.store left right [] comparison k
  | .inr .query=>query
  | .inr .reader=>reader
  | .inr .valid=>valid
  | .inr .output=>output
  | .inr .fieldScratch | .inr .copyScratch=>[]
/-- Only the original binary wire key and actual framed prefix are initial data. -/
def initial (query reader : List Bool) : C.State Stack Label :=
  ⟨some (.loop true true),none,none,data query reader [] [] [] [] [],[]⟩
/-- Literal complete halt data: retained key/tail and physically acquired flags. -/
def done (query : List Bool) (rows : List (List Bool×Bool)) (tail : List Bool) : C.State Stack Label :=
  let answer:=SemiprimeD1OwnerPrefixBits.scan query rows true true
  ⟨none,none,none,data query tail [] [] [] [] [answer.1,answer.2],[]⟩
/-- One actual fixed finite machine, with no key/prefix length in its control. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inr .reader) (.inr .output) (.loop true true) program
/-- All ten actual Boolean roles are included in resource inventory. -/
theorem stack_card : Fintype.card Stack=10 := by decide
/-- Actual key/parser/work ports are distinct. -/
theorem field_injective : Function.Injective fieldStack := by decide
/-- Actual query/comparison/copy-scratch roles are distinct. -/
theorem copy_injective : Function.Injective copyStack := by decide
/-- All data and real return alphabets are fixed and finite. -/
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (.inr .reader) (.inr .output) (.loop true true) program
/-- Transient flags/labels contain no natural/list/function/table/clock payload. -/
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite (.inr .reader) (.inr .output) (.loop true true) program
end RiemannGaussian.SemiprimeD1StackOwnerPrefix
