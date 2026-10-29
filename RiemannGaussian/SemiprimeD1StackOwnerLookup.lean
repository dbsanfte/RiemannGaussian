/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerPrefixComponents
/-! # Literal physical endpoint-key to original owner-ID lookup
The input is the physically acquired framed forward catalogue. The program
parses actual keys, copies its retained query, executes numeric WordEqual,
then parses the actual owner-ID payload. It never receives a permutation,
endpoint function, owner getter, matching bit, row count or clock.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeD1StackOwnerLookup
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
/-- Seven fixed caller roles in addition to the four actual equality roles. -/
inductive Aux where | query | reader | fieldScratch | valid | copyScratch | discard | output
  deriving DecidableEq
instance : Fintype Aux := Fintype.ofList [.query,.reader,.fieldScratch,.valid,.copyScratch,.discard,.output]
  (by intro k;cases k <;> simp)
/-- All eleven Boolean data roles, independent of original input. -/
abbrev Stack := E.Stack⊕Aux
/-- Only actual one-bit comparison outcomes enter control. -/
inductive Label where
  | loop | parseKey | parsedKey | copyKey | compare | matched
  | parseValue (same:Bool) | parsedValue (same:Bool) | clear | done | abort
  | field (part:Option Bool) (pc:F.Label) | copy (pc:Fin 9) | equal (pc:E.Label)
  deriving Fintype
/-- None parses the key; some parses the real payload into output or discard. -/
def fieldOutput : Option Bool→Stack
  | none=>.inl .left
  | some false=>.inr .discard
  | some true=>.inr .output
/-- Actual parser inclusion, with a computed payload destination. -/
def fieldStack (part:Option Bool) : F.Stack→Stack
  | .inl .input=>.inr .reader
  | .inl .scratch=>.inr .fieldScratch
  | .inl .output=>fieldOutput part
  | .inr _=>.inr .valid
/-- Actual query-preserving copy operands. -/
def copyStack (k:Fin 3) : Stack :=
  if k=0 then .inr .query else if k=1 then .inl .right else .inr .copyScratch
/-- Every actual field read and failed-row payload erase executes this table. -/
def program : Label→C.Instruction Stack Label
  | .loop=>.base (.pop (.inr .reader) .done .done .parseKey)
  | .parseKey=>.call (.field none (F.active .tagPop (none,false))) .parsedKey
  | .parsedKey=>.base (.pop (.inr .valid) .abort .abort .copyKey)
  | .copyKey=>.call (.copy 0) .compare
  | .compare=>.call (.equal .loop) .matched
  | .matched=>.base (.pop (.inl .output) .abort (.parseValue false) (.parseValue true))
  | .parseValue same=>.call (.field (some same) (F.active .tagPop (none,false))) (.parsedValue same)
  | .parsedValue same=>.base (.pop (.inr .valid) .abort .abort (if same then .done else .clear))
  | .clear=>.base (.pop (.inr .discard) .loop .clear .clear)
  | .done | .abort=>.base .halt
  | .field part pc=>SemiprimeD1StackMultiplierLink.instruction (fieldStack part) (Label.field part) (F.code pc)
  | .copy pc=>SemiprimeD1StackMultiplierLink.instruction copyStack Label.copy (SemiprimeD1StackCopy.code pc)
  | .equal pc=>SemiprimeD1StackMultiplierLink.instruction Sum.inl Label.equal (E.code pc)
/-- Mathematical view of the physical store, not an instruction-time evaluator. -/
def data (query reader left right comparison valid discard output:List Bool) : Stack→List Bool
  | .inl k=>E.store left right [] comparison k
  | .inr .query=>query
  | .inr .reader=>reader
  | .inr .valid=>valid
  | .inr .discard=>discard
  | .inr .output=>output
  | .inr .fieldScratch | .inr .copyScratch=>[]
open SemiprimeSourceHistogramKeyBits (frame)
/-- Actual two-field forward-map format; arbitrary suffixes remain literal. -/
def records : List (List Bool×List Bool)→List Bool→List Bool
  | [],tail=>false::tail
  | (key,value)::rows,tail=>true::frame key (frame value (records rows tail))
/-- Proof-side meaning of the actual first-match scan and retained unread tail. -/
def result (query:List Bool) : List (List Bool×List Bool)→List Bool→List Bool×List Bool
  | [],tail=>([],tail)
  | (key,value)::rows,tail=>
    if SemiprimeBitArithmetic.bitValue key=SemiprimeBitArithmetic.bitValue query
      then (value,records rows tail) else result query rows tail
/-- Only the physically acquired query and catalogue are loaded initially. -/
def initial (query reader:List Bool) : C.State Stack Label :=
  ⟨some .loop,none,none,data query reader [] [] [] [] [] [],[]⟩
/-- Exact halt state with actual returned ID and unread catalogue suffix. -/
def done (query:List Bool) (rows:List (List Bool×List Bool)) (tail:List Bool) : C.State Stack Label :=
  ⟨none,none,none,data query (result query rows tail).2 [] [] [] [] [] (result query rows tail).1,[]⟩
/-- One fixed finite TM2 for the actual prepared-map lookup. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine (.inr .reader) (.inr .output) .loop program
theorem stack_card : Fintype.card Stack=11 := by decide
theorem field_injective (part:Option Bool) : Function.Injective (fieldStack part) := by
  cases part with
  | none=>decide
  | some b=>cases b <;> decide
theorem copy_injective : Function.Injective copyStack := by decide
theorem all_alphabets_finite : ∀k,Finite (machine.Γ k) :=
  SemiprimeD1StackCalls.all_alphabets_finite (.inr .reader) (.inr .output) Label.loop program
theorem control_finite : Finite machine.σ :=
  SemiprimeD1StackCalls.control_finite (.inr .reader) (.inr .output) Label.loop program
end RiemannGaussian.SemiprimeD1StackOwnerLookup
