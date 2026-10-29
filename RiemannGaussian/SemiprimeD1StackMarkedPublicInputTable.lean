/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticWordTable
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputCompactBounds
import RiemannGaussian.SemiprimeD1StackPublicInputTable
/-! # One fixed144-role whole marked input-table source
Inputs are only binary N, actual unary descriptor index, actual side singleton
and the physically acquired scope bank. Every actual DFS leaf executes the
immutable66 source followed by real binary compaction before word framing.
-/
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 262144
set_option maxRecDepth 32768
namespace RiemannGaussian.SemiprimeD1StackMarkedPublicInputTable
namespace P
export SemiprimeD1StackMarkedPublicInputCompact (Stack Label program initial coefficient)
end P
namespace M
export SemiprimeD1StackMarkedPublicInput (checker word product aux)
end M
namespace G
export SemiprimeD1StackStaticWordTable (Static)
end G
/-- Literal inventory of all66 real checker/helper/shadow words before N. -/
def roles : List P.Stack :=
  SemiprimeD1StackPublicInputTable.roles.map M.checker++
  (List.finRange 5).map M.word++
  ([.multiplier,.multiplicand,.scratch,.product] : List SemiprimeD1StackUnaryProduct.Stack).map M.product++
  ([.side,.widthTemplate,.shifted,.copyScratch,.output] : List SemiprimeD1StackMarkedPublicInput.Aux).map M.aux
/-- Every physical role is visited once, including the temporarily used trim shadow. -/
theorem roles_nodup : roles.Nodup := by decide
/-- Exactly66 literal physical positions. -/
theorem roles_length : roles.length=66 := by decide
/-- Dormant aliases and all checker caches are included in physical clearing. -/
theorem roles_complete (k : P.Stack) : k∈roles := by
  have he : roles.toFinset=(Finset.univ : Finset P.Stack) := by decide
  have hk : k∈roles.toFinset := by rw [he];exact Finset.mem_univ k
  exact List.mem_toFinset.mp hk
/-- ONE static source program/inventory before every original input or arity. -/
def static : G.Static P.Stack P.Label :=
  ⟨P.program,SemiprimeD1StackMarkedPublicInputCompact.ctl .start,
    M.checker SemiprimeD1StackPublicInput.assignment,M.aux .output,roles,roles_complete,roles_nodup⟩
/-- Checker66, actual original-input template66, count7 and DFS5. -/
abbrev Stack := SemiprimeD1StackStaticWordTable.Stack P.Stack
/-- Fixed finite labels; neither arity nor an original number enters control. -/
abbrev Label := SemiprimeD1StackStaticWordTable.Label P.Label roles.length
/-- Parameterless literal whole marked-table compiler. -/
def program : Label → SemiprimeD1StackCalls.Instruction Stack Label :=
  SemiprimeD1StackStaticWordTable.program static
/-- Only original N, index and side are in the template; the raw operand is empty. -/
def inputTemplate (bits indexWord : List Bool) (side : Bool) : P.Stack → List Bool :=
  (P.initial bits [] indexWord side).data
/-- Actual binary scope-ID vector is physically parsed/counted, never advised as arity. -/
def initial (bits indexWord : List Bool) (side : Bool) (bank : List Bool) :
    SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackStaticWordTable.initial static (inputTemplate bits indexWord side) bank
/-- Genuine finite source fixed before all original inputs and scopes. -/
def machine : Turing.FinTM2 := SemiprimeD1StackStaticWordTable.machine static
/-- Every leaf's raw-assignment slot is initially physically empty. -/
theorem template_raw (bits indexWord : List Bool) (side : Bool) :
    inputTemplate bits indexWord side static.raw=[] := rfl
/-- Actual assignment reversal produces the ordinary compact source initial bank. -/
theorem template_raw_update (bits raw indexWord : List Bool) (side : Bool) :
    Function.update (inputTemplate bits indexWord side) static.raw raw=
      (P.initial bits raw indexWord side).data := by
  change Function.update
    (Sum.elim (SemiprimeD1StackPublicInput.initial bits [] indexWord).data
      (SemiprimeD1StackMarkedPublicInput.privateInput [side]))
    (Sum.inl SemiprimeD1StackPublicInput.assignment) raw=_
  rw [Sum.update_elim_inl]
  have h := SemiprimeD1StackPublicInputTable.template_raw_update bits raw indexWord
  change Function.update (SemiprimeD1StackPublicInput.initial bits [] indexWord).data
    SemiprimeD1StackPublicInput.assignment raw=(SemiprimeD1StackPublicInput.initial bits raw indexWord).data at h
  rw [h]
  rfl
/-- Complete physical inventory including both66-role banks and every helper. -/
theorem stack_card : Fintype.card Stack=144 := by
  rw [SemiprimeD1StackStaticWordTable.stack_card,SemiprimeD1StackMarkedPublicInputCompact.stack_card]
/-- Every original number and assignment stays in Boolean data words. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackStaticWordTable.control_finite static
end RiemannGaussian.SemiprimeD1StackMarkedPublicInputTable

