/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackStaticTable
import RiemannGaussian.SemiprimeD1StackPublicInputBounds
/-! # One fixed116-role whole-table compiler for the actual public input checker
Only original binary N, original descriptor index markers and a physically
acquired scope-ID bank are initialized. The static checker is fixed before N;
active/inactive and first/nonfirst input cases are executed by that SAME code.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 16384
namespace RiemannGaussian.SemiprimeD1StackPublicInputTable
namespace P
export SemiprimeD1StackPublicInput (Stack Label program initial assignment output index)
end P
namespace G
export SemiprimeD1StackStaticTable (Static)
end G
/-- Literal complete28-role public-acquisition inventory, fixed before N. -/
def publicRoles : List SemiprimeD1BinaryPublicAcquisition.Stack :=
  let metaStack:=SemiprimeD1BinaryDigitAcquisition.metaStack
  let bankStack:=SemiprimeD1BinaryDigitAcquisition.bankStack
  let digitRoles : List SemiprimeD1BinaryDigitAcquisition.Stack :=
    (([.input,.width,.nonzero,.threshold,.radius,.square,.exponent,.squareWork,.thresholdWork,.temporary,.radix]:
      List SemiprimeD1StackTransform.Stack).map metaStack)++
    (([.input,.width,.counter,.scratch,.temporary,.dummyLeft,.dummyRight,.output]:
      List SemiprimeD1StackDigitBlock.Stack).map (fun k=>bankStack (.inl k)))++
    [bankStack (.inr 0),bankStack (.inr 1),bankStack (.inr 2),SemiprimeD1BinaryDigitAcquisition.copyTemporary]
  digitRoles.map SemiprimeD1BinaryPublicAcquisition.digitStack++
    [SemiprimeD1BinaryPublicAcquisition.fermatStack (.inr false),SemiprimeD1BinaryPublicAcquisition.fermatStack (.inr true),
      SemiprimeD1BinaryPublicAcquisition.axesStack (.inr 0),SemiprimeD1BinaryPublicAcquisition.axesStack (.inr 1),
      SemiprimeD1BinaryPublicAcquisition.axesStack (.inr 2)]

/-- Literal complete52-role input-checker inventory, including every shadow. -/
def roles : List P.Stack :=
  publicRoles.map (fun k=>.inl (.inl k))++
    (([.widthCache,.radixCache,.indexCache,.remaining,.multiplier,.scratch,.skip,.limit,.output]:
      List SemiprimeD1StackInputWidth.Stack).map (fun k=>.inl (.inr k)))++
    (List.finRange 5).map (fun k=>.inr (.inl k))++
    (([.left,.right,.scratch,.output]:List SemiprimeD1StackAdder.Stack).map
      (fun k=>.inr (.inr (.inl (.inl k)))))++[.inr (.inr (.inl (.inr ())))]++
    (([.left,.right,.scratch,.output]:List SemiprimeD1StackAdder.Stack).map
      (fun k=>.inr (.inr (.inr (.inl k)))))++[.inr (.inr (.inr (.inr ())))]
/-- All52 roles are visited exactly once, as a compile-time fact only. -/
theorem roles_nodup : roles.Nodup := by decide
/-- The literal inventory has its fixed52 positions before all inputs. -/
theorem roles_length : roles.length=52 := by decide
/-- Dormant input/header/comparator/private shadows are included too. -/
theorem roles_complete (k : P.Stack) : k∈roles := by
  have h:roles.toFinset=(Finset.univ : Finset P.Stack):=by decide
  have hk:k∈roles.toFinset:=by rw [h];exact Finset.mem_univ k
  exact List.mem_toFinset.mp hk
/-- One constant static checker instance for ALL original inputs/descriptors.
There is no N, arity, raw assignment, predicate or budget in this value. -/
def static : G.Static P.Stack P.Label :=
  ⟨P.program,.start,P.assignment,P.output,roles,roles_complete,roles_nodup⟩
/-- The fixed finite Boolean-bank type, independent of N and descriptor values. -/
abbrev Stack := SemiprimeD1StackStaticTable.Stack P.Stack
/-- The fixed finite label type, independent of N and actual scope arity. -/
abbrev Label := SemiprimeD1StackStaticTable.Label P.Label roles.length
/-- Literal whole table program; the SAME constant checker instance for all N. -/
def program : Label→SemiprimeD1StackCalls.Instruction Stack Label :=
  SemiprimeD1StackStaticTable.program static
/-- The read-only template contains ONLY actual checker initialization words:
original binary N and the upstream physical descriptor index, raw empty. -/
def inputTemplate (bits indexWord : List Bool) : P.Stack→List Bool :=(P.initial bits [] indexWord).data
/-- The scope is an actual binary-ID vector; its arity is acquired by the real
record scanner rather than initialized as a cardinality/width/count answer. -/
def initial (bits indexWord bank : List Bool) : SemiprimeD1StackCalls.State Stack Label :=
  SemiprimeD1StackStaticTable.initial static (inputTemplate bits indexWord) bank
/-- One genuine finite machine fixed before ALL original N and descriptor values. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackStaticTable.machine static
/-- The raw-assignment slot in the input template is physically EMPTY. -/
theorem template_raw (bits indexWord : List Bool) : inputTemplate bits indexWord P.assignment=[] := rfl
/-- Supplying the actual physically reversed prefix reproduces exactly the
frozen original checker's input; no metadata/caches/verdict are added. -/
theorem template_raw_update (bits raw indexWord : List Bool) :
    Function.update (inputTemplate bits indexWord) P.assignment raw=(P.initial bits raw indexWord).data := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · rcases k with k|k
        · rfl
        · cases k;rfl
/-- Complete116-role inventory: checker52, read-only template52, counter7 and DFS5. -/
theorem stack_card : Fintype.card Stack=116 := by
  rw [SemiprimeD1StackStaticTable.stack_card,SemiprimeD1StackPublicInput.stack_card]
/-- Runtime state consists solely of finite Boolean and return-label flags. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackStaticTable.control_finite static
end RiemannGaussian.SemiprimeD1StackPublicInputTable
