/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackFullFactorCatalogueOriginal
import RiemannGaussian.SemiprimeD1StackOwnerRecordsPrefixResources
import RiemannGaussian.SemiprimeD1StackReverseWord

/-! # Actual original-N complete root-network record acquisition
Both original record families are acquired by their real sources. The caller
physically copies the two output streams, removes the owner stream's sole
final marker, and joins OWNERS before FACTORS. All source caches are retained.
The standard front door supplies only N; a second entry accepts the actual
physical caller prefix/tail for later public-search composition.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackRootNetworkRecords
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace F
export SemiprimeD1StackFullFactorCatalogue (Stack Label program originalInput output input initial)
export SemiprimeD1StackFullFactorCatalogueExecution (done timeBound)
end F
namespace O
export SemiprimeD1StackOwnerRecords (Stack Label program originalInput output initial initialPrefix)
export SemiprimeD1StackOwnerRecordsExecution (done budget)
end O
/-- Original N/prefix caches, the actual two-stream join and restoring-copy work. -/
inductive Aux where
  | number | prefix | left | reverse | output | scratch
  deriving DecidableEq,Repr
instance : Fintype Aux where
  elems := {.number,.prefix,.left,.reverse,.output,.scratch}
  complete := by intro k;cases k <;> simp
/-- All1804 physical words, including both entire original source banks. -/
abbrev Stack := F.Stack ⊕ (O.Stack ⊕ Aux)
/-- Entire actual1454-role factor source. -/
def factorStack : F.Stack→Stack := Sum.inl
/-- Entire actual344-role owner source, with all caches retained. -/
def ownerStack (k:O.Stack) : Stack := .inr (.inl k)
/-- Six actual caller-word addresses, independent of N or any typed graph. -/
def aux (k:Aux) : Stack := .inr (.inr k)
/-- The sole original binary-N input. -/
def originalInput : Stack := aux .number
/-- Final original complete network records, owners first and factors second. -/
def output : Stack := aux .output
/-- Five literal preserving-copy sites, all determined before original N. -/
inductive Copy where | ownerNumber | prefix | factorNumber | factorOutput | ownerOutput
  deriving DecidableEq,Repr
instance : Fintype Copy where
  elems := {.ownerNumber,.prefix,.factorNumber,.factorOutput,.ownerOutput}
  complete := by intro k;cases k <;> simp
/-- Real copy source; no numerical/record getter enters the instruction table. -/
def copySource : Copy→Stack
  | .ownerNumber | .factorNumber=>originalInput
  | .prefix=>aux .prefix
  | .factorOutput=>factorStack F.output
  | .ownerOutput=>ownerStack O.output
/-- Real copy target, with both source-bank inputs physically acquired. -/
def copyTarget : Copy→Stack
  | .ownerNumber=>ownerStack O.originalInput
  | .prefix=>ownerStack (SemiprimeD1StackOwnerRecords.aux .prefixBytes)
  | .factorNumber=>factorStack F.originalInput
  | .factorOutput=>output
  | .ownerOutput=>aux .left
/-- Every copy uses an actual separate restoring scratch stack. -/
def copyStack (site:Copy) (k:Fin 3) : Stack :=
  if k=0 then copySource site else if k=1 then copyTarget site else aux .scratch
/-- The first real reversal exposes the owner terminator; the second joins its payload. -/
def reverseStack (second:Bool) (k:Fin 2) : Stack :=
  if k=0 then aux (if second then .reverse else .left)
  else aux (if second then .output else .reverse)
/-- Literal source, copy, marker-removal, join and halt phases. -/
inductive Control where
  | start | main | copyPrefix | owners | copyFactorNumber | factors
  | copyFactorOutput | copyOwnerOutput | reverseOwners | strip | append | done | abort
  deriving DecidableEq,Repr
instance : Fintype Control where
  elems := {.start,.main,.copyPrefix,.owners,.copyFactorNumber,.factors,.copyFactorOutput,
    .copyOwnerOutput,.reverseOwners,.strip,.append,.done,.abort}
  complete := by intro k;cases k <;> simp
/-- All labels and actual return symbols are fixed finite before N. -/
abbrev Label := Control ⊕ (F.Label ⊕ (O.Label ⊕ ((Copy×Fin 9) ⊕ (Bool×Fin 4))))
/-- Actual included factor-source label. -/
def factorLabel (pc:F.Label) : Label := .inr (.inl pc)
/-- Actual included owner-source label. -/
def ownerLabel (pc:O.Label) : Label := .inr (.inr (.inl pc))
/-- Actual included restoring-copy label. -/
def copyLabel (site:Copy) (pc:Fin 9) : Label := .inr (.inr (.inr (.inl (site,pc))))
/-- Actual included byte-reversal label. -/
def reverseLabel (second:Bool) (pc:Fin 4) : Label := .inr (.inr (.inr (.inr (second,pc))))
local notation "ctl" => (Sum.inl : Control→Label)
/-- One literal program acquires both full original families and joins their actual bytes. -/
def program : Label→C.Instruction Stack Label
  | .inl .start=>.base (.push (aux .prefix) false (ctl .main))
  | .inl .main=>.call (copyLabel .ownerNumber 0) (ctl .copyPrefix)
  | .inl .copyPrefix=>.call (copyLabel .prefix 0) (ctl .owners)
  | .inl .owners=>.call (ownerLabel (.local .main)) (ctl .copyFactorNumber)
  | .inl .copyFactorNumber=>.call (copyLabel .factorNumber 0) (ctl .factors)
  | .inl .factors=>.call (factorLabel (.local .main)) (ctl .copyFactorOutput)
  | .inl .copyFactorOutput=>.call (copyLabel .factorOutput 0) (ctl .copyOwnerOutput)
  | .inl .copyOwnerOutput=>.call (copyLabel .ownerOutput 0) (ctl .reverseOwners)
  | .inl .reverseOwners=>.call (reverseLabel false 0) (ctl .strip)
  | .inl .strip=>.base (.pop (aux .reverse) (ctl .abort) (ctl .append) (ctl .abort))
  | .inl .append=>.call (reverseLabel true 0) (ctl .done)
  | .inl .done|.inl .abort=>.base .halt
  | .inr (.inl pc)=>SemiprimeD1StackValidationLink.instruction factorStack factorLabel (F.program pc)
  | .inr (.inr (.inl pc))=>SemiprimeD1StackValidationLink.instruction ownerStack ownerLabel (O.program pc)
  | .inr (.inr (.inr (.inl (site,pc))))=>SemiprimeD1StackMultiplierLink.instruction
      (copyStack site) (copyLabel site) (SemiprimeD1StackCopy.code pc)
  | .inr (.inr (.inr (.inr (second,pc))))=>SemiprimeD1StackMultiplierLink.instruction
      (reverseStack second) (reverseLabel second) (SemiprimeD1StackReverseWord.code pc)
/-- Six-word actual caller store; all numerical values reside on Boolean tapes. -/
def words (number pre left reverse out scratch:List Bool) : Aux→List Bool
  | .number=>number | .prefix=>pre | .left=>left | .reverse=>reverse
  | .output=>out | .scratch=>scratch
/-- Complete retained factor/owner/caller physical payload. -/
def data (f:F.Stack→List Bool) (o:O.Stack→List Bool) (a:Aux→List Bool) : Stack→List Bool :=
  Sum.elim f (Sum.elim o a)
/-- Standard initialization has N alone; the program writes its own empty-prefix marker. -/
def input (bits:List Bool) : Stack→List Bool :=data (fun _=>[]) (fun _=>[]) (words bits [] [] [] [] [])
/-- Original-N-only whole entry. -/
def initial (bits:List Bool) : C.State Stack Label := ⟨some (ctl .start),none,none,input bits,[]⟩
/-- Actual caller-prefix entry, with no prepared source caches, tables or count. -/
def initialPrefix (bits pre:List Bool) : C.State Stack Label :=
  ⟨some (ctl .main),none,none,data (fun _=>[]) (fun _=>[]) (words bits pre [] [] [] []),[]⟩
/-- One genuine finite machine, before all inputs and all prescribed prefixes. -/
def machine : Turing.FinTM2 :=SemiprimeD1StackCalls.machine originalInput output (ctl .start) program
/-- Every included owner-source role remains distinct. -/
theorem owner_injective : Function.Injective ownerStack :=fun _ _ h=>Sum.inl.inj (Sum.inr.inj h)
/-- Every real copy source, target and scratch role is distinct. -/
theorem copy_injective (site:Copy) : Function.Injective (copyStack site) := by cases site <;> decide
/-- Both actual byte-reversal operands are distinct. -/
theorem reverse_injective (second:Bool) : Function.Injective (reverseStack second) := by cases second <;> decide
/-- All1804 roles, including both copied source N operands and all actual source shadows, are counted. -/
theorem stack_card : Fintype.card Stack=1804 := by
  rw [Fintype.card_sum,SemiprimeD1StackFullFactorCatalogue.stack_card,Fintype.card_sum,
    SemiprimeD1StackOwnerRecords.stack_card]
  decide
/-- Runtime state contains only finite Boolean and real-return-label flags. -/
theorem control_finite : Finite machine.σ :=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every real data and return alphabet is fixed finite before N. -/
theorem alphabets_finite : ∀k,Finite (machine.Γ k) :=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRootNetworkRecords
