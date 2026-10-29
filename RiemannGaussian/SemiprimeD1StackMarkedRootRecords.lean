/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRootNetworkRecordsOriginal
import RiemannGaussian.SemiprimeD1StackRootOwnerIndexCoordinates
import RiemannGaussian.SemiprimeD1StackMarkedPublicInputTableOriginal
/-! # Original-N marked root-record acquisition by physical byte patching
The real original record source runs once. Its retained factor stream is
synchronously parsed with a fresh actual descriptor catalogue. Only input
tables are reacquired by the actual144-role source; original owner/table bytes
are retained and rejoined by real copies and reversals. No graph, descriptor,
index, side, scope, table, coefficient, precision or clock is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackMarkedRootRecords
namespace C
export SemiprimeD1StackCalls (Instruction State run)
end C
namespace R
export SemiprimeD1StackRootNetworkRecords (Stack Label program input initial originalInput factorStack ownerStack aux)
end R
namespace V
export SemiprimeD1StackVertexCatalogue (Stack Label program originalInput kernelStack)
end V
namespace T
export SemiprimeD1StackMarkedPublicInputTable (Stack Label program roles)
end T
namespace G
export SemiprimeD1StackStaticWordTable (checker template counter aux)
end G
namespace M
export SemiprimeD1StackMarkedPublicInput (checker aux)
end M
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
namespace L
export SemiprimeD1StackVertexRecordStream (Stack Label code)
end L
/-- Ten actually allocated words; status is parser validity until final outcome. -/
inductive Aux where
  | recordReader | descriptorReader | tag | coord0 | coord2 | coord3
  | fieldScratch | status | history | output
  deriving DecidableEq, Repr
/-- Literal complete private physical inventory. -/
def auxRoles : List Aux :=
  [.recordReader,.descriptorReader,.tag,.coord0,.coord2,.coord3,.fieldScratch,.status,.history,.output]
/-- All private roles are fixed before the original input. -/
instance : Fintype Aux := Fintype.ofList auxRoles (by intro k;cases k <;> simp [auxRoles])
/-- Entire retained1804 bank, fresh53 catalogue, actual144 table source and ten private words. -/
abbrev Stack := R.Stack ⊕ (V.Stack ⊕ (T.Stack ⊕ Aux))
/-- Entire actual original record-source inclusion. -/
def root : R.Stack → Stack := Sum.inl
/-- Fresh actual descriptor catalogue inclusion. -/
def catalogue (k : V.Stack) : Stack := .inr (.inl k)
/-- Physically allocated table role, including the unused shared-N shadow. -/
def tablePrivate (k : T.Stack) : Stack := .inr (.inr (.inl k))
/-- One actual private word. -/
def aux (k : Aux) : Stack := .inr (.inr (.inr k))
/-- Sole original binary input, retained through all sources and patching. -/
def originalInput : Stack := root R.originalInput
/-- The table's readonly original-N role, never a numerical answer operand. -/
def tableNumber : T.Stack := G.template (M.checker (.inl SemiprimeD1StackPublicInputWidth.original))
/-- Readonly actual unary descriptor coordinate1, parsed directly into this role. -/
def tableIndex : T.Stack := G.template (M.checker SemiprimeD1StackPublicInput.index)
/-- Readonly physical side SINGLETON, acquired by actual pop/EOF checks. -/
def tableSide : T.Stack := G.template (M.aux .side)
/-- Only original N aliases the already retained actual source word. -/
def tableStack (k : T.Stack) : Stack :=
  if k=tableNumber then originalInput else tablePrivate k
/-- Original unary port vector is directly the real table scanner's input bank. -/
def ports : Stack := tableStack (G.counter .bank)
/-- Old parsed table is physically drained here before the actual new table call. -/
def table : Stack := tableStack (G.aux .output)
/-- Actually acquired arity markers, physically cleared before the next record. -/
def count : Stack := tableStack (G.counter .count)
/-- Parsed original unary input index. -/
def index : Stack := tableStack tableIndex
/-- Physically normalized side singleton. -/
def side : Stack := tableStack tableSide
/-- Four consecutive raw descriptor fields; coord1 uses the actual table index role. -/
def coordinate (i : Fin 5) : Stack :=
  if i=0 then aux .tag else if i=1 then aux .coord0 else if i=2 then index
  else if i=3 then aux .coord2 else aux .coord3
/-- Fresh actual catalogue output; a FLAT five-field stream with EMPTY EOF. -/
def catalogueOutput : Stack :=
  catalogue (V.kernelStack (SemiprimeD1StackCartesian4.aux 2))
/-- Retained actual factor-only stream, distinct from the old combined output. -/
def oldFactors : Stack := root (R.factorStack SemiprimeD1StackFullFactorCatalogue.output)
/-- Retained actual owner stream; no owner is reconstructed from factors. -/
def oldOwners : Stack := root (R.ownerStack SemiprimeD1StackOwnerRecords.output)
/-- Three actual old join work words, proven empty after the real root source. -/
def scratch : Stack := root (R.aux .scratch)
/-- Borrowed owner-copy buffer; restored EMPTY by actual reversal. -/
def ownerCopy : Stack := root (R.aux .left)
/-- Borrowed owner-reversal buffer; restored EMPTY after the actual join. -/
def ownerReverse : Stack := root (R.aux .reverse)
/-- Four fixed real copies; no runtime source selector is present. -/
inductive Copy where | factors | number | descriptors | owners deriving DecidableEq, Repr
/-- Literal fixed copy-site inventory. -/
instance : Fintype Copy := Fintype.ofList [.factors,.number,.descriptors,.owners] (by intro k;cases k <;> simp)
/-- Each copy reads an actual retained source word. -/
def copySource : Copy → Stack
  | .factors => oldFactors | .number => originalInput
  | .descriptors => catalogueOutput | .owners => oldOwners
/-- Each destination is physically empty before its actual copy. -/
def copyTarget : Copy → Stack
  | .factors => aux .recordReader | .number => catalogue V.originalInput
  | .descriptors => aux .descriptorReader | .owners => ownerCopy
/-- All restoring-copy scratch is actual borrowed empty root scratch. -/
def copyStack (what : Copy) (k : Fin 3) : Stack :=
  if k=0 then copySource what else if k=1 then copyTarget what else scratch
/-- Actual owner terminator exposure and then owner-first append to patched factors. -/
def reverseStack (join : Bool) (k : Fin 2) : Stack :=
  if k=0 then (if join then ownerReverse else ownerCopy)
  else if join then aux .output else ownerReverse
/-- Two record fields and all five raw descriptor fields, without a descriptor row tag. -/
inductive Field where | ports | table | tag | coord0 | coord1 | coord2 | coord3 deriving DecidableEq, Repr
/-- All seven physical parse sites. -/
def fields : List Field := [.ports,.table,.tag,.coord0,.coord1,.coord2,.coord3]
/-- Literal fixed parser-site enumeration. -/
instance : Fintype Field := Fintype.ofList fields (by intro k;cases k <;> simp [fields])
/-- Each parser reads only its actual record or descriptor stream. -/
def fieldReader : Field → Stack
  | .ports | .table => aux .recordReader
  | _ => aux .descriptorReader
/-- Each parser writes its actual shared field/cache destination. -/
def fieldTarget : Field → Stack
  | .ports => ports | .table => table | .tag => aux .tag | .coord0 => aux .coord0
  | .coord1 => index | .coord2 => aux .coord2 | .coord3 => aux .coord3
/-- Four distinct actual field roles, with a consumed physical validity singleton. -/
def fieldStack (what : Field) : F.Stack → Stack
  | .inl .input => fieldReader what
  | .inl .scratch => aux .fieldScratch
  | .inl .output => fieldTarget what
  | .inr _ => aux .status
/-- Logger directly consumes original ports and actual relayed/reacquired table. -/
def loggerStack : L.Stack → Stack
  | .ports => ports | .table => table | .history => aux .history | .output => aux .output
/-- Literal144-role abort inventory, including every unused alias shadow. -/
def tableRoles : List T.Stack :=
  T.roles.map G.checker++T.roles.map G.template++
  ([.bank,.reader,.count,.word,.fieldScratch,.valid,.copyScratch] :
    List SemiprimeD1StackDigitCount.Stack).map G.counter++
  ([.prefix,.work,.scratch,.reversed,.output] :
    List SemiprimeD1StackStaticWordTable.Aux).map G.aux
/-- All table roles are counted, not just the currently used parsed fields. -/
theorem tableRoles_length : tableRoles.length=144 := by decide
/-- Every table allocation occurs exactly once in the static clear inventory. -/
theorem tableRoles_nodup : tableRoles.Nodup := by decide
/-- Every real table/helper/shadow role is included. -/
theorem tableRoles_complete (k : T.Stack) : k∈tableRoles := by
  have he : tableRoles.toFinset=(Finset.univ : Finset T.Stack) := by decide
  exact List.mem_toFinset.mp (he.symm ▸ Finset.mem_univ k)
/-- Literal table slot for finite abort labels; no input-valued index is in control. -/
def tableRole (i : Fin 144) : T.Stack := tableRoles[i.val]'(by rw [tableRoles_length];exact i.isLt)
/-- Literal private slot for finite abort labels. -/
def auxRole (i : Fin 10) : Aux := auxRoles[i.val]'(by have h : auxRoles.length=10 := rfl;omega)
/-- Only actual borrowed old work words are cleared on abort. -/
def rootWork (i : Fin 3) : Stack := if i=0 then ownerCopy else if i=1 then ownerReverse else scratch
/-- Finite source/parse/branch/log/clear/join stages. -/
inductive Control where
  | start | ready | copyNumber | catalogue | copyDescriptors | initialize | rowTag
  | field (what : Field) | valid (what : Field)
  | caseTag | sideRead | sideEOF | sideFalse | sideTrue | clearOldTable | inputTable | log
  | clearField (part : Fin 5) | clearSide | clearCount | next
  | recordEOF | descriptorEOF | reverseFactors | copyOwners | reverseOwners | stripOwnerEnd | join | accept | done
  | abort | abortTable (i : Fin 145) | abortAux (i : Fin 11) | abortRoot (i : Fin 4) | reject
  deriving DecidableEq, Fintype, Repr
/-- All real source, parser, logger, copy and return labels are fixed before N. -/
abbrev Label := Control ⊕ (R.Label ⊕ (V.Label ⊕ (T.Label ⊕
  ((Copy × Fin 9) ⊕ ((Field × F.Label) ⊕ (L.Label ⊕ (Bool × Fin 4)))))))
/-- Literal local stage. -/
def ctl : Control → Label := Sum.inl
/-- Literal old root-source inclusion. -/
def rootLabel (k : R.Label) : Label := .inr (.inl k)
/-- Literal fresh descriptor-source inclusion. -/
def catalogueLabel (k : V.Label) : Label := .inr (.inr (.inl k))
/-- Literal whole marked input-table inclusion. -/
def tableLabel (k : T.Label) : Label := .inr (.inr (.inr (.inl k)))
/-- Literal preserving-copy inclusion. -/
def copyLabel (what : Copy) (k : Fin 9) : Label := .inr (.inr (.inr (.inr (.inl (what,k)))))
/-- Literal field-parser inclusion. -/
def fieldLabel (what : Field) (k : F.Label) : Label := .inr (.inr (.inr (.inr (.inr (.inl (what,k))))))
/-- Literal consuming-logger inclusion. -/
def loggerLabel (k : L.Label) : Label := .inr (.inr (.inr (.inr (.inr (.inr (.inl k))))))
/-- Literal owner-copy/join reversal inclusion. -/
def reverseLabel (join : Bool) (k : Fin 4) : Label := .inr (.inr (.inr (.inr (.inr (.inr (.inr (join,k)))))))
/-- Next actual parse call, or the actual physical tag branch. -/
def fieldNext : Field → Label
  | .ports => ctl (.field .table) | .table => ctl (.field .tag)
  | .tag => ctl (.field .coord0) | .coord0 => ctl (.field .coord1)
  | .coord1 => ctl (.field .coord2) | .coord2 => ctl (.field .coord3)
  | .coord3 => ctl .caseTag
/-- Next actual current-descriptor cleanup. -/
def clearNext (i : Fin 5) : Label :=
  if h:i.val<4 then ctl (.clearField ⟨i.val+1,by omega⟩) else ctl .clearSide
/-- One parameterless original-N program; every descriptor and coefficient is physically acquired. -/
def program : Label → C.Instruction Stack Label
  | .inl .start => .call (rootLabel (.inl .start)) (ctl .ready)
  | .inl .ready => .call (copyLabel .factors 0) (ctl .copyNumber)
  | .inl .copyNumber => .call (copyLabel .number 0) (ctl .catalogue)
  | .inl .catalogue => .call (catalogueLabel (.inl .main)) (ctl .copyDescriptors)
  | .inl .copyDescriptors => .call (copyLabel .descriptors 0) (ctl .initialize)
  | .inl .initialize => .call (loggerLabel .initialize) (ctl .rowTag)
  | .inl .rowTag => .base (.pop (aux .recordReader) (ctl .abort) (ctl .recordEOF) (ctl (.field .ports)))
  | .inl (.field what) => .call (fieldLabel what (F.active .tagPop (none,false))) (ctl (.valid what))
  | .inl (.valid what) => .base (.pop (aux .status) (ctl .abort) (ctl .abort) (fieldNext what))
  | .inl .caseTag => .base (.peek (aux .tag) (ctl .sideRead) (ctl .abort) (ctl .log))
  | .inl .sideRead => .base (.pop (aux .coord0) (ctl .sideFalse) (ctl .abort) (ctl .sideEOF))
  | .inl .sideEOF => .base (.peek (aux .coord0) (ctl .sideTrue) (ctl .abort) (ctl .abort))
  | .inl .sideFalse => .base (.push side false (ctl .clearOldTable))
  | .inl .sideTrue => .base (.push side true (ctl .clearOldTable))
  | .inl .clearOldTable => .base (.pop table (ctl .inputTable) (ctl .clearOldTable) (ctl .clearOldTable))
  | .inl .inputTable => .call (tableLabel .start) (ctl .log)
  | .inl .log => .call (loggerLabel .record) (ctl (.clearField 0))
  | .inl (.clearField part) => .base (.pop (coordinate part) (clearNext part)
      (ctl (.clearField part)) (ctl (.clearField part)))
  | .inl .clearSide => .base (.pop side (ctl .clearCount) (ctl .clearSide) (ctl .clearSide))
  | .inl .clearCount => .base (.pop count (ctl .next) (ctl .clearCount) (ctl .clearCount))
  | .inl .next => .base (.jump (ctl .rowTag))
  | .inl .recordEOF => .base (.peek (aux .recordReader) (ctl .descriptorEOF) (ctl .abort) (ctl .abort))
  | .inl .descriptorEOF => .base (.peek (aux .descriptorReader) (ctl .reverseFactors) (ctl .abort) (ctl .abort))
  | .inl .reverseFactors => .call (loggerLabel .reverse) (ctl .copyOwners)
  | .inl .copyOwners => .call (copyLabel .owners 0) (ctl .reverseOwners)
  | .inl .reverseOwners => .call (reverseLabel false 0) (ctl .stripOwnerEnd)
  | .inl .stripOwnerEnd => .base (.pop ownerReverse (ctl .abort) (ctl .join) (ctl .abort))
  | .inl .join => .call (reverseLabel true 0) (ctl .accept)
  | .inl .accept => .base (.push (aux .status) true (ctl .done))
  | .inl .done => .base .halt
  | .inl .abort => .base (.jump (ctl (.abortTable 0)))
  | .inl (.abortTable i) =>
      if h:i.val<144 then
        let k := tableRole ⟨i.val,h⟩
        let next := ctl (.abortTable ⟨i.val+1,by omega⟩)
        if k=tableNumber then .base (.jump next)
        else .base (.pop (tableStack k) next (ctl (.abortTable i)) (ctl (.abortTable i)))
      else .base (.jump (ctl (.abortAux 0)))
  | .inl (.abortAux i) =>
      if h:i.val<10 then
        .base (.pop (aux (auxRole ⟨i.val,h⟩)) (ctl (.abortAux ⟨i.val+1,by omega⟩))
          (ctl (.abortAux i)) (ctl (.abortAux i)))
      else .base (.jump (ctl (.abortRoot 0)))
  | .inl (.abortRoot i) =>
      if h:i.val<3 then
        .base (.pop (rootWork ⟨i.val,h⟩) (ctl (.abortRoot ⟨i.val+1,by omega⟩))
          (ctl (.abortRoot i)) (ctl (.abortRoot i)))
      else .base (.jump (ctl .reject))
  | .inl .reject => .base (.push (aux .status) false (ctl .done))
  | .inr (.inl k) => SemiprimeD1StackValidationLink.instruction root rootLabel (R.program k)
  | .inr (.inr (.inl k)) => SemiprimeD1StackValidationLink.instruction catalogue catalogueLabel (V.program k)
  | .inr (.inr (.inr (.inl k))) => SemiprimeD1StackValidationLink.instruction tableStack tableLabel (T.program k)
  | .inr (.inr (.inr (.inr (.inl (what,k))))) =>
      SemiprimeD1StackMultiplierLink.instruction (copyStack what) (copyLabel what) (SemiprimeD1StackCopy.code k)
  | .inr (.inr (.inr (.inr (.inr (.inl (what,k)))))) =>
      SemiprimeD1StackMultiplierLink.instruction (fieldStack what) (fieldLabel what) (F.code k)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inl k)))))) =>
      SemiprimeD1StackMultiplierLink.instruction loggerStack loggerLabel (L.code k)
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (join,k))))))) =>
      SemiprimeD1StackMultiplierLink.instruction (reverseStack join) (reverseLabel join) (SemiprimeD1StackReverseWord.code k)
/-- Only the actually shared original-N shadow is physically unused and always empty. -/
def privateTable (t : T.Stack → List Bool) (k : T.Stack) : List Bool :=
  if k=tableNumber then [] else t k
/-- Four complete fixed physical banks; these functions are finite tape views only. -/
def data (r : R.Stack → List Bool) (v : V.Stack → List Bool)
    (t : T.Stack → List Bool) (a : Aux → List Bool) : Stack → List Bool :=
  Sum.elim r (Sum.elim v (Sum.elim (privateTable t) a))
/-- Whole source initializes original binary N alone. -/
def input (bits : List Bool) : Stack → List Bool :=
  data (R.input bits) (fun _ => []) (fun _ => []) (fun _ => [])
/-- Real no-prescription original-input front door. -/
def initial (bits : List Bool) : C.State Stack Label :=
  ⟨some (ctl .start),none,none,input bits,[]⟩
/-- Genuine fixed finite machine; complete weighted records are its physical output. -/
def machine : Turing.FinTM2 := SemiprimeD1StackCalls.machine originalInput (aux .output) (ctl .start) program
/-- Static inverse for the one actual shared table input. -/
def tableInverse : Stack → T.Stack
  | .inl _ => tableNumber
  | .inr (.inr (.inl k)) => k
  | _ => tableNumber
/-- Actual table inclusion is injective despite sharing the retained N. -/
theorem table_inverse (k : T.Stack) : tableInverse (tableStack k)=k := by
  by_cases h:k=tableNumber
  · subst k;rfl
  · simp only [tableStack,h,ite_false,tablePrivate,tableInverse]
/-- All table source roles retain distinct physical images. -/
theorem table_injective : Function.Injective tableStack := by
  intro a b h
  have hh := congrArg tableInverse h
  simpa only [table_inverse] using hh
/-- Every copy uses three physically distinct words. -/
theorem copy_injective (what : Copy) : Function.Injective (copyStack what) := by cases what <;> decide
/-- Both real consuming reversals use distinct physical words. -/
theorem reverse_injective (join : Bool) : Function.Injective (reverseStack join) := by cases join <;> decide
/-- Every actual parser site has four distinct physical operands. -/
theorem field_injective (what : Field) : Function.Injective (fieldStack what) := by cases what <;> decide
/-- Every actual consuming logger operand is physically distinct. -/
theorem logger_injective : Function.Injective loggerStack := by decide
/-- Complete allocated2011 words, including the unused shared-N shadow and borrowed root work. -/
theorem stack_card : Fintype.card Stack=2011 := by
  rw [Fintype.card_sum,SemiprimeD1StackRootNetworkRecords.stack_card,Fintype.card_sum,
    SemiprimeD1StackVertexCatalogue.stack_card,Fintype.card_sum,SemiprimeD1StackMarkedPublicInputTable.stack_card]
  decide
/-- Runtime transient state contains only finite Boolean flags and fixed return labels. -/
theorem control_finite : Finite machine.σ := SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Every data and actual return alphabet is finite before N. -/
theorem alphabets_finite : ∀ k, Finite (machine.Γ k) := SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackMarkedRootRecords

