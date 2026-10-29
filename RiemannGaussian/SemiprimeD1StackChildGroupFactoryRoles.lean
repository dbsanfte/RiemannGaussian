/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerLookupBounds
import RiemannGaussian.SemiprimeD1StackPacketRowsOriginal
import RiemannGaussian.SemiprimeD1StackAdderExecution
import RiemannGaussian.SemiprimeD1StackWordEqualExecution
import RiemannGaussian.SemiprimeD1StackPortOrdinalStreamOriginal
import RiemannGaussian.SemiprimeD1StackProcedureCallsTrace
/-! # Fixed complete child-factory physical inventory
All inputs are actual cache/header words. Colour index is unary; the distinct
NEW jet-axis header is carried unchanged. Neither old nor new precision is fixed.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace L
export SemiprimeD1StackOwnerLookup (Stack Label program)
end L
namespace R
export SemiprimeD1StackPacketRows (Stack Label program)
end R
namespace A
export SemiprimeD1StackAdder (Stack Label code)
end A
namespace E
export SemiprimeD1StackWordEqual (Label code)
end E
namespace F
export SemiprimeD1TensorTapeFieldBytecode (Stack Label code active)
end F
namespace O
export SemiprimeD1StackPortOrdinalStream (Stack Label program)
end O
/-- All65 real input/output/parser/logger/search words, fixed before inputs. -/
inductive Aux where
  | environment
  | catalogue
  | owners
  | factors
  | occurrences
  | placements
  | packets
  | colourIndex
  | group
  | oldAxes
  | oldPrecision
  | jetAxis
  | newPrecision
  | activation
  | activationMap
  | endpoints
  | oldEndpoints
  | buckets
  | leftPorts
  | orders
  | output
  | vertexTodo
  | vertexKey
  | selectedID
  | jointKey
  | pairReader
  | placementReader
  | packetReader
  | endpointReader
  | oldReader
  | childReader
  | outerReader
  | ownerKey
  | factorKey
  | sourceKey
  | paddingKey
  | packetKey
  | slotWord
  | edgeWord
  | sideWord
  | validWord
  | colourReader
  | colourCursor
  | colourWord
  | activationHistory
  | endpointHistory
  | oldHistory
  | bucketHistory
  | factorHistory
  | portHistory
  | orderHistory
  | vertexHistory
  | tagWord
  | candidateTag
  | localPosition
  | globalPosition
  | answerPosition
  | frameBuffer
  | rowBuffer
  | copyScratch
  | sentinelScratch
  | flagScratch
  | success
  | orderBank
  | portBank
  deriving DecidableEq,Repr
/-- Literal complete auxiliary role enumeration. -/
instance auxFintype:Fintype Aux:=Fintype.ofList
  [.environment,.catalogue,.owners,.factors,.occurrences,.placements,.packets,.colourIndex,.group,.oldAxes,.oldPrecision,.jetAxis,.newPrecision,.activation,.activationMap,.endpoints,.oldEndpoints,.buckets,.leftPorts,.orders,.output,.vertexTodo,.vertexKey,.selectedID,.jointKey,.pairReader,.placementReader,.packetReader,.endpointReader,.oldReader,.childReader,.outerReader,.ownerKey,.factorKey,.sourceKey,.paddingKey,.packetKey,.slotWord,.edgeWord,.sideWord,.validWord,.colourReader,.colourCursor,.colourWord,.activationHistory,.endpointHistory,.oldHistory,.bucketHistory,.factorHistory,.portHistory,.orderHistory,.vertexHistory,.tagWord,.candidateTag,.localPosition,.globalPosition,.answerPosition,.frameBuffer,.rowBuffer,.copyScratch,.sentinelScratch,.flagScratch,.success,.orderBank,.portBank] (by intro k;cases k <;> simp)
/-- All115 allocations, including every unaliased callee source shadow. -/
abbrev Stack:=L.Stack⊕(R.Stack⊕(A.Stack⊕(F.Stack⊕(O.Stack⊕Aux))))
/-- Real11-word numeric lookup bank. -/
def lookup:L.Stack→Stack:=Sum.inl
/-- Whole19-word real paired colour-row reader bank. -/
def rows:R.Stack→Stack:=fun k=>.inr (.inl k)
/-- Actual shared full-adder/numeric-equality four-word bank. -/
def arithmetic:A.Stack→Stack:=fun k=>.inr (.inr (.inl k))
/-- Full four-field-parser allocation; redirected inputs/outputs leave counted shadows. -/
def field:F.Stack→Stack:=fun k=>.inr (.inr (.inr (.inl k)))
/-- All12 real binary-ordinal to unary-selector words. -/
def ordinal:O.Stack→Stack:=fun k=>.inr (.inr (.inr (.inr (.inl k))))
/-- Fixed actual auxiliary address. -/
def aux:Aux→Stack:=fun k=>.inr (.inr (.inr (.inr (.inr k))))
/-- Exactly thirteen physical acquired words are immutable source operands. -/
def inputRole:Aux→Bool
  | .environment=>true
  | .catalogue=>true
  | .owners=>true
  | .factors=>true
  | .occurrences=>true
  | .placements=>true
  | .packets=>true
  | .colourIndex=>true
  | .group=>true
  | .oldAxes=>true
  | .oldPrecision=>true
  | .jetAxis=>true
  | .newPrecision=>true
  | _=>false
/-- Eight actual acquired graph outputs survive successful cleanup. -/
def outputRole:Aux→Bool
  | .activation=>true
  | .activationMap=>true
  | .endpoints=>true
  | .oldEndpoints=>true
  | .buckets=>true
  | .leftPorts=>true
  | .orders=>true
  | .output=>true
  | _=>false
/-- Cleanup retention is a finite physical-port decision, never a data test. -/
def retained (aborted:Bool):Stack→Bool
  | .inr (.inr (.inr (.inr (.inr k))))=>inputRole k || (!aborted && outputRole k)
  | _=>false
/-- Complete static local lookup inventory. -/
def lookupRoles:List L.Stack:=[.inl .left,.inl .right,.inl .scratch,.inl .output,.inr .query,.inr .reader,.inr .fieldScratch,.inr .valid,.inr .copyScratch,.inr .discard,.inr .output]
/-- Complete static local rows inventory. -/
def rowsRoles:List R.Stack:=[.inl (.inl .left),.inl (.inl .right),.inl (.inl .scratch),.inl (.inl .output),.inl (.inr .query),.inl (.inr .reader),.inl (.inr .fieldScratch),.inl (.inr .valid),.inl (.inr .copyScratch),.inl (.inr .discard),.inl (.inr .output),.inr .key,.inr .catalogue,.inr .keyReader,.inr .leftBytes,.inr .leftHistory,.inr .rightHistory,.inr .leftOutput,.inr .rightOutput]
/-- Complete static local arithmetic inventory. -/
def arithmeticRoles:List A.Stack:=[.left,.right,.scratch,.output]
/-- Complete static local field inventory. -/
def fieldRoles:List F.Stack:=[.inl .input,.inl .scratch,.inl .output,.inr ()]
/-- Complete static local ordinal inventory. -/
def ordinalRoles:List O.Stack:=[.bank,.reader,.word,.fieldScratch,.valid,.copyScratch,.digits,.unaryScratch,.unary,.logScratch,.history,.output]
/-- Complete static local aux inventory. -/
def auxRoles:List Aux:=[.environment,.catalogue,.owners,.factors,.occurrences,.placements,.packets,.colourIndex,.group,.oldAxes,.oldPrecision,.jetAxis,.newPrecision,.activation,.activationMap,.endpoints,.oldEndpoints,.buckets,.leftPorts,.orders,.output,.vertexTodo,.vertexKey,.selectedID,.jointKey,.pairReader,.placementReader,.packetReader,.endpointReader,.oldReader,.childReader,.outerReader,.ownerKey,.factorKey,.sourceKey,.paddingKey,.packetKey,.slotWord,.edgeWord,.sideWord,.validWord,.colourReader,.colourCursor,.colourWord,.activationHistory,.endpointHistory,.oldHistory,.bucketHistory,.factorHistory,.portHistory,.orderHistory,.vertexHistory,.tagWord,.candidateTag,.localPosition,.globalPosition,.answerPosition,.frameBuffer,.rowBuffer,.copyScratch,.sentinelScratch,.flagScratch,.success,.orderBank,.portBank]
/-- Every lookup allocation occurs in its local list. -/
theorem lookup_complete:∀k:L.Stack,k∈lookupRoles:=by
  rintro (k|k) <;> cases k <;> simp [lookupRoles]
/-- Every reader allocation occurs in its local list. -/
theorem rows_complete:∀k:R.Stack,k∈rowsRoles:=by
  rintro ((k|k)|k) <;> cases k <;> simp [rowsRoles]
/-- Every arithmetic allocation occurs in its local list. -/
theorem arithmetic_complete:∀k:A.Stack,k∈arithmeticRoles:=by intro k;cases k <;> simp [arithmeticRoles]
/-- Every parser allocation occurs in its local list. -/
theorem field_complete:∀k:F.Stack,k∈fieldRoles:=by rintro (k|k) <;> cases k <;> simp [fieldRoles]
/-- Every converter allocation occurs in its local list. -/
theorem ordinal_complete:∀k:O.Stack,k∈ordinalRoles:=by intro k;cases k <;> simp [ordinalRoles]
/-- Every auxiliary allocation occurs in its local list. -/
theorem aux_complete:∀k:Aux,k∈auxRoles:=by intro k;cases k <;> simp [auxRoles]
/-- Entire literal115-port order used by actual cleanup labels. -/
def roles:List Stack:=lookupRoles.map lookup++(rowsRoles.map rows++(arithmeticRoles.map arithmetic++
  (fieldRoles.map field++(ordinalRoles.map ordinal++auxRoles.map aux))))
/-- Every physical allocation is counted. -/
theorem roles_length:roles.length=115:=by decide
/-- No physical allocation is duplicated. -/
theorem roles_nodup:roles.Nodup:=by decide
/-- Every physical allocation is covered by the fixed cleanup order. -/
theorem roles_complete:∀k:Stack,k∈roles:=by
  intro k
  rcases k with k|k|k|k|k|k
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨k,lookup_complete k,rfl⟩)
  · apply List.mem_append_right
    exact List.mem_append_left _ (List.mem_map.mpr ⟨k,rows_complete k,rfl⟩)
  · apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_append_left _ (List.mem_map.mpr ⟨k,arithmetic_complete k,rfl⟩)
  · apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_append_left _ (List.mem_map.mpr ⟨k,field_complete k,rfl⟩)
  · apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_append_left _ (List.mem_map.mpr ⟨k,ordinal_complete k,rfl⟩)
  · apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨k,aux_complete k,rfl⟩
/-- The actual physical role at one bounded cleanup label. -/
def role (i:Fin 115):Stack:=roles[i.val]'(by rw [roles_length];exact i.isLt)
/-- Distinct cleanup labels visit distinct physical words. -/
theorem role_injective:Function.Injective role:=by
  intro i j h;apply Fin.ext;exact roles_nodup.getElem_inj.mp h
/-- Every physical word is visited by some cleanup label. -/
theorem role_complete (k:Stack):∃i:Fin 115,role i=k:=by
  obtain ⟨n,hn,he⟩:=List.mem_iff_getElem.mp (roles_complete k)
  exact ⟨⟨n,by rw [←roles_length];exact hn⟩,he⟩
/-- All115 physical allocations are counted without dropping source shadows. -/
theorem stack_card:Fintype.card Stack=115:=by decide
end RiemannGaussian.SemiprimeD1StackChildGroupFactoryRoles
