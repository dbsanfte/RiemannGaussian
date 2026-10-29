/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackCachePhaseLineage
/-! # Literal complete238-role cleanup inventory
These lists enumerate fixed physical ports before any input. No list, numeric
index or bank is stored in runtime control; clear labels below are finite.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackCachePhaseBankInventory
open SemiprimeD1StackCachePhase
/-- Static physical port enumeration, used only to generate finite cleanup code. -/
class Listing (K:Type) where
  /-- Complete literal finite port list, independent of every actual input. -/
  items:List K
  /-- Every physical port occurs in the static list. -/
  complete:∀k:K,k∈items
instance (n:Nat):Listing (Fin n):=⟨List.finRange n,by intro k;exact List.mem_finRange k⟩
instance:Listing Bool:=⟨[false,true],by intro k;cases k <;> simp⟩
instance:Listing Unit:=⟨[()],by intro k;cases k;simp⟩
instance {K L:Type} [Listing K] [Listing L]:Listing (K⊕L):=
  ⟨(Listing.items (K:=K)).map Sum.inl++(Listing.items (K:=L)).map Sum.inr,by
    intro k
    rcases k with k|k
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨k,Listing.complete k,rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨k,Listing.complete k,rfl⟩)⟩
instance adderListing:Listing SemiprimeD1StackAdder.Stack:=⟨SemiprimeD1StackRootPhaseParametersInventory.subtraction,by intro k;cases k <;> simp [SemiprimeD1StackRootPhaseParametersInventory.subtraction]⟩
instance geometryListing:Listing SemiprimeD1StackPhaseGeometry.Aux:=⟨SemiprimeD1StackRootPhaseParametersInventory.geometry,by intro k;cases k <;> simp [SemiprimeD1StackRootPhaseParametersInventory.geometry]⟩
instance guardListing:Listing SemiprimeD1StackPhaseGeometryGuard.Aux:=⟨SemiprimeD1StackRootPhaseParametersInventory.guards,by intro k;cases k <;> simp [SemiprimeD1StackRootPhaseParametersInventory.guards]⟩
instance divisionListing:Listing SemiprimeD1StackUnaryDivmod.Stack:=⟨SemiprimeD1StackRootPhaseParametersInventory.division,by intro k;cases k <;> simp [SemiprimeD1StackRootPhaseParametersInventory.division]⟩
instance metadataListing:Listing SemiprimeD1StackPhaseWorkingPrecisionMetadata.Aux:=⟨SemiprimeD1StackRootPhaseParametersInventory.metadata,by intro k;cases k <;> simp [SemiprimeD1StackRootPhaseParametersInventory.metadata]⟩
instance precisionListing:Listing SemiprimeD1StackPhaseWorkingPrecision.Aux:=⟨SemiprimeD1StackRootPhaseParametersInventory.binary,by intro k;cases k <;> simp [SemiprimeD1StackRootPhaseParametersInventory.binary]⟩
instance suffixListing:Listing SemiprimeD1StackJetSuffix.Stack:=⟨SemiprimeD1StackRootPhaseFreshRecordsInventory.suffixRoles,by intro k;cases k <;> simp [SemiprimeD1StackRootPhaseFreshRecordsInventory.suffixRoles]⟩
instance headerListing:Listing SemiprimeD1StackPhaseChildContext.Aux:=⟨SemiprimeD1StackRootPhaseFreshRecordsInventory.headerAux,by intro k;cases k <;> simp [SemiprimeD1StackRootPhaseFreshRecordsInventory.headerAux]⟩
instance freshListing:Listing SemiprimeD1StackPhaseChildContextFresh.Aux:=⟨SemiprimeD1StackRootPhaseFreshRecordsInventory.freshAux,by intro k;cases k <;> simp [SemiprimeD1StackRootPhaseFreshRecordsInventory.freshAux]⟩
instance heapListing:Listing SemiprimeD1StackHeapRead.Stack:=⟨SemiprimeD1StackRootPhaseFreshRecordsInventory.heapRoles,by intro k;cases k <;> simp [SemiprimeD1StackRootPhaseFreshRecordsInventory.heapRoles]⟩
instance routeListing:Listing SemiprimeD1StackJetRoute.Stack:=⟨[.axes,.reverseAxes,.axis,.radix,.product,.records,.scratch,.valid,.left,.right,.result,.q,.d,.copied,.divScratch,.quotLeft,.remLeft,.quotRight,.remRight],by intro k;cases k <;> simp ⟩
instance pointListing:Listing SemiprimeD1StackJetPoint.Aux:=⟨[.a,.b,.axes,.rank,.i,.j,.target,.acc,.reader,.index,.parser,.skipped,.valid,.readCopy,.eqRight,.eqValid,.eqScratch,.addWork,.copyWork],by intro k;cases k <;> simp ⟩
instance additionListing:Listing SemiprimeD1StackJetAdd.Aux:=⟨[.leftTape,.rightTape,.rank,.active,.reverseOut,.output,.valid,.parser,.copy],by intro k;cases k <;> simp ⟩
instance foldListing:Listing SemiprimeD1StackJetFold.Aux:=⟨[.children,.modes,.group,.frames,.fieldScratch,.valid,.copyScratch,.frameScratch,.precision,.tailSum,.sum],by intro k;cases k <;> simp ⟩
instance blocksListing:Listing SemiprimeD1StackJetBlocks.Aux:=⟨[.coefficients,.blocks,.todo,.reader,.rankTodo,.word,.fieldScratch,.valid,.copyScratch,.frameBuffer,.frameScratch,.rowHistory,.row,.logScratch,.history,.output],by intro k;cases k <;> simp ⟩
/-- All238 real component/shadow/cache/heap roles occur, in one fixed physical order. -/
def roles:List Stack:=Listing.items
/-- This list includes all238 allocated physical words. -/
theorem roles_length:roles.length=238:=by decide
/-- No physical tape is swept twice in the fixed inventory. -/
theorem roles_nodup:roles.Nodup:=by decide
/-- Every real component/shadow allocation is swept or explicitly retained. -/
theorem roles_complete:∀k:Stack,k∈roles:=Listing.complete
/-- Actual fixed physical port at each finite cleanup label. -/
def role (i:Fin 238):Stack:=roles[i.val]'(by rw [roles_length];exact i.isLt)
/-- Distinct cleanup labels refer to distinct actual tapes. -/
theorem role_injective:Function.Injective role:=by
  intro i j he
  apply Fin.ext
  exact roles_nodup.getElem_inj.mp he
/-- Every actual tape occurs at one finite cleanup label. -/
theorem role_complete (k:Stack):∃i:Fin 238,role i=k:=by
  obtain ⟨n,hn,he⟩:=List.mem_iff_getElem.mp (roles_complete k)
  exact ⟨⟨n,by rw [←roles_length];exact hn⟩,he⟩
end RiemannGaussian.SemiprimeD1StackCachePhaseBankInventory
