/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackOwnerCatalogue
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32000
set_option synthInstance.maxSize 131072
namespace RiemannGaussian.SemiprimeD1StackOwnerCatalogueSource
open SemiprimeD1StackOwnerCatalogue
open SemiprimeD1StackProcedureTrace (Runs included_call runs_trans)
namespace Rel
export SemiprimeD1StackMultiplierLink (DataRel)
end Rel
/-- Exact literal physical source, recipe work, parsed fields and private outer work store. -/
def data (s:S.Stack→List Bool) (w:RecipeWork→List Bool) (f:Fin 7→List Bool) (a:Aux→List Bool) : Stack→List Bool :=
  Sum.elim s (Sum.elim w (Sum.elim f a))
/-- The actual original-N source plus fresh recipe/field work and two private readers. -/
def clean (s:S.Stack→List Bool) (edges ids:List Bool) : Stack→List Bool :=
  data s (fun _=>[]) (fun _=>[]) (fun k=>match k with | .readerEdges=>edges | .readerIds=>ids | _=>[])
/-- Source stack inclusion never aliases an outer reader, parsed field or recipe role. -/
theorem source_injective : Function.Injective source := Sum.inl_injective
/-- Both real preserving Copy calls have three distinct data roles. -/
theorem copy_injective : ∀ids:Bool,Function.Injective (copyStack ids) := by decide
/-- Literal original binary-N initial data; every new cache/reader is empty. -/
theorem input_clean (bits:List Bool) : input bits=clean (S.input bits) [] [] := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
/-- Exact physical update of the private edge reader. -/
theorem clean_edges (s:S.Stack→List Bool) (edges ids next:List Bool) :
    Function.update (clean s edges ids) (aux .readerEdges) next=clean s next ids := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> simp [clean,data,aux,Function.update]
/-- Exact physical update of the private M-ID bank reader. -/
theorem clean_ids (s:S.Stack→List Bool) (edges ids next:List Bool) :
    Function.update (clean s edges ids) (aux .readerIds) next=clean s edges next := by
  funext k
  rcases k with k|k
  · rfl
  · rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> simp [clean,data,aux,Function.update]
/-- Actual original Edge13/count/M-bank source runs once inside the catalogue producer. -/
theorem original_acquisition (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits) :
    ∃time≤SemiprimeD1StackRootScopeBankExecution.budget bits+1,
      Runs program time (.local .main) (input bits) (.local .copyEdges)
        (clean (SemiprimeD1StackRootScopeBankExecution.result bits) [] []) := by
  obtain ⟨time,ht,hr⟩:=SemiprimeD1StackRootScopeBankExecution.source_run bits hc hN
  refine ⟨time+1,Nat.add_le_add_right ht 1,?_⟩
  apply SemiprimeD1StackProcedureInclusion.included_call program source Label.source source_injective
    S.program (.inl .start) (fun _=>rfl) (.local .main) (.local .copyEdges) rfl time
    (SemiprimeD1StackRootScopeBank.initial bits) (SemiprimeD1StackRootScopeBankExecution.done bits)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;rfl
    · intro k _;rfl
  · constructor
    · intro k;rfl
    · intro k hk
      rcases k with k|k
      · exact (hk k rfl).elim
      · rcases k with k|k
        · rfl
        · rcases k with k|k
          · rfl
          · cases k <;> rfl
/-- Real preserving Copy on the already-acquired source; no advised reader bytes. -/
theorem copy_call (ids:Bool) (store:Stack→List Bool) (pc next:Label)
    (hs:store (aux .copyScratch)=[]) (hc:program pc=.call (.copy ids 0) next) :
    Runs program (5*(store (if ids then idBank else edgeTape)).length+4) pc store next
      (Function.update store (if ids then aux .readerIds else aux .readerEdges)
        (store (if ids then idBank else edgeTape)++store (if ids then aux .readerIds else aux .readerEdges))) := by
  let x:=store (if ids then idBank else edgeTape)
  let y:=store (if ids then aux .readerIds else aux .readerEdges)
  let before:=SemiprimeD1StackCopy.state 0 none x y []
  let after:=SemiprimeD1StackCopy.done x (x++y)
  have hi:Rel.DataRel (copyStack ids) store before.store store:=by
    constructor
    · intro k;fin_cases k <;> simp [before,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,copyStack,x,y,hs]
    · intro k _;rfl
  apply included_call program (copyStack ids) (Label.copy ids) (copy_injective ids)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc _ before after
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words x y none
  · exact hi
  · have he:Function.update before.store (1:Fin 3) (x++y)=after.store:=by
      funext k;fin_cases k <;> rfl
    simpa only [he,copyStack,show ¬(1:Fin 3)=0 by decide,ite_false,ite_true] using
      SemiprimeD1StackPortOwnerRecipeCalls.update_rel (copyStack ids) (copy_injective ids) store before.store store hi 1 (x++y)
/-- Actual source tape bytes, not an edge-record supplier or native enumeration input. -/
def edges (bits:List Bool) : List Bool :=
  SemiprimeD1StackRootScopeBankExecution.result bits (S.edgeStack (SemiprimeD1StackEdgeCatalogue.aux .output))
/-- Actual physically generated padded M-ID bank bytes, retained separately from E wire count. -/
def ids (bits:List Bool) : List Bool := SemiprimeD1StackRootScopeBankExecution.result bits S.ids
/-- Exact reached parsing state after original acquisition and the two actual reader copies. -/
def ready (bits:List Bool) : Stack→List Bool :=
  clean (SemiprimeD1StackRootScopeBankExecution.result bits) (edges bits) (ids bits)
/-- Literal whole acquisition prefix clock, charging original source and BOTH physical copies. -/
def budget (bits:List Bool) : ℕ :=
  SemiprimeD1StackRootScopeBankExecution.budget bits+5*(edges bits).length+5*(ids bits).length+9
/-- Closed original-binary-N acquisition prefix: no r/t/digits/E/M/edge/ID advice is an operand. -/
theorem acquisition_run (bits:List Bool) (hc:SemiprimeSourceCompactBits.Compact bits)
    (hN:0<SemiprimeBitArithmetic.bitValue bits) :
    ∃time≤budget bits,Runs program time (.local .main) (input bits) (.local .parse) (ready bits) := by
  obtain ⟨time,ht,hr⟩:=original_acquisition bits hc hN
  let s:=SemiprimeD1StackRootScopeBankExecution.result bits
  have he:=copy_call false (clean s [] []) (.local .copyEdges) (.local .copyIds) rfl rfl
  have hi:=copy_call true (clean s (edges bits) []) (.local .copyIds) (.local .parse) rfl rfl
  change Runs program (5*(edges bits).length+4) (.local .copyEdges) (clean s [] []) (.local .copyIds)
    (Function.update (clean s [] []) (aux .readerEdges) (edges bits++[])) at he
  rw [List.append_nil,clean_edges] at he
  change Runs program (5*(ids bits).length+4) (.local .copyIds) (clean s (edges bits) []) (.local .parse)
    (Function.update (clean s (edges bits) []) (aux .readerIds) (ids bits++[])) at hi
  rw [List.append_nil,clean_ids] at hi
  have h:=runs_trans program _ _ _ _ _ _ _ _ hr (runs_trans program _ _ _ _ _ _ _ _ he hi)
  exact ⟨time+((5*(edges bits).length+4)+(5*(ids bits).length+4)),by unfold budget;omega,h⟩
end RiemannGaussian.SemiprimeD1StackOwnerCatalogueSource
