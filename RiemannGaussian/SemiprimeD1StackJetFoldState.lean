/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackJetFoldWords
/-! # Exact live-word views for the actual111-role ordered fold
Only fourteen words can be live at a real-call boundary. Every other allocated
private/shadow role is empty there; it is still counted in every prefix bound.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackJetFoldState
open SemiprimeD1StackJetFold
/-- Literal live roles; this finite proof tuple is not accepted by the executing source. -/
inductive Slot where
  | axes | precision | children | rank | width | modes | group | frames | left | product | result | tailSum | sum | valid
  deriving DecidableEq,Repr
instance :Fintype Slot where
  elems:={.axes,.precision,.children,.rank,.width,.modes,.group,.frames,.left,.product,.result,.tailSum,.sum,.valid}
  complete:=by intro k;cases k <;> simp
/-- Every named word has its literal actual source address. -/
def address:Slot→Stack
  | .axes=>axes | .precision=>aux .precision | .children=>aux .children | .rank=>rank | .width=>width
  | .modes=>aux .modes | .group=>aux .group | .frames=>aux .frames | .left=>left | .product=>product
  | .result=>mulOutput | .tailSum=>aux .tailSum | .sum=>output | .valid=>aux .valid
/-- The fourteen live roles occupy distinct actual Boolean stacks. -/
theorem address_injective:Function.Injective address:=by decide
/-- Proof notation for the fourteen physical live words, independent of all numerical values. -/
abbrev Values:=Slot→List Bool
/-- Literal whole store at an actual procedure boundary; all unlisted real roles are empty. -/
def data (v:Values) (k:Stack):List Bool:=
  if k=address .axes then v .axes else if k=address .precision then v .precision else
  if k=address .children then v .children else if k=address .rank then v .rank else
  if k=address .width then v .width else if k=address .modes then v .modes else
  if k=address .group then v .group else if k=address .frames then v .frames else
  if k=address .left then v .left else if k=address .product then v .product else
  if k=address .result then v .result else if k=address .tailSum then v .tailSum else
  if k=address .sum then v .sum else if k=address .valid then v .valid else []
/-- Every declared actual live word has exactly its specified physical bytes. -/
theorem data_get (v:Values) (s:Slot):data v (address s)=v s:=by
  cases s <;> simp [data,address_injective.eq_iff]
/-- Every private operator word and every allocated unused shadow is explicitly empty at a boundary. -/
theorem data_other (v:Values) (k:Stack) (hk:∀s,k≠address s):data v k=[]:=by
  simp [data,hk]
/-- A live-word update is precisely an actual source-store function update. -/
theorem data_update (v:Values) (s:Slot) (word:List Bool):
    data (Function.update v s word)=Function.update (data v) (address s) word:=by
  funext k
  by_cases hex:∃t,k=address t
  · obtain ⟨t,rfl⟩:=hex
    rw [data_get]
    by_cases he:t=s
    · subst t;simp
    · have hn:address t≠address s:=fun h=>he (address_injective h)
      simp only [Function.update_of_ne he,Function.update_of_ne hn,data_get]
  · have hk:∀s,k≠address s:=by simpa only [not_exists] using hex
    rw [data_other _ _ hk,Function.update_of_ne (hk s),data_other _ _ hk]
/-- Exact literal live words used to describe every source/recursive boundary. -/
def values (axes precision children rank width modes group frames left product result tailSum sum valid:List Bool):Values
  | .axes=>axes | .precision=>precision | .children=>children | .rank=>rank | .width=>width
  | .modes=>modes | .group=>group | .frames=>frames | .left=>left | .product=>product
  | .result=>result | .tailSum=>tailSum | .sum=>sum | .valid=>valid
/-- The physical full source initially contains only its three actual original input tapes. -/
theorem initial_data (axisTape precision children:List Bool):
    (initial axisTape precision children).data=
      data (values axisTape precision children [] [] [] [] [] [] [] [] [] [] []):=by
  funext k
  by_cases hex:∃s,k=address s
  · obtain ⟨s,rfl⟩:=hex
    rw [data_get]
    cases s <;> rfl
  · have hk:∀s,k≠address s:=by simpa only [not_exists] using hex
    rw [data_other _ _ hk]
    have ha:k≠axes:=hk .axes
    have hp:k≠aux .precision:=hk .precision
    have hc:k≠aux .children:=hk .children
    simp only [initial,input,Function.update_of_ne ha,Function.update_of_ne hp,Function.update_of_ne hc]
/-- The real preserving-copy scratch is never one of the fourteen live roles. -/
theorem copy_scratch_empty (v:Values):data v (aux .copyScratch)=[]:=by
  apply data_other
  intro s;cases s <;> decide
/-- The real frame scratch is never one of the fourteen live roles. -/
theorem frame_scratch_empty (v:Values):data v (aux .frameScratch)=[]:=by
  apply data_other
  intro s;cases s <;> decide
/-- The real field-parser scratch is never one of the fourteen live roles. -/
theorem field_scratch_empty (v:Values):data v (aux .fieldScratch)=[]:=by
  apply data_other
  intro s;cases s <;> decide
end RiemannGaussian.SemiprimeD1StackJetFoldState
