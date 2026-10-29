/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNetworkRowsView
import RiemannGaussian.SemiprimeD1StackNetworkRowsEncoding
/-! # Actual dictionary copy/scan, singleton validation and returned-owner logging -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNetworkRowsLookup
open SemiprimeD1StackNetworkRows SemiprimeD1StackNetworkRowsPrimitives
open SemiprimeD1StackNetworkRowsView SemiprimeD1StackNetworkRowsEncoding
open SemiprimeD1StackProcedureTrace
open SemiprimeSourceHistogramKeyBits (frame)
local notation "ctl" => Label.local
/-- Parsed actual singleton owner word, with query retained and all14private fibre fields physically clear. -/
def owned (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences key owner:List Bool) :Stack→List Bool :=
  Function.update (keyed index reader ports rowHistory history factors occurrences key) (aux .owner) owner
/-- Actual preserving catalogue copy followed by the REAL14-role scan; singleton is a source-derived semantic fact. -/
theorem lookup_run (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences key owner:List Bool)
    (rows:List (List Bool×List Bool))
    (hd:index .output=SemiprimeD1StackOwnerFibre.records rows [])
    (hs:SemiprimeD1StackOwnerFibre.values key rows=[owner]) :
    ∃q≤ 5*(SemiprimeD1StackOwnerFibre.records rows []).length+SemiprimeD1StackOwnerFibreBounds.runBound key rows+5,
      Runs program q (ctl .copyDictionary) (keyed index reader ports rowHistory history factors occurrences key)
        (ctl .singletonTag) (returned index reader ports rowHistory history factors occurrences key owner) :=by
  have h0:=copy_call .dictionary .copyDictionary .lookup rfl
    (keyed index reader ports rowHistory history factors occurrences key) (SemiprimeD1StackOwnerFibre.records rows []) []
    hd rfl rfl
  simp only [List.append_nil] at h0
  obtain ⟨b,hb,h1⟩:=fibre_call
    (copied index reader ports rowHistory history factors occurrences key (SemiprimeD1StackOwnerFibre.records rows [])) key rows
    (fibre_initial index reader ports rowHistory history factors occurrences key (SemiprimeD1StackOwnerFibre.records rows []))
  rw [fibre_singleton index reader ports rowHistory history factors occurrences key owner rows hs] at h1
  refine ⟨(5*(SemiprimeD1StackOwnerFibre.records rows []).length+4)+b,by omega,join h0 h1⟩
/-- Consume the actual singleton TRUEtag/Field/truevalid/FALSEend/EOF, never a supplied owner answer. -/
theorem singleton_run (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences key owner:List Bool) :
    Runs program (8*owner.length+11) (ctl .singletonTag)
      (returned index reader ports rowHistory history factors occurrences key owner) (ctl .ownerFrame)
      (owned index reader ports rowHistory history factors occurrences key owner) :=by
  let b0:=returned index reader ports rowHistory history factors occurrences key owner
  let b1:=Function.update b0 (fibreStack (.inr .output)) (frame owner [false])
  let b2:=Function.update (Function.update (Function.update b1 (fibreStack (.inr .output)) [false]) (aux .owner) owner) (aux .valid) [true]
  let b3:=Function.update b2 (aux .valid) []
  let b4:=Function.update b3 (fibreStack (.inr .output)) []
  have h0:=pop_run .singletonTag (ctl .abort) (ctl .abort) (ctl .ownerField) (fibreStack (.inr .output)) b0
    (true::frame owner [false]) rfl rfl
  have h1:=field_call .owner .ownerField .ownerValid rfl b1 owner [false] (by rfl)
    (by rfl)
    (by rfl)
    (by rfl)
  have h2:=pop_run .ownerValid (ctl .abort) (ctl .abort) (ctl .singletonEnd) (aux .valid) b2 [true] rfl (by rfl)
  have h3:=pop_run .singletonEnd (ctl .abort) (ctl .singletonEOF) (ctl .abort) (fibreStack (.inr .output)) b3 [false] rfl
    (by rfl)
  have h4:=peek_run .singletonEOF (ctl .ownerFrame) (ctl .abort) (ctl .abort) (fibreStack (.inr .output)) b4 [] rfl (by rfl)
  have hh:=join (join (join (join h0 h1) h2) h3) h4
  have he:b4=owned index reader ports rowHistory history factors occurrences key owner:=by
    funext k
    rcases k with k|k
    · rfl
    · rcases k with k|k
      · rcases k with k|k
        · cases k <;> rfl
        · cases k <;> rfl
      · cases k <;> rfl
  change Runs program (1+(8*owner.length+7)+1+1+1) (ctl .singletonTag) b0 (ctl .ownerFrame) b4 at hh
  rw [he] at hh
  have hc:1+(8*owner.length+7)+1+1+1=8*owner.length+11:=by omega
  rw [hc] at hh
  exact hh
/-- Frame the ACTUALreturned binary owner, restore order and clear both query/value work before counting ONEport. -/
theorem emit_owner (index:I.Stack→List Bool) (reader ports rowHistory history factors occurrences key owner:List Bool) :
    Runs program (11*owner.length+key.length+16) (ctl .ownerFrame)
      (owned index reader ports rowHistory history factors occurrences key owner) (ctl .portLoop)
      (view index reader ports ((chunk owner).reverse++rowHistory) history factors (true::occurrences)) :=by
  let b0:=owned index reader ports rowHistory history factors occurrences key owner
  let b1:=Function.update b0 (aux .frameBuffer) (frame owner [])
  let b2:=Function.update b1 (aux .frameBuffer) (chunk owner)
  let b3:=Function.update (Function.update b2 (aux .frameBuffer) []) (aux .rowHistory) ((chunk owner).reverse++rowHistory)
  let b4:=Function.update b3 (aux .owner) []
  let b5:=Function.update b4 (aux .key) []
  have h0:=frame_call b0 owner [] rfl rfl rfl
  have h1:=push_run .ownerTag (ctl .ownerReverse) (aux .frameBuffer) true b1 rfl
  have he1:Function.update b1 (aux .frameBuffer) (true::b1 (aux .frameBuffer))=b2:=by
    simp only [b1,b2,Function.update_self,Function.update_idem,chunk]
  rw [he1] at h1
  have h2:=reverse_call .owner .ownerReverse .clearOwner rfl b2 (chunk owner) rowHistory
    (by rfl)
    (by rfl)
  have h3:=drain_loop .clearOwner (ctl .clearKey) (aux .owner) rfl b3 owner
    (by rfl)
  have h4:=drain_loop .clearKey (ctl .countOccurrence) (aux .key) rfl b4 key
    (by rfl)
  have h5:=push_run .countOccurrence (ctl .portLoop) (aux .occurrences) true b5 rfl
  have hh:=join (join (join (join (join h0 h1) h2) h3) h4) h5
  have he:Function.update b5 (aux .occurrences) (true::b5 (aux .occurrences))=
      view index reader ports ((chunk owner).reverse++rowHistory) history factors (true::occurrences):=by
    funext k
    rcases k with k|k
    · rfl
    · rcases k with k|k
      · rfl
      · cases k <;> rfl
  rw [he] at hh
  have hl:=chunk_length owner
  have hc:(6*owner.length+5)+1+(2*(chunk owner).length+3)+(owner.length+1)+(key.length+1)+1=
      11*owner.length+key.length+16:=by omega
  rw [hc] at hh
  exact hh
end RiemannGaussian.SemiprimeD1StackNetworkRowsLookup
