/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueOrders
/-! # Physical catalogue reversal and exact native mode-coordinate binding -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueFinish
open SemiprimeD1StackWeightedModeCatalogue SemiprimeD1StackWeightedModeCatalogueView
open SemiprimeD1StackWeightedModeCataloguePrimitives SemiprimeD1StackWeightedModeCatalogueOrders
open SemiprimeD1StackWeightedModeView (unary history vector)
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackProcedureTrace
local notation "ctl" => (Sum.inl :Control→Label)
/-- Exact actual catalogue weights, in order-major/slot-major sequence. -/
theorem weights_original (slots P:Nat):
    orderWeights slots 0 P=(SemiprimeD1ModeCatalog.weights slots P).map unary:=by
  rw [SemiprimeD1ModeCatalog.weights_eq]
  simp only [orderWeights,slotWeights,List.map_flatMap,List.map_replicate,Nat.zero_add]
/-- Exact actual finite labels, including the physical unary slot and order fields. -/
theorem labels_original (slots P:Nat):
    orderLabels slots 0 P=(SemiprimeD1ModeCatalog.catalog slots P).map (fun m=>modeWord m.slot m.order):=by
  simp only [orderLabels,slotLabels,SemiprimeD1ModeCatalog.catalog,List.map_flatMap,List.map_map,
    Function.comp_def,Nat.zero_add]
/-- The physical reverse source and target are always separate. -/
theorem reverse_ne (site:Bool):reverseStack site 0≠reverseStack site 1:=by cases site <;> decide
/-- Each actual output reversal includes the real call and return. -/
theorem reverse_call (site:Bool) (pc next:Control)
    (hc:program (ctl pc)=.call (reverseLabel site 0) (ctl next))
    (s:Stack→List Bool) (hist out:List Bool)
    (hh:s (reverseStack site 0)=hist) (ho:s (reverseStack site 1)=out):
    Runs program (2*hist.length+3) (ctl pc) s (ctl next)
      (Function.update (Function.update s (reverseStack site 0) []) (reverseStack site 1) (hist.reverse++out)):=by
  apply included_call program (reverseStack site) (reverseLabel site) (reverse_injective site)
    SemiprimeD1StackReverseWord.code 0 (fun _=>rfl) (ctl pc) (ctl next) hc (2*hist.length+2)
    (SemiprimeD1StackReverseWord.state none hist out) (SemiprimeD1StackReverseWord.done (hist.reverse++out)) s _
  · rfl
  · rfl
  · exact SemiprimeD1StackReverseWord.reverse_run hist out none
  · constructor
    · intro k;fin_cases k
      · exact hh
      · exact ho
    · intro k _;rfl
  · constructor
    · intro k;fin_cases k
      · change Function.update (Function.update s (reverseStack site 0) []) (reverseStack site 1)
          (hist.reverse++out) (reverseStack site 0)=[]
        rw [Function.update_of_ne (reverse_ne site),Function.update_self]
      · exact Function.update_self _ _ _
    · intro k hk
      rw [Function.update_of_ne (hk 1).symm,Function.update_of_ne (hk 0).symm]
/-- Proof-side name for the actual generated weight catalogue. -/
def weights (p t width:Nat):List Nat:=SemiprimeD1ModeCatalog.weights (p*t) (width-1)
/-- Proof-side name for the actual generated full mode-label bytes. -/
def labels (p t width:Nat):List Bool:=
  vectorBits ((SemiprimeD1ModeCatalog.catalog (p*t) (width-1)).map (fun m=>modeWord m.slot m.order))
/-- The physically reached prepared DFS input, retaining all computed metadata. -/
def ready (p t width:Nat):Words:=
  {scanning p t width 0 (width-1) 0 0 [] [] with
    enumData:=W.input (vector (weights p t width)) (unary width),labels:=labels p t width}
/-- Both actual logs are reversed to their exact literal native catalogue bytes. -/
theorem finish_run (p t width:Nat):
    Runs program
      (2*(history (orderWeights (p*t) 0 (width-1)) []).length+
        2*(history (orderLabels (p*t) 0 (width-1)) []).length+8)
      (ctl .catalogueSeed)
      (store (scanning p t width 0 (width-1) 0 0
        (history (orderWeights (p*t) 0 (width-1)) []) (history (orderLabels (p*t) 0 (width-1)) [])))
      (ctl .enumerate) (store (ready p t width)):=by
  let wh:=history (orderWeights (p*t) 0 (width-1)) []
  let lh:=history (orderLabels (p*t) 0 (width-1)) []
  let a:=scanning p t width 0 (width-1) 0 0 wh lh
  let b:=write a (weighted .catalogue) [false]
  let c:=write (write b (aux .weightHistory) []) (weighted .catalogue) (vectorBits (orderWeights (p*t) 0 (width-1)))
  let d:Words:={c with labels:=[false]}
  have h0:=push_run .catalogueSeed .reverseWeights (weighted .catalogue) false (store a) rfl
  rw [store_write] at h0
  change Runs program 1 _ _ _ (store b) at h0
  have h1:=reverse_call true .reverseWeights .labelsSeed rfl (store b) wh [false] rfl rfl
  rw [store_write,store_write,SemiprimeD1StackWeightedModeExecution.history_vector] at h1
  change Runs program (2*wh.length+3) _ _ _ (store c) at h1
  have h2:=push_run .labelsSeed .reverseLabels (aux .labels) false (store c) rfl
  rw [store_write] at h2
  change Runs program 1 _ _ _ (store d) at h2
  have h3:=reverse_call false .reverseLabels .enumerate rfl (store d) lh [false] rfl rfl
  rw [store_write,store_write,SemiprimeD1StackWeightedModeExecution.history_vector,
    labels_original] at h3
  have hdata:write (write d (reverseStack false 0) []) (reverseStack false 1)
      (vectorBits ((SemiprimeD1ModeCatalog.catalog (p*t) (width-1)).map (fun m=>modeWord m.slot m.order)))=
      ready p t width:=by
    change {ready p t width with enumData:=c.enumData}=ready p t width
    have he:c.enumData=(ready p t width).enumData:=by
      funext k
      cases k <;> first
        | rfl
        | (change vectorBits (orderWeights (p*t) 0 (width-1))=vector (weights p t width)
           rw [weights_original]
           rfl)
    rw [he]
  rw [hdata] at h3
  have h:=join h0 (join h1 (join h2 h3))
  dsimp only [wh,lh] at h
  convert h using 1;omega
end RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueFinish
