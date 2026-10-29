/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackWeightedModeCatalogue
/-! # Exact physical metadata catalogue word views -/
set_option autoImplicit false
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueView
open SemiprimeD1StackWeightedModeCatalogue
open SemiprimeD1StackWeightedModeView (unary history)
open SemiprimeSourceHistogramKeyBits (frame)
/-- Proof-side description of the actual thirty-five Boolean words. -/
structure Words where
  /-- All seventeen actual enumeration words, including their readonly WIDTH. -/
  enumData:W.Stack→List Bool:=fun _=>[]
  /-- All seven actual multiply-plus-offset words, including both operands. -/
  productData:M.Stack→List Bool:=fun _=>[]
  /-- Remaining real unary order markers, acquired by copying and popping WIDTH. -/
  orders:List Bool:=[]
  /-- Current positive unary weight, physically incremented once per order. -/
  weight:List Bool:=[]
  /-- Current unary order index, physically incremented once per order. -/
  order:List Bool:=[]
  /-- Remaining real unary slots in the current copied product. -/
  slotsTodo:List Bool:=[]
  /-- Current unary slot index, drained between consecutive orders. -/
  slot:List Bool:=[]
  /-- Actual two-field mode-label assembly word. -/
  word:List Bool:=[]
  /-- Chronological reverse log of physically emitted label records. -/
  labelHistory:List Bool:=[]
  /-- Chronological reverse log of physically emitted weights. -/
  weightHistory:List Bool:=[]
  /-- Disjoint restoring copy/logger scratch. -/
  copyScratch:List Bool:=[]
  /-- Disjoint restoring field-framing scratch. -/
  frameScratch:List Bool:=[]
  /-- Actual acquired mode-label vector after its physical final reversal. -/
  labels:List Bool:=[]
/-- Literal projection to the thirty-five actual Boolean data words. -/
def store (v:Words) :Stack→List Bool
  | .inl k=>v.enumData k
  | .inr (.inl k)=>v.productData k
  | .inr (.inr .orders)=>v.orders
  | .inr (.inr .weight)=>v.weight
  | .inr (.inr .order)=>v.order
  | .inr (.inr .slotsTodo)=>v.slotsTodo
  | .inr (.inr .slot)=>v.slot
  | .inr (.inr .word)=>v.word
  | .inr (.inr .labelHistory)=>v.labelHistory
  | .inr (.inr .weightHistory)=>v.weightHistory
  | .inr (.inr .copyScratch)=>v.copyScratch
  | .inr (.inr .frameScratch)=>v.frameScratch
  | .inr (.inr .labels)=>v.labels
/-- Proof notation for one actual physical word update. -/
def write (v:Words) (k:Stack) (xs:List Bool) :Words:=match k with
  | .inl k=>{v with enumData:=Function.update v.enumData k xs}
  | .inr (.inl k)=>{v with productData:=Function.update v.productData k xs}
  | .inr (.inr .orders)=>{v with orders:=xs}
  | .inr (.inr .weight)=>{v with weight:=xs}
  | .inr (.inr .order)=>{v with order:=xs}
  | .inr (.inr .slotsTodo)=>{v with slotsTodo:=xs}
  | .inr (.inr .slot)=>{v with slot:=xs}
  | .inr (.inr .word)=>{v with word:=xs}
  | .inr (.inr .labelHistory)=>{v with labelHistory:=xs}
  | .inr (.inr .weightHistory)=>{v with weightHistory:=xs}
  | .inr (.inr .copyScratch)=>{v with copyScratch:=xs}
  | .inr (.inr .frameScratch)=>{v with frameScratch:=xs}
  | .inr (.inr .labels)=>{v with labels:=xs}
theorem store_write (v:Words) (k:Stack) (xs:List Bool) :
    Function.update (store v) k xs=store (write v k xs):=by
  rcases k with k|k
  · funext j;rcases j with j|j
    · by_cases h:j=k <;> simp [Function.update,store,write,h]
    · rcases j with j|j
      · rfl
      · cases j <;> rfl
  · rcases k with k|k
    · funext j;rcases j with j|j
      · rfl
      · rcases j with j|j
        · by_cases h:j=k <;> simp [Function.update,store,write,h]
        · cases j <;> rfl
    · cases k <;> funext j <;> rcases j with j|j
      all_goals first | rfl | (rcases j with j|j;try rfl;cases j <;> rfl)
/-- Mode labels are literal two-field records, preserving order and slot padding. -/
def modeWord (slot order:Nat) :List Bool:=frame (unary slot) (frame (unary order) [])
theorem modeWord_length (slot order:Nat) :(modeWord slot order).length=2*slot+2*order+2:=by
  simp only [modeWord,SemiprimeSourceHistogramKeyBits.frame_length,
    SemiprimeD1StackWeightedModeView.unary_length,List.length_nil]
  omega
/-- Exact current physical slot iteration with retained metadata and both partial logs. -/
def scanning (packets tiles width remaining order todo slot:Nat) (wh lh:List Bool) :Words:=
  {enumData:=W.input [] (unary width)
   productData:=M.data (unary packets) (unary tiles) [] [] [] [] (unary (packets*tiles))
   orders:=unary remaining,weight:=unary (order+1),order:=unary order,
   slotsTodo:=unary todo,slot:=unary slot,weightHistory:=wh,labelHistory:=lh}
/-- Actual payloads remaining in one order-major slot scan. -/
def slotWeights (order count:Nat) :List (List Bool):=List.replicate count (unary (order+1))
/-- The exact two-field payloads remaining in a consecutive physical slot scan. -/
def slotLabels (order first count:Nat) :List (List Bool):=
  (List.range count).map (fun k=>modeWord (first+k) order)
theorem slotLabels_cons (order first count:Nat) :
    slotLabels order first (count+1)=modeWord first order::slotLabels order (first+1) count:=by
  rw [slotLabels,List.range_succ_eq_map]
  simp only [List.map_cons,List.map_map,Function.comp_def,Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro k _
  congr 1
  omega
end RiemannGaussian.SemiprimeD1StackWeightedModeCatalogueView
