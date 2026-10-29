/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackLeaf
/-! # Exact declarative registers between the leaf's actual included calls -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 131072
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeD1StackLeafState
open SemiprimeD1StackLeaf
namespace PS
export SemiprimeD1StackVertexProductState (Values Slot data address data_get data_other data_update)
end PS
/-- The only outer registers that can be live between included calls. -/
inductive Slot where
  | widthBits | catalogue | sum | sumResult | valid | unaryInput | counter | zero
  deriving DecidableEq,Repr
instance : Fintype Slot := Fintype.ofList [.widthBits,.catalogue,.sum,.sumResult,.valid,.unaryInput,.counter,.zero]
  (by intro s; cases s <;> simp)
/-- Fixed physical addresses of the outer register tuple. -/
def address : Slot→Stack
  | .widthBits => aux .widthBits
  | .catalogue => aux .catalogue
  | .sum => aux .sum
  | .sumResult => aux .sumResult
  | .valid => aux .valid
  | .unaryInput => unaryStack .left
  | .counter => unaryStack .output
  | .zero => enumerationWork .word
/-- Distinct slots are genuinely distinct physical registers. -/
theorem address_injective : Function.Injective address := by decide
/-- Outer live register tuple, a proof-side finite record only. -/
abbrev Values := Slot→List Bool
/-- Physical state invariant: exact product registers and outer live tuple;
all other work registers are empty. -/
def data (p : PS.Values) (v : Values) : Stack→List Bool
  | .inl k => PS.data p k
  | k => if k=address .widthBits then v .widthBits else
      if k=address .catalogue then v .catalogue else
      if k=address .sum then v .sum else
      if k=address .sumResult then v .sumResult else
      if k=address .valid then v .valid else
      if k=address .unaryInput then v .unaryInput else
      if k=address .counter then v .counter else
      if k=address .zero then v .zero else []
/-- Product registers are stored directly, without a decoder or semantic getter. -/
theorem data_product (p : PS.Values) (v : Values) (k : P.Stack) :
    data p v (productStack k)=PS.data p k := rfl
/-- Every original product slot has its declared physical contents. -/
theorem data_product_get (p : PS.Values) (v : Values) (s : PS.Slot) :
    data p v (productStack (PS.address s))=p s := PS.data_get p s
/-- Every outer register has its declared physical contents. -/
theorem data_get (p : PS.Values) (v : Values) (s : Slot) : data p v (address s)=v s := by
  cases s <;> simp [data,address,aux,unaryStack,enumerationWork]
/-- Every unmentioned outer work register is genuinely empty. -/
theorem data_other (p : PS.Values) (v : Values) (k : Stack)
    (hp : ∀j,k ≠ productStack j) (hk : ∀s,k ≠ address s) : data p v k=[] := by
  cases k with
  | inl k => exact (hp k rfl).elim
  | inr k => simp [data,hk]
/-- Replacing an outer slot changes exactly its one physical stack. -/
theorem data_update (p : PS.Values) (v : Values) (s : Slot) (word : List Bool) :
    data p (Function.update v s word)=Function.update (data p v) (address s) word := by
  funext k
  by_cases hex : ∃t,k=address t
  · obtain ⟨t,rfl⟩:=hex
    rw [data_get]
    by_cases he : t=s
    · subst t; simp
    · have hn : address t ≠ address s := fun hh=>he (address_injective hh)
      simp only [Function.update_of_ne he,Function.update_of_ne hn,data_get]
  · have hk : ∀t,k ≠ address t := by simpa only [not_exists] using hex
    cases k with
    | inl k =>
      have hn : productStack k ≠ address s := hk s
      change PS.data p k=Function.update (data p v) (address s) word (productStack k)
      rw [Function.update_of_ne hn]
      rfl
    | inr k =>
      rw [data_other _ _ (.inr k) (by intro j; simp [productStack]) hk,
        Function.update_of_ne (hk s),data_other _ _ (.inr k) (by intro j; simp [productStack]) hk]
/-- Replacing an actual product slot changes exactly its shared physical stack. -/
theorem data_product_update (p : PS.Values) (v : Values) (s : PS.Slot) (word : List Bool) :
    data (Function.update p s word) v=
      Function.update (data p v) (productStack (PS.address s)) word := by
  funext k
  cases k with
  | inl k =>
    change PS.data (Function.update p s word) k=_
    rw [PS.data_update]
    by_cases he : k=PS.address s
    · subst k; simp [productStack]
    · simp [productStack,he,data]
  | inr k => simp [data,productStack]
/-- Direct product inclusion has no hidden work-bank contents. -/
theorem product_project (p : PS.Values) (v : Values) (k : P.Stack) :
    data p v (productStack k)=PS.data p k := rfl
/-- Real catalogue parser sees exactly its current physical stream and assignment. -/
theorem field_project (p : PS.Values) (v : Values) (k : F.Stack) :
    data p v (fieldStack k)=
      match k with
      | .inl .input => v .catalogue
      | .inl .scratch => []
      | .inl .output => p .assignment
      | .inr _ => v .valid := by
  fin_cases k
  · exact data_get p v .catalogue
  · rfl
  · exact data_product_get p v .assignment
  · exact data_get p v .valid

end RiemannGaussian.SemiprimeD1StackLeafState
