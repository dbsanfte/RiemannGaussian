/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackVertexArity

/-! # Real included arithmetic/copy calls for physical original vertex arity -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option Elab.async false
namespace RiemannGaussian.SemiprimeD1StackVertexArityComponents
open SemiprimeD1StackVertexArity
open SemiprimeD1StackProcedureFragments (Runs included_call)
open SemiprimeD1StackUnaryDivmod (unary)

/-- The actual three Copy operands never alias. -/
theorem copyStack_injective (kind:CopyKind) : Function.Injective (copyStack kind) := by cases kind <;> decide
/-- Product has four distinct physical operands, including the readonly R+1 cache. -/
theorem productStack_injective : Function.Injective productStack := by decide
/-- All actual comparison operands are separate. -/
theorem compareStack_injective : Function.Injective compareStack := by decide
/-- Copy destination is never its scratch. -/
theorem copyTarget_scratch (kind:CopyKind) : copyTarget kind≠Aux.copyScratch := by cases kind <;> decide

/-- Actual source-preserving copy, including its real call/return. -/
theorem copy_call (kind:CopyKind) (store:Stack→List Bool) (hs:store (aux .copyScratch)=[])
    (pc next:Label) (hc:program pc=.call (copyLabel kind 0) next) :
    Runs program (5*(store (source (copySource kind))).length+4) pc store next
      (Function.update store (aux (copyTarget kind))
        (store (source (copySource kind))++store (aux (copyTarget kind)))) := by
  apply included_call program (copyStack kind) (copyLabel kind) (copyStack_injective kind)
    SemiprimeD1StackCopy.code 0 (fun _=>rfl) pc next hc
    (5*(store (source (copySource kind))).length+3)
    (SemiprimeD1StackCopy.state 0 none (store (source (copySource kind))) (store (aux (copyTarget kind))) [])
    (SemiprimeD1StackCopy.done (store (source (copySource kind)))
      (store (source (copySource kind))++store (aux (copyTarget kind))))
  · rfl
  · rfl
  · exact SemiprimeD1StackCopy.copy_words _ _ none
  · constructor
    · intro k;fin_cases k <;> simp [copyStack,SemiprimeD1StackCopy.state,SemiprimeD1StackCopy.payload,hs]
    · intro k _;rfl
  · have hs':store (.inr Aux.copyScratch)=[]:=hs
    have hn:copyTarget kind≠Aux.copyScratch:=copyTarget_scratch kind
    constructor
    · intro k
      fin_cases k <;> simp [copyStack,source,aux,SemiprimeD1StackCopy.done,SemiprimeD1StackCopy.payload,
        Function.update,hn.symm,hs']
    · intro k hk
      have hn:k≠aux (copyTarget kind):=by intro h;exact hk 1 h.symm
      exact Function.update_of_ne hn _ _

/-- Product is actually executed on acquired unary operands; no multiplication answer or clock is supplied. -/
theorem product_call (store:Stack→List Bool) (m d:ℕ)
    (hm:store (aux .multiplier)=unary m) (hd:store (source .radiusSucc)=unary d)
    (hs:store (aux .mulScratch)=[]) (ha:store (aux .arity)=[]) :
    ∃time≤5*(m*(2*d+3)+1)+1,Runs program time (.inl .product) store (.inl .halt)
      (Function.update (Function.update store (aux .multiplier) []) (aux .arity) (unary (m*d))) := by
  obtain ⟨time,ht,hr⟩:=Product.product_run m d
  refine ⟨time+1,by omega,?_⟩
  apply included_call program productStack productLabel productStack_injective Product.code Product.entry
    (fun _=>rfl) (.inl .product) (.inl .halt) rfl time
    (⟨some Product.entry,none,Product.contents (unary m) (unary d) [] []⟩:B.State Product.Stack Product.Label)
    (⟨none,none,Product.contents [] (unary d) [] (unary (m*d))⟩:B.State Product.Stack Product.Label)
  · rfl
  · rfl
  · exact hr
  · constructor
    · intro k;cases k <;> simp [productStack,Product.contents,hm,hd,hs,ha]
    · intro k _;rfl
  · have hd':store (.inl Source.radiusSucc)=unary d:=hd
    have hs':store (.inr Aux.mulScratch)=[]:=hs
    constructor
    · intro k;cases k <;> simp [productStack,Product.contents,source,aux,Function.update,hd',hs']
    · intro k hk
      have h0:k≠aux .multiplier:=by intro h;exact hk .multiplier h.symm
      have h1:k≠aux .arity:=by intro h;exact hk .product h.symm
      simp [Function.update,h0,h1]

/-- Real comparison of copied zero+index against the copied actual digit count. -/
theorem compare_call (store:Stack→List Bool) (index digits:ℕ)
    (hl:store (aux .compareLeft)=[]) (hr:store (aux .compareRight)=unary index)
    (hd:store (aux .compareLimit)=unary digits) (hv:store (aux .compareResult)=[]) :
    ∃time≤30*(index+digits+1)+11,Runs program time (.inl .compare) store (.inl .verdict)
      (Function.update (Function.update (Function.update store (aux .compareRight) []) (aux .compareLimit) [])
        (aux .compareResult) [decide (index<digits)]) := by
  obtain ⟨time,ht,he⟩:=Compare.compare_run 0 index digits
  simp only [Nat.zero_add] at he ht
  refine ⟨time+1,by omega,?_⟩
  apply included_call program compareStack compareLabel compareStack_injective Compare.code Compare.entry
    (fun _=>rfl) (.inl .compare) (.inl .verdict) rfl time
    (⟨some Compare.entry,none,Compare.contents [] (unary index) (unary digits) []⟩:B.State Compare.Stack Compare.Label)
    (⟨none,none,Compare.contents [] [] [] [decide (index<digits)]⟩:B.State Compare.Stack Compare.Label)
  · rfl
  · rfl
  · exact he
  · constructor
    · intro k;cases k <;> simp [compareStack,Compare.contents,hl,hr,hd,hv]
    · intro k _;rfl
  · have hl':store (.inr Aux.compareLeft)=[]:=hl
    constructor
    · intro k;cases k <;> simp [compareStack,Compare.contents,aux,Function.update,hl']
    · intro k hk
      have h0:k≠aux .compareRight:=by intro h;exact hk .right h.symm
      have h1:k≠aux .compareLimit:=by intro h;exact hk .limit h.symm
      have h2:k≠aux .compareResult:=by intro h;exact hk .valid h.symm
      simp [Function.update,h0,h1,h2]
end RiemannGaussian.SemiprimeD1StackVertexArityComponents
