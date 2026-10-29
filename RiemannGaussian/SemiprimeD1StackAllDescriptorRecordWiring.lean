/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecord
/-! # Injective actual component wiring and complete physical private inventory -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordWiring
open SemiprimeD1StackAllDescriptorRecord
private theorem routed_injective {K : Type} (targets : K→Option Common) (key : Common→Option K)
    (embed : K→Private) (he : Function.Injective embed)
    (hk : ∀k c,targets k=some c→key c=some k) :
    Function.Injective (fun k=>(targets k).elim (privateStack (embed k)) Sum.inl) :=by
  intro a b h
  cases ha:targets a with
  | none=>
    cases hb:targets b with
    | none=>
      simp only [ha,hb,Option.elim_none] at h
      exact he (Sum.inr.inj h)
    | some c=>simp only [ha,hb,Option.elim_none,Option.elim_some,privateStack] at h;cases h
  | some c=>
    cases hb:targets b with
    | none=>simp only [ha,hb,Option.elim_none,Option.elim_some,privateStack] at h;cases h
    | some d=>
      simp only [ha,hb,Option.elim_some] at h
      have hc:c=d:=Sum.inl.inj h
      subst d
      exact Option.some.inj ((hk a c ha).symm.trans (hk b c hb))
/-- Proof-side partial inverse for the distinct actual metadata common operands. -/
def metadataKey {K : Type} : Common→Option (SemiprimeD1StackDescriptorRecord.Stack K)
  | .source i=>some (.inr (.inl i))
  | .bank=>some (.inl (.inl (.inr (.inr (.inl .bank)))))
  | .history=>some (.inl (.inr (.inr .history)))
  | .output=>some (.inl (.inr (.inr .output)))
  | _=>none
/-- Every shared metadata operand is exactly its unique literal component role. -/
theorem metadata_key {K : Type} (k : SemiprimeD1StackDescriptorRecord.Stack K) (c : Common)
    (h : metadataAlias k=some c) : metadataKey c=some k :=by
  rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k
      · simp only [metadataAlias] at h;cases h
      · rcases k with k|k
        · simp only [metadataAlias] at h;cases h
        · rcases k with k|k
          · cases k <;> simp_all [metadataAlias,metadataKey]
            all_goals (subst c; rfl)
          · simp only [metadataAlias] at h;cases h
    · rcases k with k|k
      · simp only [metadataAlias] at h;cases h
      · cases k <;> simp_all [metadataAlias,metadataKey]
        all_goals (subst c; rfl)
  · rcases k with k|k
    · simp_all [metadataAlias,metadataKey]
      all_goals (subst c; rfl)
    · simp only [metadataAlias] at h;cases h
/-- Proof-side partial inverse for the distinct actual selected common operands. -/
def selectedKey {K : Type} : Common→Option (SemiprimeD1StackSelectedDescriptorRecord.Stack K)
  | .source i=>if i=1 then some (.inr .tag) else if i=2 then some (.inr .transform) else some (.inl (.inr (.inl i)))
  | c=>(metadataKey c).map Sum.inl
/-- Every shared selected operand is exactly its unique literal component role. -/
theorem selected_key {K : Type} (k : SemiprimeD1StackSelectedDescriptorRecord.Stack K) (c : Common)
    (h : selectedAlias k=some c) : selectedKey c=some k :=by
  rcases k with d|k
  · cases hd:metadataAlias d with
    | none=>simp only [selectedAlias,hd] at h;cases h
    | some a=>
      have hv:=metadata_key d a hd
      cases a with
      | source i=>
        by_cases hi:i=1 ∨ i=2
        · simp only [selectedAlias,hd,hi,ite_true] at h;cases h
        · have he:c=Common.source i:=by
            simpa only [selectedAlias,hd,hi,ite_false,Option.some.injEq] using h.symm
          subst c
          have de:d=Sum.inr (Sum.inl i):=(Option.some.inj hv).symm
          subst d
          have h1:i≠1:=fun hh=>hi (Or.inl hh)
          have h2:i≠2:=fun hh=>hi (Or.inr hh)
          simp only [selectedKey,h1,h2,ite_false]
      | bank=>
        have hc:c=Common.bank:=by simpa only [selectedAlias,hd,Option.some.injEq] using h.symm
        subst c
        change (metadataKey Common.bank).map Sum.inl=some (.inl d)
        rw [hv];rfl
      | history=>
        have hc:c=Common.history:=by simpa only [selectedAlias,hd,Option.some.injEq] using h.symm
        subst c
        change (metadataKey Common.history).map Sum.inl=some (.inl d)
        rw [hv];rfl
      | output=>
        have hc:c=Common.output:=by simpa only [selectedAlias,hd,Option.some.injEq] using h.symm
        subst c
        change (metadataKey Common.output).map Sum.inl=some (.inl d)
        rw [hv];rfl
      | tagReader=>cases hv
      | copyScratch=>cases hv
  · cases k <;> simp_all [selectedAlias,selectedKey]
    all_goals (subst c; rfl)
/-- Proof-side partial inverse for the distinct actual product common operands. -/
def productKey : Common→Option P.Stack
  | .source i=>if i=0 then some SemiprimeD1StackProductRecord.original else none
  | .bank=>some (.inr (.inl .bank))
  | .history=>some (.inr (.inr .history))
  | .output=>some (.inr (.inr .output))
  | _=>none
/-- Every shared product operand is exactly its unique literal component role. -/
theorem product_key (k : P.Stack) (c : Common) (h : productAlias k=some c) : productKey c=some k :=by
  rcases k with k|k
  · rcases k with k|k
    · simp only [productAlias] at h;cases h
    · cases k <;> simp_all [productAlias,productKey,SemiprimeD1StackProductRecord.original,
        SemiprimeD1StackProductRecord.tableStack,SemiprimeD1StackProductRecord.Z.original]
      all_goals (subst c; rfl)
  · rcases k with k|k
    · cases k <;> simp_all [productAlias,productKey]
      all_goals (subst c; rfl)
    · cases k <;> simp_all [productAlias,productKey]
      all_goals (subst c; rfl)
/-- Proof-side partial inverse for the distinct actual boundary common operands. -/
def boundaryKey : Common→Option Z.Stack
  | .source i=>if i=0 then some SemiprimeD1StackBoundaryRecord.original else none
  | .bank=>some (.inr (.inl .bank))
  | .history=>some (.inr (.inr .history))
  | .output=>some (.inr (.inr .output))
  | _=>none
/-- Every shared boundary operand is exactly its unique literal component role. -/
theorem boundary_key (k : Z.Stack) (c : Common) (h : boundaryAlias k=some c) : boundaryKey c=some k :=by
  by_cases hn:k=SemiprimeD1StackBoundaryRecord.original
  · subst k
    simp only [boundaryAlias,ite_true] at h
    have he:=Option.some.inj h
    subst c
    rfl
  · simp only [boundaryAlias,hn,ite_false] at h
    rcases k with k|k
    · cases h
    · rcases k with k|k
      · cases k <;> simp_all [boundaryKey]
        all_goals (subst c; rfl)
      · cases k <;> simp_all [boundaryKey]
        all_goals (subst c; rfl)
/-- Proof-side partial inverse for the distinct actual boolean common operands. -/
def booleanKey : Common→Option B.Stack
  | .bank=>some (.inr (.inl .bank))
  | .history=>some (.inr (.inr .history))
  | .output=>some (.inr (.inr .output))
  | _=>none
/-- Every shared boolean operand is exactly its unique literal component role. -/
theorem boolean_key (k : B.Stack) (c : Common) (h : booleanAlias k=some c) : booleanKey c=some k :=by
  rcases k with k|k
  · simp only [booleanAlias] at h;cases h
  · rcases k with k|k
    · cases k <;> simp_all [booleanAlias,booleanKey]
      all_goals (subst c; rfl)
    · cases k <;> simp_all [booleanAlias,booleanKey]
      all_goals (subst c; rfl)
/-- Every actual input-client role has a distinct physical target. -/
theorem inputStack_injective : Function.Injective inputStack :=by
  apply routed_injective metadataAlias metadataKey Sum.inl Sum.inl_injective metadata_key
/-- Every actual carry-client role has a distinct physical target. -/
theorem carryStack_injective : Function.Injective carryStack :=by
  apply routed_injective metadataAlias metadataKey (fun k=>.inr (.inl k))
    (by intro a b h;exact Sum.inl.inj (Sum.inr.inj h)) metadata_key
/-- No computed-selector or original-source role collides in scale wiring. -/
theorem scaleStack_injective : Function.Injective scaleStack :=by
  apply routed_injective selectedAlias selectedKey (fun k=>.inr (.inr (.inl k)))
    (by intro a b h;exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj h))) selected_key
/-- Both actual transform selectors and every template/private shadow remain distinct. -/
theorem transformStack_injective : Function.Injective transformStack :=by
  apply routed_injective selectedAlias selectedKey (fun k=>.inr (.inr (.inr (.inl k))))
    (by intro a b h;exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h)))) selected_key
/-- Actual original N, scope, caller and all product-private roles remain distinct. -/
theorem productStack_injective : Function.Injective productStack :=by
  apply routed_injective productAlias productKey (fun k=>.inr (.inr (.inr (.inr (.inl k)))))
    (by intro a b h;exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h))))) product_key
/-- Actual boundary-source aliases have no private or caller collision. -/
theorem boundaryStack_injective : Function.Injective boundaryStack :=by
  apply routed_injective boundaryAlias boundaryKey (fun k=>.inr (.inr (.inr (.inr (.inr (.inl k))))))
    (by intro a b h;exact Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h)))))) boundary_key
/-- Actual three-mode Boolean source aliases are injective. -/
theorem booleanStack_injective : Function.Injective booleanStack :=by
  apply routed_injective booleanAlias booleanKey (fun k=>.inr (.inr (.inr (.inr (.inr (.inr k))))))
    (by intro a b h;exact Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj h)))))) boolean_key
/-- Original tag, reader and preserving-copy scratch are distinct real words. -/
theorem copyStack_injective : Function.Injective copyStack :=by decide
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordWiring
