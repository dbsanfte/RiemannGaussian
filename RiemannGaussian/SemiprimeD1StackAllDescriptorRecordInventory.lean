/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackAllDescriptorRecord
/-! # Complete fixed physical cleanup inventory for the actual1263-role source -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 1000000
namespace RiemannGaussian.SemiprimeD1StackAllDescriptorRecordInventory
open SemiprimeD1StackAllDescriptorRecord
private theorem counter_complete (k : SemiprimeD1StackDigitCount.Stack) : k∈counterRoles :=by cases k <;> simp [counterRoles]
private theorem scope_complete (k : SemiprimeD1StackPortOrdinalStream.Stack) : k∈scopeRoles :=by cases k <;> simp [scopeRoles]
private theorem logger_complete (k : SemiprimeD1StackVertexRecordStream.Stack) : k∈loggerRoles :=by cases k <;> simp [loggerRoles]
private theorem static_complete {K : Type} (roles : List K) (h : ∀k,k∈roles)
    (k : SemiprimeD1StackStaticRecord.Stack K) : k∈staticRecordRoles roles :=by
  rcases k with k|k
  · rcases k with k|k
    · simp only [staticRecordRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inl ⟨k,h k,rfl⟩
    · rcases k with k|k
      · simp only [staticRecordRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inr (Or.inl ⟨k,h k,rfl⟩)
      · rcases k with k|k
        · simp only [staticRecordRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inr (Or.inr (Or.inl ⟨k,counter_complete k,rfl⟩))
        · cases k <;> simp [staticRecordRoles]
  · rcases k with k|k
    · simp only [staticRecordRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,scope_complete k,rfl⟩))))
    · simp only [staticRecordRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k,logger_complete k,rfl⟩))))
private theorem metadata_complete {K : Type} (roles : List K) (h : ∀k,k∈roles)
    (k : SemiprimeD1StackDescriptorRecord.Stack K) : k∈metadataRoles roles :=by
  rcases k with k|k
  · simp only [metadataRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inl ⟨k,static_complete roles h k,rfl⟩
  · rcases k with k|k
    · simp [metadataRoles]
    · cases k;simp [metadataRoles]
private theorem selected_complete {K : Type} (roles : List K) (h : ∀k,k∈roles)
    (k : SemiprimeD1StackSelectedDescriptorRecord.Stack K) : k∈selectedRoles roles :=by
  rcases k with k|k
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨k,metadata_complete roles h k,rfl⟩)
  · cases k <;> simp [selectedRoles,selectorRoles]
private theorem product_complete (k : P.Stack) : k∈productRoles :=by
  rcases k with k|k
  · rcases k with k|k
    · simp only [productRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inl ⟨.inl k,Or.inl ⟨k,SemiprimeD1StackProductTableSpec.checkerRoles_complete k,rfl⟩,rfl⟩
    · cases k <;> simp [productRoles]
  · rcases k with k|k
    · simp only [productRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inr (Or.inl ⟨k,scope_complete k,rfl⟩)
    · simp only [productRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inr (Or.inr ⟨k,logger_complete k,rfl⟩)
private theorem public_complete (k : SemiprimeD1BinaryPublicAcquisition.Stack) : k∈SemiprimeD1StackPublicInputTable.publicRoles :=by
  have h:SemiprimeD1StackPublicInputTable.publicRoles.toFinset=(Finset.univ : Finset SemiprimeD1BinaryPublicAcquisition.Stack):=by decide
  exact List.mem_toFinset.mp (h.symm ▸ Finset.mem_univ k)
private theorem boundary_complete (k : Z.Stack) : k∈boundaryRoles :=by
  rcases k with k|k
  · rcases k with k|k
    · simp only [boundaryRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inl ⟨.inl k,Or.inl ⟨k,public_complete k,rfl⟩,rfl⟩
    · cases k <;> simp [boundaryRoles]
  · rcases k with k|k
    · simp only [boundaryRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inr (Or.inl ⟨k,scope_complete k,rfl⟩)
    · simp only [boundaryRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inr (Or.inr ⟨k,logger_complete k,rfl⟩)
private theorem boolean_complete (k : B.Stack) : k∈booleanRoles :=by
  rcases k with k|k
  · cases k;simp [booleanRoles]
  · rcases k with k|k
    · simp only [booleanRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inr (Or.inl ⟨k,scope_complete k,rfl⟩)
    · simp only [booleanRoles,List.append_assoc,List.mem_append,List.mem_map];exact Or.inr (Or.inr ⟨k,logger_complete k,rfl⟩)
/-- Every allocated component/private/shadow word has an actual cleanup position. -/
theorem privateRoles_complete (k : Private) : k∈privateRoles :=by
  simp only [privateRoles,List.append_assoc,List.mem_append,List.mem_map]
  rcases k with k|k
  · exact Or.inl ⟨k,metadata_complete _ SemiprimeD1StackPublicInputTable.roles_complete k,rfl⟩
  · rcases k with k|k
    · exact Or.inr (Or.inl ⟨k,metadata_complete _ SemiprimeD1StackPublicCarryTable.roles_complete k,rfl⟩)
    · rcases k with k|k
      · exact Or.inr (Or.inr (Or.inl ⟨k,selected_complete _ SemiprimeD1StackPublicScaleTable.roles_complete k,rfl⟩))
      · rcases k with k|k
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k,selected_complete _ SemiprimeD1StackPublicTransformTable.roles_complete k,rfl⟩)))
        · rcases k with k|k
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,product_complete k,rfl⟩))))
          · rcases k with k|k
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,boundary_complete k,rfl⟩)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨k,boolean_complete k,rfl⟩)))))
/-- Every actual1263-role source operand is either common caller data or one
of the1252 physically drained allocated slots. -/
theorem physical_cover (k : Stack) : (∃c:Common,k=Sum.inl c) ∨ ∃p∈privateRoles,k=privateStack p :=by
  cases k with
  | inl c=>exact Or.inl ⟨c,rfl⟩
  | inr p=>exact Or.inr ⟨p,privateRoles_complete p,rfl⟩
end RiemannGaussian.SemiprimeD1StackAllDescriptorRecordInventory
