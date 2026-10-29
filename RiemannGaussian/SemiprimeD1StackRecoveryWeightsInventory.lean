/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeights
/-! # Dedicated53-role cleanup excludes THIS source's immutable cached-power tape
The old inverse54-role whole-source cleanup must not be reused: its last role
is now the actual retained power input. Every other helper work/shadow remains.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsInventory
open SemiprimeD1StackRecoveryWeights
/-- All five retained helper fields are excluded from THIS actual cleanup. -/
def kept (k:I.Stack):Prop:=k=SemiprimeD1StackNormalizedInverse.template ∨
  k=SemiprimeD1StackNormalizedInverse.aux .denominator ∨ k=SemiprimeD1StackNormalizedInverse.aux .prefixReverse ∨
  k=SemiprimeD1StackNormalizedInverse.aux .originalQ ∨ k=SemiprimeD1StackNormalizedInverse.aux .output
/-- The omitted old54th work role is precisely the actual immutable power tape. -/
theorem last_work:SemiprimeD1StackNormalizedInverse.workRole (53:Fin 54)=SemiprimeD1StackNormalizedInverse.aux .prefixReverse:=rfl
/-- No actual private cleanup address aliases the immutable power-array input. -/
theorem work_not_powers (i:Fin 53):workRole i≠aux .prefixReverse:=by fin_cases i <;> decide
/-- Every one of the53 actual private fields is disjoint from all five retained helper words. -/
theorem work_not_kept (i:Fin 53):¬kept (SemiprimeD1StackNormalizedInverse.workRole ⟨i.val,by omega⟩):=by
  intro h
  rcases h with ht|ha|hp|hq|ho
  · exact SemiprimeD1StackNormalizedInverseInventory.workRole_not_template _ ht
  · exact SemiprimeD1StackNormalizedInverseInventory.workRole_not_denominator _ ha
  · exact work_not_powers i (congrArg helper hp)
  · exact SemiprimeD1StackNormalizedInverseInventory.workRole_not_q _ hq
  · exact SemiprimeD1StackNormalizedInverseInventory.workRole_not_output _ ho
/-- No omitted shadow or unused allocation: all nonretained helper words occur in THIS53-slot inventory. -/
theorem work_complete (k:I.Stack) (hk:¬kept k):
    ∃i:Fin 53,SemiprimeD1StackNormalizedInverse.workRole ⟨i.val,by omega⟩=k:=by
  obtain ⟨i,hi⟩:=SemiprimeD1StackNormalizedInverseInventory.workRole_complete k
    (fun h=>hk (Or.inl h)) (fun h=>hk (Or.inr (Or.inl h)))
    (fun h=>hk (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    (fun h=>hk (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  by_cases hl:i.val<53
  · exact ⟨⟨i.val,hl⟩,hi⟩
  · have he:i=(53:Fin 54):=Fin.ext (by omega)
    rw [he,last_work] at hi
    exact (hk (Or.inr (Or.inr (Or.inl hi.symm)))).elim
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsInventory
