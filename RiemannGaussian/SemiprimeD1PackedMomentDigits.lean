/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1PackedMomentAlgebra
import RiemannGaussian.SemiprimePublicFactorCount

/-! # Local digit marks on the actual arithmetic graph
The mark reads the actual ordered first-side input WORD. It neither supplies
an operand nor changes any Boolean constraint, port, multiplicity or scope.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RiemannGaussian.SemiprimeD1PackedMomentDigits
open scoped BigOperators
open SemiprimeMacroGraph SemiprimeMacroGraphSemantics SemiprimeMacroGraphExtension

/-- A local original input vertex contributes its physically decoded first
operand digit at its actual radix position; all other vertices contribute zero. -/
def originalMark (p : Config) : (v : Vertex p.r p.t p.digits)→(LocalSlot v→Bool)→ℕ
  | .input side i, x =>
      if side=0 then readWord (p.r*p.t+1) (fun bit => x (.inl bit))*(2^p.bits)^i.val else 0
  | _, _ => 0

/-- Literal ordered-port version of the same mark, including zero-mark equality
vertices. No global operand is an input to this coefficient function. -/
def localMark (p : Config) : (v : SubdividedVertex p.r p.t p.digits)→
    (Fin (subdividedArity v)→Bool)→ℕ
  | .inl v, x => originalMark p v (fun slot => x ((localSlotFinEquiv v) slot))
  | .inr _, _ => 0

/-- Exact original input-word decoder, before any projection to a full operand. -/
theorem input_word (p : Config) (a : BitSignal p.r p.t p.digits→Bool)
    (side : Fin 2) (i : Fin (p.r*p.t)) :
    readWord (p.r*p.t+1) (fun bit => originalLocal p a (.input side i) (.inl bit))=
      wordNat p a (.input side i) := rfl

/-- Summing the actual original local marks retains every first-side digit. -/
theorem original_marks (p : Config) (a : BitSignal p.r p.t p.digits→Bool) :
    (∑v : Vertex p.r p.t p.digits, originalMark p v (originalLocal p a v))=
      ∑i : Fin (p.r*p.t), wordNat p a (.input 0 i)*(2^p.bits)^i.val := by
  rw [←(vertexSumEquiv p.r p.t p.digits).symm.sum_comp]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,vertexSumEquiv,
    Equiv.coe_fn_symm_mk,originalMark,Fin.sum_univ_two,ite_true,Fin.isValue,
    show (1 : Fin 2)≠0 by decide,ite_false,
    Finset.sum_const_zero,add_zero,input_word]

/-- Inactive input words vanish by their actual local checker constraints. -/
theorem digit_sum (p : Config) (a : BitSignal p.r p.t p.digits→Bool)
    (ha : OriginalAccepted p a) :
    (∑i : Fin (p.r*p.t), wordNat p a (.input 0 i)*(2^p.bits)^i.val)=sourceOperand p a 0 := by
  have he : (∑i : Fin (p.r*p.t), wordNat p a (.input 0 i)*(2^p.bits)^i.val)=
      ∑i : Fin (p.r*p.t), sourceFunction p a 0 i.val*(2^p.bits)^i.val := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [sourceFunction,i.isLt,dite_eq_left]
  rw [he,Fin.sum_univ_eq_sum_range (fun i => sourceFunction p a 0 i*(2^p.bits)^i) (p.r*p.t)]
  unfold sourceOperand
  symm
  apply Finset.sum_subset (Finset.range_mono p.cap)
  intro i _ hi
  have hd : p.digits ≤ i := by simpa only [Finset.mem_range,not_lt] using hi
  rw [sourceFunction_zero p a ha 0 i hd,Nat.zero_mul]

/-- Accepted actual local marks decode the genuine FIRST integer factor. -/
theorem original_operand (p : Config) (a : Accepted p) :
    (∑v : Vertex p.r p.t p.digits, originalMark p v (originalLocal p a.val v))=
      sourceOperand p a.val 0 := (original_marks p a.val).trans (digit_sum p a.val a.property)

/-- Equality checks, rather than a supplied decoded assignment, justify each
ordered local mark's producer-side shared signal read. -/
theorem local_mark_shared (p : Config) (a : Edge p.r p.t p.digits→Bool)
    (ha : SubdividedAccepted p a) (v : Vertex p.r p.t p.digits) :
    localMark p (.inl v) (fun slot => a (orderedEdgeAt p.digits_pos p.cap ⟨.inl v,slot⟩))=
      originalMark p v (originalLocal p (fun signal => a (signal,false)) v) := by
  have heq := ((subdivided_tables_iff p a).mp ha).1
  have he (e : Edge p.r p.t p.digits) : a e=a (e.1,false) := by
    rcases e with ⟨signal,side⟩
    cases side
    · rfl
    · exact (heq signal).symm
  dsimp only [localMark,originalLocal]
  congr 1
  funext slot
  rw [ordered_original_edge,ordered_unstructured]
  exact he _

/-- The FULL ordered subdivided graph's local marks, with all equality vertices
and every inactive input retained, recover the exact original operand. -/
theorem subdivided_operand (p : Config) (a : Edge p.r p.t p.digits→Bool)
    (ha : SubdividedAccepted p a) :
    (∑v : SubdividedVertex p.r p.t p.digits,
      localMark p v (fun slot => a (orderedEdgeAt p.digits_pos p.cap ⟨v,slot⟩)))=
      sourceOperand p (fun signal => a (signal,false)) 0 := by
  rw [Fintype.sum_sum_type]
  have he : (∑v : Vertex p.r p.t p.digits,
      localMark p (.inl v) (fun slot => a (orderedEdgeAt p.digits_pos p.cap ⟨.inl v,slot⟩)))=
      ∑v : Vertex p.r p.t p.digits, originalMark p v (originalLocal p (fun signal => a (signal,false)) v) := by
    exact Finset.sum_congr rfl (fun v _ => local_mark_shared p a ha v)
  rw [he]
  have hz : (∑signal : BitSignal p.r p.t p.digits,
      localMark p (.inr signal) (fun slot => a (orderedEdgeAt p.digits_pos p.cap ⟨.inr signal,slot⟩)))=0 := by
    simp only [localMark,Finset.sum_const_zero]
  rw [hz,Nat.add_zero]
  exact original_operand p ⟨_,subdivided_original p a ha⟩

end RiemannGaussian.SemiprimeD1PackedMomentDigits
