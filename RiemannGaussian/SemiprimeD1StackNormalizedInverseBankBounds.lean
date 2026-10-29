/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOperationBounds
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOuterView
/-! # All58 physical bank lengths: bounded rational/cache fields and retained array bytes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseBankBounds
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseReadBuffers SemiprimeD1StackNormalizedInverseIndices
open SemiprimeD1StackNormalizedInverseOuterView SemiprimeD1StackNormalizedInverseWidths
open SemiprimeD1StackNormalizedInverseOperationCall
open SemiprimeD1StackNormalizedInverseCleanup (mass)
/-- Explicit bounds cover ALL36 rational words,8 coefficient fields and14 controller words. -/
def BoundedBank (w : Words) (r c u : ℕ) : Prop :=
  (∀k,(w.rational k).length ≤ r) ∧ (∀reg den,(w.registers (reg,den)).length ≤ c) ∧ (∀k,(w.auxiliary k).length ≤ u)
/-- Abstract bank decomposition avoids expanding the fixed nested arithmetic role types in any proof. -/
theorem sum_bank {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (f : A→List Bool) (g : B→List Bool) (h : C→List Bool) :
    (∑k : A⊕(B⊕C),(Sum.elim f (Sum.elim g h) k).length)=
      (∑k : A,(f k).length)+((∑k : B,(g k).length)+(∑k : C,(h k).length)) := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl,Sum.elim_inr]
  congr 1
  rw [Fintype.sum_sum_type]
  rfl
/-- No alias shadow is omitted from the complete physical-bank mass. -/
theorem mass_le (w : Words) (r c u : ℕ) (h : BoundedBank w r c u) : mass (store w) ≤ 36*r+8*c+14*u := by
  have hr : (∑k : R.Stack,(w.rational k).length) ≤ 36*r := by
    calc
      _ ≤ ∑_k : R.Stack,r :=Finset.sum_le_sum (fun k _=>h.1 k)
      _=_ :=by simp only [Finset.sum_const,Finset.card_univ,SemiprimeD1StackRationalOperation.stack_card,smul_eq_mul]
  have hc : (∑k : Reg×Bool,(w.registers k).length) ≤ 8*c := by
    calc
      _ ≤ ∑_k : Reg×Bool,c :=Finset.sum_le_sum (fun k _=>h.2.1 k.1 k.2)
      _=_ :=by simp only [Finset.sum_const,Finset.card_univ,show Fintype.card (Reg×Bool)=8 by decide,smul_eq_mul]
  have hu : (∑k : Aux,(w.auxiliary k).length) ≤ 14*u := by
    calc
      _ ≤ ∑_k : Aux,u :=Finset.sum_le_sum (fun k _=>h.2.2 k)
      _=_ :=by simp only [Finset.sum_const,Finset.card_univ,show Fintype.card Aux=14 by decide,smul_eq_mul]
  have he : mass (store w)=(∑k : R.Stack,(w.rational k).length)+
      ((∑k : Reg×Bool,(w.registers k).length)+(∑k : Aux,(w.auxiliary k).length)) :=
    sum_bank w.rational w.registers w.auxiliary
  rw [he]
  omega
/-- An actual acquired coefficient write charges both its complete fields and retains every foreign bank word. -/
theorem put_bound (w : Words) (r c u : ℕ) (h : BoundedBank w r c u) (reg : Reg)
    (word : SemiprimeRationalBits.RationalWord) (hw : bytes word ≤ c) : BoundedBank (putReg w reg word) r c u := by
  refine ⟨h.1,?_,h.2.2⟩
  intro other den
  by_cases he:other=reg
  · subst other
    cases den
    · rw [(putReg_fields w reg word).1]
      exact (Nat.le_add_right _ _).trans hw
    · rw [(putReg_fields w reg word).2]
      exact (Nat.le_add_left _ _).trans hw
  · rw [putReg_other w reg other word den he]
    exact h.2.1 other den
/-- Actual three-index updates remain bounded by their physically present unary marker counts. -/
theorem counters_bound (w : Words) (r c u : ℕ) (h : BoundedBank w r c u)
    (terms a b : ℕ) (ht : terms ≤ u) (ha : a ≤ u) (hb : b ≤ u) : BoundedBank (counters w terms a b) r c u := by
  refine ⟨h.1,h.2.1,?_⟩
  intro k
  cases k <;> first
    | exact h.2.2 _
    | (change (unary terms).length ≤ u;simpa only [unary,List.length_replicate] using ht)
    | (change (unary a).length ≤ u;simpa only [unary,List.length_replicate] using ha)
    | (change (unary b).length ≤ u;simpa only [unary,List.length_replicate] using hb)
/-- Every real fitted arithmetic result fits this cache cap; no semantic Valid/Fits assumption is required. -/
theorem after_bound (site : Site) (w : Words) (width : List Bool) (r c u : ℕ)
    (h : BoundedBank w r c u) (hw : 2*width.length+1 ≤ c) : BoundedBank (after site w width) r c u := by
  apply put_bound w r c u h
  rw [acquired,execute_bytes]
  exact hw
/-- A missing cached-array entry is the literal ZERO; it is bounded with every actual stored entry. -/
theorem read_uniform (words : List SemiprimeRationalBits.RationalWord) (n cap : ℕ)
    (hzero : 2 ≤ cap) (h : ∀word∈words,bytes word ≤ cap) : bytes (SemiprimeD1StackNormalizedInverseSpec.readWord words n) ≤ cap := by
  induction words generalizing n with
  | nil=>exact hzero
  | cons word words ih=>
    cases n with
    | zero=>exact h word List.mem_cons_self
    | succ n=>exact ih n (fun x hx=>h x (List.mem_cons_of_mem word hx))
end RiemannGaussian.SemiprimeD1StackNormalizedInverseBankBounds
