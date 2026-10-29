/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseView
/-! # Actual array-reader buffers and disjoint coefficient/cache writes -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseReadBuffers
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
/-- Actual bounded unary metadata, never a decoded runtime Nat. -/
def unary (n : ℕ) : List Bool := List.replicate n true
/-- Only the physical array reader and query-marker copy are changed. -/
def buffers (w : Words) (reader todo : List Bool) : Words :=
  {w with auxiliary:=fun k=>if k=.reader then reader else if k=.readTodo then todo else w.auxiliary k}
/-- Every actual reader pop changes only that physical word. -/
theorem update_reader (w : Words) (reader todo xs : List Bool) :
    Function.update (store (buffers w reader todo)) (aux .reader) xs=store (buffers w xs todo) := by
  rw [update_aux]
  congr 1
  congr 1
  funext k;cases k <;> simp [buffers]
/-- Every actual index-marker pop changes only that physical word. -/
theorem update_todo (w : Words) (reader todo xs : List Bool) :
    Function.update (store (buffers w reader todo)) (aux .readTodo) xs=store (buffers w reader xs) := by
  rw [update_aux]
  congr 1
  congr 1
  funext k;cases k <;> simp [buffers]
/-- Actual cache acquisition commutes with reader/counter writes at disjoint physical addresses. -/
theorem put_buffers (w : Words) (r : Reg) (word : SemiprimeRationalBits.RationalWord) (reader todo : List Bool) :
    putReg (buffers w reader todo) r word=buffers (putReg w r word) reader todo := rfl
/-- Actual cache clearing commutes with reader/counter writes at disjoint physical addresses. -/
theorem empty_buffers (w : Words) (r : Reg) (reader todo : List Bool) :
    emptyReg (buffers w reader todo) r=buffers (emptyReg w r) reader todo := rfl
/-- A completed reader restores exactly its actual two originally empty helper words. -/
theorem buffers_self (w : Words) : buffers w (w.auxiliary .reader) (w.auxiliary .readTodo)=w := by
  unfold buffers
  congr 1
  funext k;cases k <;> rfl
/-- Actual two-field drains restore an originally empty cache, regardless of padding/validity. -/
theorem erase_put (w : Words) (r : Reg) (word : SemiprimeRationalBits.RationalWord)
    (hn : w.registers (r,false)=[]) (hd : w.registers (r,true)=[]) : emptyReg (putReg w r word) r=w := by
  dsimp only [emptyReg,putReg]
  congr 1
  funext k
  rcases k with ⟨other,den⟩
  by_cases he:other=r
  · subst other;cases den <;> simp [hn,hd]
  · cases den <;> simp [he]
/-- A real read completion writes its actual TRUE marker for the real caller to pop. -/
def success (w : Words) : Words := {w with auxiliary:=Function.update w.auxiliary .valid [true]}
/-- An actual success-marker push leaves every other word unchanged. -/
theorem update_success (w : Words) (hv : w.auxiliary .valid=[]) :
    Function.update (store w) (aux .valid) (true::w.auxiliary .valid)=store (success w) := by
  rw [hv,update_aux]
  rfl
/-- Original source/cache fields are retained by actual reader-buffer changes. -/
theorem buffers_other (w : Words) (reader todo : List Bool) (k : Aux) (hr : k≠.reader) (ht : k≠.readTodo) :
    (buffers w reader todo).auxiliary k=w.auxiliary k := by simp only [buffers,hr,ht,ite_false]
end RiemannGaussian.SemiprimeD1StackNormalizedInverseReadBuffers
