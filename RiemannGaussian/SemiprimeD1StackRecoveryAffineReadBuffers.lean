/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineOperationOutput
/-! # Actual array-reader and byte-count words, with all other110 roles retained -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineReadBuffers
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
/-- Proof invariant over the two physically changing reader words. -/
def buffers (w:Words) (reader todo:List Bool):Words:=
  {w with added:=fun slot=>if slot=.reader then reader else if slot=.readTodo then todo else w.added slot}
/-- Actual array-reader write touches no retained coefficient/count/metadata cell. -/
theorem update_reader (w:Words) (reader todo xs:List Bool):
    Function.update (bank (buffers w reader todo)) (aux .reader) xs=bank (buffers w xs todo):=by
  rw [update_added]
  congr 1
  congr 1
  funext slot
  cases slot <;> simp [buffers]
/-- Actual unary byte-index consumption is physically represented and paid. -/
theorem update_todo (w:Words) (reader todo xs:List Bool):
    Function.update (bank (buffers w reader todo)) (aux .readTodo) xs=bank (buffers w reader xs):=by
  rw [update_added]
  congr 1
  congr 1
  funext slot
  cases slot <;> simp [buffers]
/-- Acquired signed coefficient caches and both private reader words are disjoint. -/
theorem put_buffers (w:Words) (r:SemiprimeD1StackRecoveryGrid.Reg) (x:SemiprimeRationalBits.RationalWord) (reader todo:List Bool):
    putReg (buffers w reader todo) r x=buffers (putReg w r x) reader todo:=rfl
/-- Real drains restore an initially EMPTY coefficient cache without altering the other110 words. -/
theorem erase_put (w:Words) (x:SemiprimeRationalBits.RationalWord)
    (hn:w.registers (.numBase,false)=[]) (hd:w.registers (.numBase,true)=[]):
    SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg (putReg w .numBase x) .numBase=w:=by
  dsimp only [SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg,putReg]
  congr 1
  congr 1
  funext slot
  rcases slot with ⟨r,b⟩
  cases r <;> cases b <;> simp [hn,hd]
/-- The reader-view identity never inserts an unacquired runtime word. -/
theorem buffers_self (w:Words):buffers w (w.added .reader) (w.added .readTodo)=w:=by
  unfold buffers
  congr 1
  funext slot
  cases slot <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryAffineReadBuffers
