/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineOperationOutput
/-! # Exact physical slope-row reversal buffers and restored scalar cache -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeBuffers
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
/-- Only actual forward reader and reversed-row output change during slope acquisition. -/
def buffers (w:Words) (reader reversed:List Bool):Words:=
  {w with added:=fun slot=>if slot=.reader then reader else if slot=.reverseSlopes then reversed else w.added slot}
/-- A real reader write preserves the entire original bank and every accumulated reversed row. -/
theorem update_reader (w:Words) (reader reversed xs:List Bool):
    Function.update (bank (buffers w reader reversed)) (aux .reader) xs=bank (buffers w xs reversed):=by
  rw [update_added]
  congr 1
  congr 1
  funext slot
  cases slot <;> simp [buffers]
/-- A real frame/tag write preserves the unread forward suffix and every other110 word. -/
theorem update_reversed (w:Words) (reader reversed xs:List Bool):
    Function.update (bank (buffers w reader reversed)) (aux .reverseSlopes) xs=bank (buffers w reader xs):=by
  rw [update_added]
  congr 1
  congr 1
  funext slot
  cases slot <;> simp [buffers]
/-- Acquired scalar caches and added physical row buffers are disjoint actual data roles. -/
theorem put_buffers (w:Words) (r:SemiprimeD1StackRecoveryGrid.Reg) (x:SemiprimeRationalBits.RationalWord) (reader reversed:List Bool):
    putReg (buffers w reader reversed) r x=buffers (putReg w r x) reader reversed:=rfl
/-- Both literal signed/denominator drains restore the original EMPTY slope cache, including W0. -/
theorem erase_put (w:Words) (x:SemiprimeRationalBits.RationalWord)
    (hn:w.registers (.slope,false)=[]) (hd:w.registers (.slope,true)=[]):
    SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg (putReg w .slope x) .slope=w:=by
  dsimp only [SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg,putReg]
  congr 1
  congr 1
  funext slot
  rcases slot with ⟨r,b⟩
  cases r <;> cases b <;> simp [hn,hd]
/-- The two row buffers initially equal their actual existing physical words. -/
theorem buffers_self (w:Words):buffers w (w.added .reader) (w.added .reverseSlopes)=w:=by
  unfold buffers
  congr 1
  funext slot
  cases slot <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryAffineSlopeBuffers
