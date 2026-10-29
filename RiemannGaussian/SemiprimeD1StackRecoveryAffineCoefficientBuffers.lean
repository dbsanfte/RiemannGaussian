/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineOperationOutput
/-! # Exact physical descending coefficient framing buffers and restored dot suffix cache -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientBuffers
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
/-- Only actual forward remaining and next-row output change during slope acquisition. -/
def buffers (w:Words) (remaining next:List Bool):Words:=
  {w with added:=fun slot=>if slot=.remaining then remaining else if slot=.nextArray then next else w.added slot}
/-- A real remaining write preserves the entire original bank and every accumulated next row. -/
theorem update_remaining (w:Words) (remaining next xs:List Bool):
    Function.update (bank (buffers w remaining next)) (aux .remaining) xs=bank (buffers w xs next):=by
  rw [update_added]
  congr 1
  congr 1
  funext slot
  cases slot <;> simp [buffers]
/-- A real frame/tag write preserves the unread forward suffix and every other110 word. -/
theorem update_next (w:Words) (remaining next xs:List Bool):
    Function.update (bank (buffers w remaining next)) (aux .nextArray) xs=bank (buffers w remaining xs):=by
  rw [update_added]
  congr 1
  congr 1
  funext slot
  cases slot <;> simp [buffers]
/-- Acquired scalar caches and added physical row buffers are disjoint actual data roles. -/
theorem put_buffers (w:Words) (r:SemiprimeD1StackRecoveryGrid.Reg) (x:SemiprimeRationalBits.RationalWord) (remaining next:List Bool):
    putReg (buffers w remaining next) r x=buffers (putReg w r x) remaining next:=rfl
/-- Both literal signed/denominator drains restore the original EMPTY slope cache, including W0. -/
theorem erase_put (w:Words) (x:SemiprimeRationalBits.RationalWord)
    (hn:w.registers (.denPower,false)=[]) (hd:w.registers (.denPower,true)=[]):
    SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg (putReg w .denPower x) .denPower=w:=by
  dsimp only [SemiprimeD1StackRecoveryAffineOperationOutput.emptyReg,putReg]
  congr 1
  congr 1
  funext slot
  rcases slot with ⟨r,b⟩
  cases r <;> cases b <;> simp [hn,hd]
/-- The two row buffers initially equal their actual existing physical words. -/
theorem buffers_self (w:Words):buffers w (w.added .remaining) (w.added .nextArray)=w:=by
  unfold buffers
  congr 1
  funext slot
  cases slot <;> rfl
end RiemannGaussian.SemiprimeD1StackRecoveryAffineCoefficientBuffers
