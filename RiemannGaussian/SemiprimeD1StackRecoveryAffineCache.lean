/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryAffineRegisters
import RiemannGaussian.SemiprimeD1StackRecoveryAffineReadCount
/-! # Exact disjoint actual cache/counter writes used by the affine loop -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryAffineCache
open SemiprimeD1StackRecoveryAffine SemiprimeD1StackRecoveryAffineView
open SemiprimeD1StackRecoveryGrid (Reg)
/-- Actual writes to two distinct physical cache pairs commute literally, without changing raw bytes. -/
theorem putReg_comm (w:Words) (r s:Reg) (x y:SemiprimeRationalBits.RationalWord) (hne:r≠s):
    putReg (putReg w r x) s y=putReg (putReg w s y) r x:=by
  dsimp only [putReg]
  congr 1
  congr 1
  funext slot
  rcases slot with ⟨q,b⟩
  by_cases hr:q=r
  · subst q
    cases b <;> simp [hne]
  · by_cases hs:q=s
    · subst q
      cases b <;> simp [Ne.symm hne]
    · cases b <;> simp [hr,hs]
/-- The physically decremented k word, not a numerical control register. -/
def counter (w:Words) (n:Nat):Words:=
  {w with added:=Function.update w.added .k (SemiprimeD1StackRecoveryAffineReadCount.unary n)}
/-- Rational-cache writes and the actual byte-index write use distinct physical cells. -/
theorem put_counter (w:Words) (n:Nat) (r:Reg) (x:SemiprimeRationalBits.RationalWord):
    putReg (counter w n) r x=counter (putReg w r x) n:=rfl
/-- Each actual k pop replaces only its physical marker word. -/
theorem update_counter (w:Words) (n m:Nat):
    Function.update (bank (counter w n)) (aux .k) (SemiprimeD1StackRecoveryAffineReadCount.unary m)=bank (counter w m):=by
  rw [update_added]
  simp only [counter,Function.update_idem]
end RiemannGaussian.SemiprimeD1StackRecoveryAffineCache
