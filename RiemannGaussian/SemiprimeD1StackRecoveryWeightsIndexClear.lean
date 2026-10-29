/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryWeightsInner
/-! # BOTH actual decreasing-index words are drained even at the zero-term EOF
No missing index reset is represented by a mathematical state shortcut.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRecoveryWeightsIndexClear
open SemiprimeD1StackRecoveryWeights SemiprimeD1StackRecoveryWeightsView
open SemiprimeD1StackRecoveryWeightsCalls SemiprimeD1StackRecoveryWeightsIndices SemiprimeD1StackProcedureTrace
open SemiprimeRationalBits (RationalWord)
/-- Exact mathematical result of the two actual index drains, with every other word retained. -/
def emptied (w:Words):Words:={w with auxiliary:=Function.update (Function.update w.auxiliary .aIndex []) .bIndex []}
/-- Both actual index words, including both final empty tests, are charged before scalar multiplication. -/
theorem clear_run (w:Words):
    Runs program ((w.auxiliary .aIndex).length+1+(w.auxiliary .bIndex).length+1)
      (.local (.clearIndices false)) (bank w) (.local (.scalar false)) (bank (emptied w)):=by
  let first:Words:={w with auxiliary:=Function.update w.auxiliary .aIndex []}
  have h0:=P.drain_loop (.local (.clearIndices false)) (.local (.clearIndices true)) (aux .aIndex) rfl
    (bank w) (w.auxiliary .aIndex) rfl
  rw [update_aux] at h0
  have h1:=P.drain_loop (.local (.clearIndices true)) (.local (.scalar false)) (aux .bIndex) rfl
    (bank first) (w.auxiliary .bIndex) rfl
  rw [update_aux] at h1
  simpa only [first,emptied,Nat.add_assoc] using P.join h0 h1
/-- The last descending-index state restores all originally empty counters literally; the acquired total is retained. -/
theorem clear_indexed (w:Words) (j:Nat) (acc:RationalWord)
    (ht:w.auxiliary .terms=[]) (ha:w.auxiliary .aIndex=[]) (hb:w.auxiliary .bIndex=[]):
    emptied (indexed w 0 0 (j-1) acc)=putReg w .acc acc:=by
  dsimp only [emptied,indexed,putReg,replace,SemiprimeD1StackNormalizedInverseIndices.indexed,
    SemiprimeD1StackNormalizedInverseIndices.counters,SemiprimeD1StackNormalizedInverseView.putReg]
  congr 1
  congr 1
  funext k
  cases k <;> simp [ht,ha,hb,SemiprimeD1StackNormalizedInverseReadBuffers.unary]
end RiemannGaussian.SemiprimeD1StackRecoveryWeightsIndexClear
