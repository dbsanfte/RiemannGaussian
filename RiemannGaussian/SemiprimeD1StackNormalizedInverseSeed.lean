/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseCalls
/-! # Nine actual literal ONE-row bytes, independent of the denominator and W -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseSeed
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseCalls SemiprimeD1StackProcedureTrace
/-- The native initial ONE is acquired by nine actual pushes even when W=0; a0 is never read. -/
theorem one_run (w : Words) :
    Runs program 9 (ctl (.seedOne 0)) (store w) (ctl .bump)
      (store {w with auxiliary:=Function.update w.auxiliary .prefixReverse (row SemiprimeJetBits.oneWord (w.auxiliary .prefixReverse))}) := by
  let w1 : Words := {w with auxiliary:=Function.update w.auxiliary .prefixReverse (false::w.auxiliary .prefixReverse)}
  have h0:=PTrace.push_run (ctl (.seedOne 0)) (ctl (.seedOne 1)) (aux .prefixReverse) false (store w) rfl
  change Runs program 1 _ _ _ (Function.update (store w) (aux .prefixReverse) (false::w.auxiliary .prefixReverse)) at h0
  rw [update_aux] at h0
  let w2 : Words := {w1 with auxiliary:=Function.update w1.auxiliary .prefixReverse (true::w1.auxiliary .prefixReverse)}
  have h1:=PTrace.push_run (ctl (.seedOne 1)) (ctl (.seedOne 2)) (aux .prefixReverse) true (store w1) rfl
  change Runs program 1 _ _ _ (Function.update (store w1) (aux .prefixReverse) (true::w1.auxiliary .prefixReverse)) at h1
  rw [update_aux] at h1
  let w3 : Words := {w2 with auxiliary:=Function.update w2.auxiliary .prefixReverse (true::w2.auxiliary .prefixReverse)}
  have h2:=PTrace.push_run (ctl (.seedOne 2)) (ctl (.seedOne 3)) (aux .prefixReverse) true (store w2) rfl
  change Runs program 1 _ _ _ (Function.update (store w2) (aux .prefixReverse) (true::w2.auxiliary .prefixReverse)) at h2
  rw [update_aux] at h2
  let w4 : Words := {w3 with auxiliary:=Function.update w3.auxiliary .prefixReverse (false::w3.auxiliary .prefixReverse)}
  have h3:=PTrace.push_run (ctl (.seedOne 3)) (ctl (.seedOne 4)) (aux .prefixReverse) false (store w3) rfl
  change Runs program 1 _ _ _ (Function.update (store w3) (aux .prefixReverse) (false::w3.auxiliary .prefixReverse)) at h3
  rw [update_aux] at h3
  let w5 : Words := {w4 with auxiliary:=Function.update w4.auxiliary .prefixReverse (true::w4.auxiliary .prefixReverse)}
  have h4:=PTrace.push_run (ctl (.seedOne 4)) (ctl (.seedOne 5)) (aux .prefixReverse) true (store w4) rfl
  change Runs program 1 _ _ _ (Function.update (store w4) (aux .prefixReverse) (true::w4.auxiliary .prefixReverse)) at h4
  rw [update_aux] at h4
  let w6 : Words := {w5 with auxiliary:=Function.update w5.auxiliary .prefixReverse (true::w5.auxiliary .prefixReverse)}
  have h5:=PTrace.push_run (ctl (.seedOne 5)) (ctl (.seedOne 6)) (aux .prefixReverse) true (store w5) rfl
  change Runs program 1 _ _ _ (Function.update (store w5) (aux .prefixReverse) (true::w5.auxiliary .prefixReverse)) at h5
  rw [update_aux] at h5
  let w7 : Words := {w6 with auxiliary:=Function.update w6.auxiliary .prefixReverse (false::w6.auxiliary .prefixReverse)}
  have h6:=PTrace.push_run (ctl (.seedOne 6)) (ctl (.seedOne 7)) (aux .prefixReverse) false (store w6) rfl
  change Runs program 1 _ _ _ (Function.update (store w6) (aux .prefixReverse) (false::w6.auxiliary .prefixReverse)) at h6
  rw [update_aux] at h6
  let w8 : Words := {w7 with auxiliary:=Function.update w7.auxiliary .prefixReverse (true::w7.auxiliary .prefixReverse)}
  have h7:=PTrace.push_run (ctl (.seedOne 7)) (ctl (.seedOne 8)) (aux .prefixReverse) true (store w7) rfl
  change Runs program 1 _ _ _ (Function.update (store w7) (aux .prefixReverse) (true::w7.auxiliary .prefixReverse)) at h7
  rw [update_aux] at h7
  let w9 : Words := {w8 with auxiliary:=Function.update w8.auxiliary .prefixReverse (true::w8.auxiliary .prefixReverse)}
  have h8:=PTrace.push_run (ctl (.seedOne 8)) (ctl .bump) (aux .prefixReverse) true (store w8) rfl
  change Runs program 1 _ _ _ (Function.update (store w8) (aux .prefixReverse) (true::w8.auxiliary .prefixReverse)) at h8
  rw [update_aux] at h8
  have h:=(PTrace.join (PTrace.join (PTrace.join (PTrace.join (PTrace.join (PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3) h4) h5) h6) h7) h8)
  have he : w9={w with auxiliary:=Function.update w.auxiliary .prefixReverse (row SemiprimeJetBits.oneWord (w.auxiliary .prefixReverse))} := by
    dsimp only [w9,w8,w7,w6,w5,w4,w3,w2,w1]
    simp only [Function.update_self,Function.update_idem]
    rfl
  change Runs program 9 _ _ _ (store w9) at h
  rw [he] at h
  exact h
end RiemannGaussian.SemiprimeD1StackNormalizedInverseSeed
