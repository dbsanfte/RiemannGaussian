/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOuterView
import RiemannGaussian.SemiprimeD1StackNormalizedInverseSeed
/-! # Honest three-input physical bootstrap and literal initial ONE -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseBootstrap
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseCalls SemiprimeD1StackNormalizedInverseReadBuffers
open SemiprimeD1StackNormalizedInverseOuterView SemiprimeD1StackNormalizedInverseSeed
open SemiprimeD1StackProcedureTrace
/-- The actual two FALSE array terminators and original-q preserving copy initialize the source. -/
theorem initialize_run (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    Runs program (5*q+6) (ctl .start) (input (tape a) (unary q) width) (ctl .first)
      (store (outer a q width q 0 [])) := by
  let base:=originals (tape a) (unary q) width
  let first : Words := {base with auxiliary:=Function.update base.auxiliary .output [false]}
  let second : Words := {first with auxiliary:=Function.update first.auxiliary .prefixReverse [false]}
  have h0:=PTrace.push_run (ctl .start) (ctl .seedPrefix) (aux .output) false (store base) rfl
  change Runs program 1 _ _ _ (Function.update (store base) (aux .output) [false]) at h0
  rw [update_aux] at h0
  have h1:=PTrace.push_run (ctl .seedPrefix) (ctl .copyRemaining) (aux .prefixReverse) false (store first) rfl
  change Runs program 1 _ _ _ (Function.update (store first) (aux .prefixReverse) [false]) at h1
  rw [update_aux] at h1
  have h2:=PTrace.copy_call .remaining (ctl .copyRemaining) (ctl .first) rfl (store second) (unary q) [] rfl rfl rfl
  change Runs program _ _ _ _ (Function.update (store second) (aux .remaining) (unary q++[])) at h2
  rw [List.append_nil,update_aux] at h2
  have he : ({second with auxiliary:=Function.update second.auxiliary .remaining (unary q)}:Words)=outer a q width q 0 [] := by
    apply congrArg (fun f=>({base with auxiliary:=f}:Words))
    funext k;cases k <;> rfl
  rw [he] at h2
  have h:=PTrace.join (PTrace.join h0 h1) h2
  convert h using 1 <;> first | rfl | (simp only [unary,List.length_replicate];omega)
/-- Zero requested coefficients reach the real final row loop with exactly the EMPTY array codec. -/
theorem zero_run (a : List SemiprimeRationalBits.RationalWord) (width : List Bool) :
    Runs program 7 (ctl .start) (input (tape a) [] width) (ctl .finalTag)
      (store (outer a 0 width 0 0 [])) := by
  have h0:=initialize_run a 0 width
  have h1:=PTrace.pop_run (ctl .first) (ctl .finalTag) (ctl (.abort 0)) (ctl (.seedOne 0)) (aux .remaining)
    (store (outer a 0 width 0 0 [])) [] rfl rfl
  change Runs program 1 _ _ _ (Function.update (store (outer a 0 width 0 0 [])) (aux .remaining) (unary 0)) at h1
  rw [update_remaining] at h1
  exact PTrace.join h0 h1
/-- Positive q seeds literal ONE WITHOUT reading a0 or W, then actually acquires the first built-count marker. -/
theorem positive_run (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    Runs program (5*(q+1)+17) (ctl .start) (input (tape a) (unary (q+1)) width) (ctl .outer)
      (store (outer a (q+1) width q 1 [SemiprimeJetBits.oneWord])) := by
  have h0:=initialize_run a (q+1) width
  have h1:=PTrace.pop_run (ctl .first) (ctl .finalTag) (ctl (.abort 0)) (ctl (.seedOne 0)) (aux .remaining)
    (store (outer a (q+1) width (q+1) 0 [])) (true::unary q) rfl rfl
  simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h1
  rw [update_remaining] at h1
  have h2:=one_run (outer a (q+1) width q 0 [])
  let seeded:=SemiprimeD1StackNormalizedInverseCoefficient.result (outer a (q+1) width q 0 []) SemiprimeJetBits.oneWord
  have h3:=PTrace.push_run (ctl .bump) (ctl .outer) (aux .built) true (store seeded) rfl
  change Runs program 1 _ _ _ (Function.update (store seeded) (aux .built) (true::unary 0)) at h3
  rw [update_built] at h3
  have h:=PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
  convert h using 1
end RiemannGaussian.SemiprimeD1StackNormalizedInverseBootstrap
