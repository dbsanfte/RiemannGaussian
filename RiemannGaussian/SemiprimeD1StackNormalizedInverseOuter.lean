/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseOuterView
/-! # Whole actual coefficient-acquisition loop driven by the original physical q markers -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseOuter
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseCalls SemiprimeD1StackNormalizedInverseReadBuffers
open SemiprimeD1StackNormalizedInverseCoefficient SemiprimeD1StackNormalizedInverseOuterView
open SemiprimeD1StackProcedureTrace
/-- Proof-only exact acquired prefix, not a runtime list/value supplier. -/
def more (a : List SemiprimeRationalBits.RationalWord) (width : List Bool) :
    ℕ→ℕ→List SemiprimeRationalBits.RationalWord→List SemiprimeRationalBits.RationalWord
  | 0,_,reversed=>reversed
  | remaining+1,built,reversed=>more a width remaining (built+1) (nextWord width a reversed built::reversed)
/-- The actual remaining-pop, complete coefficient trace and built-push caps are summed recursively. -/
def outerBound (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    ℕ→ℕ→List SemiprimeRationalBits.RationalWord→ℕ
  | 0,_,_=>1
  | remaining+1,built,reversed=>1+coefficientBound (outer a q width remaining built reversed) a reversed width built+1+
      outerBound a q width remaining (built+1) (nextWord width a reversed built::reversed)
/-- Complete real outer loop: each new coefficient is parsed/computed/framed before its count marker is pushed. -/
theorem outer_run (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool)
    (remaining built : ℕ) (reversed : List SemiprimeRationalBits.RationalWord) (hn : 0<built) :
    ∃t≤outerBound a q width remaining built reversed,
      Runs program t (ctl .outer) (store (outer a q width remaining built reversed)) (ctl .finalTag)
        (store (outer a q width 0 (built+remaining) (more a width remaining built reversed))) := by
  induction remaining generalizing built reversed with
  | zero=>
    have h:=PTrace.pop_run (ctl .outer) (ctl .finalTag) (ctl (.abort 0)) (ctl .copyTerms) (aux .remaining)
      (store (outer a q width 0 built reversed)) [] rfl rfl
    change Runs program 1 _ _ _ (Function.update (store (outer a q width 0 built reversed)) (aux .remaining) (unary 0)) at h
    rw [update_remaining] at h
    refine ⟨1,le_rfl,?_⟩
    exact h
  | succ remaining ih=>
    have h0:=PTrace.pop_run (ctl .outer) (ctl .finalTag) (ctl (.abort 0)) (ctl .copyTerms) (aux .remaining)
      (store (outer a q width (remaining+1) built reversed)) (true::unary remaining) rfl
      (by change unary (remaining+1)=true::unary remaining;exact List.replicate_succ)
    simp only [List.head?_cons,List.tail_cons,SemiprimeD1StackBytecode.choose] at h0
    rw [update_remaining] at h0
    obtain ⟨t1,ht1,h1⟩:=coefficient_run (outer a q width remaining built reversed) a reversed width built hn
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    have h2:=PTrace.push_run (ctl .bump) (ctl .outer) (aux .built) true
      (store (SemiprimeD1StackNormalizedInverseCoefficient.result (outer a q width remaining built reversed)
        (nextWord width a reversed built))) rfl
    change Runs program 1 _ _ _ (Function.update
      (store (SemiprimeD1StackNormalizedInverseCoefficient.result (outer a q width remaining built reversed)
        (nextWord width a reversed built))) (aux .built) (true::unary built)) at h2
    rw [update_built] at h2
    obtain ⟨t3,ht3,h3⟩:=ih (built+1) (nextWord width a reversed built::reversed) (by omega)
    have h:=PTrace.join (PTrace.join (PTrace.join h0 h1) h2) h3
    refine ⟨1+t1+1+t3,?_,?_⟩
    · change 1+t1+1+t3≤1+coefficientBound (outer a q width remaining built reversed) a reversed width built+1+
        outerBound a q width remaining (built+1) (nextWord width a reversed built::reversed)
      omega
    · have he : built+(remaining+1)=(built+1)+remaining := by omega
      simpa only [more,he] using h
end RiemannGaussian.SemiprimeD1StackNormalizedInverseOuter
