/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackNormalizedInverseBootstrap
import RiemannGaussian.SemiprimeD1StackNormalizedInverseMeaning
/-! # Actual complete inverse coefficient acquisition before chronological row reversal -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackNormalizedInverseAcquisition
open SemiprimeD1StackNormalizedInverse SemiprimeD1StackNormalizedInverseView
open SemiprimeD1StackNormalizedInverseCalls SemiprimeD1StackNormalizedInverseReadBuffers
open SemiprimeD1StackNormalizedInverseOuterView SemiprimeD1StackNormalizedInverseBootstrap
open SemiprimeD1StackNormalizedInverseOuter SemiprimeD1StackNormalizedInverseMeaning
open SemiprimeD1StackProcedureTrace
/-- Proof specification of the exact old full array bytes; no source instruction evaluates build. -/
def acquired (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    List SemiprimeRationalBits.RationalWord := (SemiprimeNormalizedInverseBits.build width a.toArray q).words.toList
/-- Own sum of actual bootstrap and complete coefficient-acquisition trace caps. -/
def acquireBound (a : List SemiprimeRationalBits.RationalWord) (width : List Bool) : ℕ→ℕ
  | 0=>7
  | q+1=>5*(q+1)+17+outerBound a (q+1) width q 1 [SemiprimeJetBits.oneWord]
/-- Every output field derives from REAL source reads and REAL R36 calls; only three actual physical inputs are used. -/
theorem acquire_run (a : List SemiprimeRationalBits.RationalWord) (q : ℕ) (width : List Bool) :
    ∃t≤acquireBound a width q,Runs program t (ctl .start) (input (tape a) (unary q) width)
      (ctl .finalTag) (store (outer a q width 0 q (acquired a q width).reverse)) := by
  cases q with
  | zero=>exact ⟨7,le_rfl,zero_run a width⟩
  | succ q=>
    have h0:=positive_run a q width
    obtain ⟨t,ht,h1⟩:=outer_run a (q+1) width q 1 [SemiprimeJetBits.oneWord] (by decide)
    rw [whole_original a width q] at h1
    have hh:1+q=q+1 := by omega
    rw [hh] at h1
    have h:=PTrace.join h0 h1
    exact ⟨5*(q+1)+17+t,Nat.add_le_add_left ht _,h⟩
end RiemannGaussian.SemiprimeD1StackNormalizedInverseAcquisition
