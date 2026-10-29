/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceInterpolationProgramBits
import RiemannGaussian.SemiprimeSourceArrayBackendBudget

/-! # Original-resource bounds for physical source coefficient execution
All widths and code/bank sizes are substituted from original A,Q,R data.
This bounds the joined interpreter/readout and literal/address-acquisition
ledgers; original source construction and scalar compiler generation retain
their separately stated obligations.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeSourceInterpolationProgramBudget
open SemiprimeSourceInterpolationProgramBits SemiprimeSourceArrayProgramCompiler
open SemiprimeSourceArrayProgramBits SemiprimeReportPolynomialGrowth
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes

/-- Original syntax bounds the entire initial literal bank. -/
def bankEnvelope (S : ℕ) : ℕ := 2+SemiprimeSourceInterpolationHeight.nodeCap S
/-- Original syntax and coefficient width bound the actual emitted instruction count. -/
def codeEnvelope (S : ℕ) : ℕ :=
  SemiprimeSourceInterpolationHeight.nodeCap S*((S+1)*((S+1)+1)+(S+1))
/-- All original and newly allocated registers, without a hidden address-space cap. -/
def frontierEnvelope (S : ℕ) : ℕ := bankEnvelope S+codeEnvelope S
/-- Actual binary width is bounded by the frozen original-dimension polynomial. -/
def bitsEnvelope (S : ℕ) : ℕ := SemiprimeSourceInterpolationBits.polynomial S S S
/-- Joined acquisition/interpreter/readout envelope after ORIGINAL resource substitution. -/
def backendEnvelope (S : ℕ) : ℕ :=
  bankEnvelope S*(8*(bitsEnvelope S+1)+16)+1+
    codeEnvelope S*(8*(frontierEnvelope S+1)+17)+1+2*(bitsEnvelope S+1)+5+
    4*(frontierEnvelope S+1)+10+
    (codeEnvelope S*(SemiprimeSourceProgramBits.stepBudget (frontierEnvelope S)
      (bitsEnvelope S+1) (frontierEnvelope S+1)+3)+1+
      (frontierEnvelope S+1)*(8*(bitsEnvelope S+1)+15*(frontierEnvelope S+1)+30)+2)

/-- Every dimension in the actual execution envelope is bounded by original data. -/
theorem source_resources {r Q : ℕ} (A R S : ℕ) (a y : UniversalType r Q 1)
    (hA : A ≤ S) (hQ : Q ≤ S) (hR : R ≤ S) :
    (bank (source A R a y)).length ≤ bankEnvelope S ∧
      (program (R+1) (source A R a y)).code.length ≤ codeEnvelope S ∧
      frontier (R+1) (source A R a y) ≤ frontierEnvelope S ∧
      SemiprimeSourceInterpolationBits.stateBits A Q R ≤ bitsEnvelope S := by
  have hd := source_dimensions A R a y
  have hnode : SemiprimeSourceInterpolationHeight.nodeCap Q ≤
      SemiprimeSourceInterpolationHeight.nodeCap S := by
    unfold SemiprimeSourceInterpolationHeight.nodeCap
    gcongr
  have hb : (bank (source A R a y)).length ≤ bankEnvelope S :=
    hd.1.trans (Nat.add_le_add_left hnode 2)
  have hc : (program (R+1) (source A R a y)).code.length ≤ codeEnvelope S := by
    apply hd.2.trans
    unfold codeEnvelope
    gcongr
  refine ⟨hb,hc,Nat.add_le_add hb hc,?_⟩
  exact (SemiprimeSourceInterpolationBits.stateBits_le_polynomial A Q R).trans
    (SemiprimeSourceInterpolationBits.polynomial_mono hA hQ hR)

/-- The executed original coefficient backend has a fixed resource-only work envelope. -/
theorem acquire_backend_work {r Q : ℕ} (A R S : ℕ) (a y : UniversalType r Q 1)
    (k : ℕ) (hA : A ≤ S) (hQ : Q ≤ S) (hR : R ≤ S) :
    (acquire A R a y k).acquisitionWork+(acquire A R a y k).bitWork ≤ backendEnvelope S := by
  have hs := source_resources A R S a y hA hQ hR
  have h := coefficient_work (SemiprimeSourceInterpolationBits.stateBits A Q R)
    (R+1) (source A R a y) k
  apply (Nat.add_le_add h.1 h.2).trans
  exact SemiprimeSourceArrayBackendBudget.envelope_mono hs.1 hs.2.1 hs.2.2.1 hs.2.2.2

/-- Input-independent constants bound the COMPLETE displayed backend envelope. -/
theorem backend_monomial : ∃ C k : ℕ,∀ S,backendEnvelope S ≤ C*(S+1)^k := by
  change Bound (fun S => backendEnvelope S)
  simp only [backendEnvelope,SemiprimeSourceProgramBits.stepBudget,frontierEnvelope,
    bankEnvelope,codeEnvelope,bitsEnvelope,SemiprimeSourceInterpolationBits.polynomial,
    SemiprimeSourceInterpolationHeight.nodeCap]
  boundArithmetic

end RiemannGaussian.SemiprimeSourceInterpolationProgramBudget
