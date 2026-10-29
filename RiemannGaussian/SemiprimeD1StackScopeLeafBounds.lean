/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackScopeLeafExecution
/-! # Actual scope-derived leaf cost; no supplied cardinality or width answer -/
set_option autoImplicit false
set_option synthInstance.maxSize 131072
set_option maxRecDepth 32768
set_option maxHeartbeats 2500000
namespace RiemannGaussian.SemiprimeD1StackScopeLeafBounds
open SemiprimeD1StackScopeLeaf
open SemiprimeD1TensorTapeCodec (vectorBits)
open SemiprimeD1StackUnaryDivmod (unary)

/-- Counting every actual framed record is bounded by physical bank inventory,
including empty and zero-valued fields, without any key-width premise. -/
theorem scope_length_le (scopeWords : List (List Bool)) : scopeWords.length≤(vectorBits scopeWords).length := by
  rw [SemiprimeD1TensorTapeCodec.vectorBits_length]
  omega
/-- Original literal input/context inventory, with NO assignment-width value or
binary M header. Scope cardinality is derived from the actual scope tape. -/
def resource (ctx : SemiprimeD1JetAxes.Context) (pBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (scopeWords : List (List Bool)) : ℕ :=
  ctx.rank+ctx.precision+ctx.axes.length+(vectorBits (ctx.axes.map unary)).length+
    pBits.length+(SemiprimeD1StackVertexProduct.records vertices).length+(vectorBits scopeWords).length+1
/-- Pure polynomial overhead of scope counting and the actual unary-ready leaf. -/
def polynomial (S : ℕ) : ℕ := SemiprimeD1StackLeafUniform.polynomial S+11*S+20

/-- The original numeric polynomial is monotone. This pure arithmetic theorem
has no execution/cost/entry premise and transfers no runtime report. -/
theorem leaf_polynomial_mono {S T : ℕ} (h : S≤T) :
    SemiprimeD1StackLeafUniform.polynomial S≤SemiprimeD1StackLeafUniform.polynomial T := by
  unfold SemiprimeD1StackLeafUniform.polynomial SemiprimeD1StackLeafUniform.overhead
    SemiprimeD1StackLeafPolynomial.roundPolynomial
    SemiprimeD1StackVertexProductPolynomial.preparedPolynomial
    SemiprimeD1StackVertexProductPolynomial.roundPolynomial SemiprimeD1StackVertexProductPolynomial.vectorBound
  gcongr

/-- All original numeric dimensions formerly counted separately are covered by
the actual physical scope-bank inventory, not an advised cardinality field. -/
theorem leaf_resource_le (ctx : SemiprimeD1JetAxes.Context) (pBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (scopeWords : List (List Bool)) :
    SemiprimeD1StackLeafUniform.resource scopeWords.length ctx pBits [] vertices≤resource ctx pBits vertices scopeWords := by
  have hs:=scope_length_le scopeWords
  unfold SemiprimeD1StackLeafUniform.resource resource
  simp only [List.length_nil]
  omega

/-- Numerical majorization of the NEW actual stage budget. Only a nonnegative
pure polynomial expression is reused; no old/new execution clock is identified. -/
theorem budget_numeric_le (ctx : SemiprimeD1JetAxes.Context) (pBits : List Bool)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (scopeWords : List (List Bool)) :
    SemiprimeD1StackScopeLeafExecution.budget ctx pBits vertices scopeWords≤
      SemiprimeD1StackLeafExecution.budget scopeWords.length ctx pBits [] vertices+
        11*(vectorBits scopeWords).length+20 := by
  have h:=SemiprimeD1StackScopeLeafReady.budget_le_enumerated scopeWords.length ctx vertices
    (SemiprimeD1StackScopeLeafExecution.ready ctx pBits vertices) (SemiprimeD1StackLeafExecution.originalValues [])
  dsimp only [SemiprimeD1StackScopeLeafExecution.budget,SemiprimeD1StackLeafExecution.budget,
    SemiprimeD1StackScopeLeafExecution.ready] at h ⊢
  omega

/-- Closed actual original-data budget, with fixed polynomial overhead and the
actual 2^(number of scope records) assignment count. No count/Fits/cost oracle. -/
theorem budget_le (ctx : SemiprimeD1JetAxes.Context) (pBits : List Bool)
    (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (hg : SemiprimeD1LeafCounter.Good ctx vertices)
    (scopeWords : List (List Bool)) :
    SemiprimeD1StackScopeLeafExecution.budget ctx pBits vertices scopeWords≤
      polynomial (resource ctx pBits vertices scopeWords)*2^scopeWords.length := by
  let S:=resource ctx pBits vertices scopeWords
  have hnum:=budget_numeric_le ctx pBits vertices scopeWords
  have hold:=SemiprimeD1StackLeafUniform.budget_le scopeWords.length ctx pBits [] hprecision vertices hg
  have hmono:=leaf_polynomial_mono (leaf_resource_le ctx pBits vertices scopeWords)
  have hmul:=Nat.mul_le_mul_right (2^scopeWords.length) hmono
  have hs : (vectorBits scopeWords).length≤S := by dsimp [S,resource];omega
  have hpow : 1≤(2:ℕ)^scopeWords.length := by
    have hp : (0:ℕ)<2^scopeWords.length := by positivity
    omega
  have hscale:=Nat.mul_le_mul_left (11*S+20) hpow
  change _≤polynomial S*2^scopeWords.length
  unfold polynomial
  nlinarith

/-- Fixed constants and degree chosen before every original header, scope bank
and literal tensor network. This is not a mere polynomial label. -/
theorem polynomial_monomial : ∃ C k : ℕ, ∀S,polynomial S≤C*(S+1)^k := by
  change SemiprimeReportPolynomialGrowth.Bound polynomial
  have h : SemiprimeReportPolynomialGrowth.Bound SemiprimeD1StackLeafUniform.polynomial :=
    SemiprimeD1StackLeafMachine.polynomial_monomial
  exact SemiprimeReportPolynomialGrowth.add_bound
    (SemiprimeReportPolynomialGrowth.add_bound h
      (SemiprimeReportPolynomialGrowth.mul_bound (SemiprimeReportPolynomialGrowth.constant_bound 11)
        SemiprimeReportPolynomialGrowth.identity_bound))
    (SemiprimeReportPolynomialGrowth.constant_bound 20)

/-- Complete actual scope-derived source trace under original data invariants. -/
theorem source_run_polynomial (ctx : SemiprimeD1JetAxes.Context) (hp : ctx.Positive) (pBits : List Bool)
    (hprecision : SemiprimeBitArithmetic.bitValue pBits=ctx.precision)
    (vertices : List SemiprimeD1LeafCounter.Vertex) (hg : SemiprimeD1LeafCounter.Good ctx vertices)
    (scopeWords : List (List Bool)) :
    ∃ m≤polynomial (resource ctx pBits vertices scopeWords)*2^scopeWords.length,
      SemiprimeD1StackCalls.run program m
        (initial (vectorBits (ctx.axes.map unary)) pBits (SemiprimeD1StackVertexProduct.records vertices) (vectorBits scopeWords))=
      some (⟨none,none,none,SemiprimeD1StackScopeLeafExecution.finalData ctx pBits vertices scopeWords,[]⟩:
        SemiprimeD1StackCalls.State Stack Label) := by
  obtain ⟨m,hm,hs⟩:=SemiprimeD1StackScopeLeafExecution.source_run ctx hp pBits hprecision vertices scopeWords
  exact ⟨m,hm.trans (budget_le ctx pBits hprecision vertices hg scopeWords),hs⟩

end RiemannGaussian.SemiprimeD1StackScopeLeafBounds
