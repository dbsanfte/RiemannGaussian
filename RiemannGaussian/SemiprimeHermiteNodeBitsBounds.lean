/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteNodeBits
import RiemannGaussian.SemiprimeNormalizedInverseBitsBounds
import RiemannGaussian.SemiprimeHermiteEvaluationBitsBounds

/-! # Complete physical arithmetic and cell budget for an intrinsic Hermite node
Every acquired input, cached stage and the supplied packet report survives.
These bounds concern the actual node and require no intermediate Fits advice.
Source packet production and literal address/tape execution remain separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace RiemannGaussian.SemiprimeHermiteNodeBitsBounds
open SemiprimeRationalBits SemiprimeJetBits SemiprimeHermiteNodeBits

/-- The exact quotient-stage uniform convolution allowance. -/
def quotientBudget (W A J : ℕ) : ℕ :=
  J*(J*(40000*(W+1)^3+4)+4+
    J*((A+1)*(2*W+3)+(J+1)*(2*W+3)))+(2*J+1)

/-- Closed polynomial budget for all stages after the acquired packet. -/
def budget (W A Q J : ℕ) : ℕ :=
  SemiprimeCardinalInputBits.budget Q J+
  (4+Q*J*SemiprimeAffineJetBits.stepBudget W J)+
  (4+Q*J*(60000*(W+1)^3+8*W+12))+
  (1+J*SemiprimeNormalizedInverseBitsBounds.stepBudget W (J+1) J)+
  quotientBudget W A J+
  (4+J*(60000*(W+1)^3+(J+1)*(2*W+3)+8*W+12))+
  20000*(W+1)^3+control W Q J

/-- The final instruction always returns the selected physical storage width. -/
theorem node_width (template : List Bool) (Q J : ℕ) (t : Fin Q) (H : JetReport) :
    Width (node template Q J t H).word template.length := by
  exact SemiprimeHermiteEvaluationBitsBounds.operation_width _ _ _ _

/-- Every actual node stage, including H.clock, is retained by the polynomial bound. -/
theorem node_clock (template : List Bool) (Q J : ℕ) (t : Fin Q) (H : JetReport)
    (A : ℕ) (hW : Q+2≤template.length) (hsize : H.words.size≤A)
    (hH : Bounded H.words template.length) :
    (node template Q J t H).clock≤H.clock+budget template.length A Q J := by
  let inputs := SemiprimeCardinalInputBits.acquire Q J t
  let cardinal := SemiprimeAffineJetBits.build template J inputs.slopes
  let atZero := SemiprimeHermiteEvaluationBits.affineValue template inputs.x inputs.slopes
  let inverse := SemiprimeNormalizedInverseBits.build template cardinal.words J
  let quotient := multiplyBits template H.words inverse.words J
  let evaluation := SemiprimeHermiteEvaluationBits.evalPrefix template quotient.words inputs.x J
  have ht : 0<template.length := by omega
  have hs (c : RationalWord) (hc : c∈inputs.slopes) : Width c template.length := by
    have hw := SemiprimeCardinalInputBits.slopes_bounded Q J t c hc
    exact ⟨hw.1.trans hW,hw.2.trans hW⟩
  have hx : Width inputs.x template.length := by
    have hw := SemiprimeCardinalInputBits.x_bounded Q J t
    exact ⟨hw.1.trans hW,hw.2.trans hW⟩
  have hsl : inputs.slopes.length=Q*J := SemiprimeCardinalInputBits.slopes_length Q J t
  have hic := SemiprimeCardinalInputBits.acquire_clock Q J t
  have hcc := SemiprimeAffineJetBits.build_clock template J inputs.slopes ht hs
  rw [hsl] at hcc
  have hcb : Bounded cardinal.words template.length := SemiprimeAffineJetBits.build_bounded _ _ _ ht
  have hcs : cardinal.words.size≤J+1 := by
    dsimp only [cardinal]
    rw [SemiprimeAffineJetBits.build_size]
    split <;> omega
  have hac := SemiprimeHermiteEvaluationBitsBounds.affineValue_clock template inputs.x inputs.slopes ht hx hs
  rw [hsl] at hac
  have hinv := SemiprimeNormalizedInverseBitsBounds.build_clock template ht cardinal.words (J+1) J hcs hcb J le_rfl
  have hib : Bounded inverse.words template.length := SemiprimeNormalizedInverseBits.build_bounded _ ht _ _
  have his : inverse.words.size=J := SemiprimeNormalizedInverseBits.build_size _ _ _
  have hqc := multiplyBits_cost template ht H.words inverse.words J hH hib
  have hqc' : quotient.clock≤quotientBudget template.length A J := by
    apply hqc.trans
    unfold quotientBudget accessCost
    rw [his]
    gcongr
  have hqb : Bounded quotient.words template.length := multiplyBits_bounded template ht _ _ J
  have hqs : quotient.words.size=J := multiplyBits_size _ _ _ _
  have hec := SemiprimeHermiteEvaluationBitsBounds.evalPrefix_clock template quotient.words inputs.x J ht hqb hx
  have hec' : evaluation.clock≤4+J*(60000*(template.length+1)^3+
      (J+1)*(2*template.length+3)+8*template.length+12) := by
    simpa only [accessCost,hqs] using hec
  have hew := SemiprimeHermiteEvaluationBitsBounds.evalPrefix_width template quotient.words inputs.x J ht
  have haw := SemiprimeHermiteEvaluationBitsBounds.affineValue_width template inputs.x inputs.slopes ht
  have hoc := executeOperation_cost .mul atZero.word evaluation.word template haw hew.1 le_rfl
  change H.clock+inputs.clock+cardinal.clock+atZero.clock+inverse.clock+
    quotient.clock+evaluation.clock+(executeOperation .mul atZero.word evaluation.word template).clock+
    control template.length Q J≤_
  change inputs.clock≤_ at hic
  change cardinal.clock≤_ at hcc
  change atZero.clock≤_ at hac
  change inverse.clock≤_ at hinv
  unfold budget
  omega

end RiemannGaussian.SemiprimeHermiteNodeBitsBounds
