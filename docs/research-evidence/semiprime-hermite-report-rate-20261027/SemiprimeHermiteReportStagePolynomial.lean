/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteBitsSetupBudget
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Explicit separated-cardinality polynomials for physical Hermite packets
Only original LOCAL and HEAD powers occur, represented by independent paid
resources. No power of a common dimension bound replaces either cardinality.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace RiemannGaussian.SemiprimeHermiteReportStagePolynomial
open scoped BigOperators
open SemiprimeNodeArrayExecution (RuntimeDesign)

/-- Original source width has a fixed polynomial resource envelope. -/
def inputEnvelope (S : ℕ) : ℕ := SemiprimeNativeInputBits.polynomial S S S S S

/-- Actual computed input bits are bounded, rather than assumed at resource scale. -/
theorem inputBits_le_envelope (n B Q R J S : ℕ)
    (hn : n ≤ S) (hB : B ≤ S) (hQ : Q ≤ S) (hR : R ≤ S) (hJ : J ≤ S) :
    SemiprimeNativeInputBits.inputBits n B Q R J ≤ inputEnvelope S := by
  apply (SemiprimeNativeInputBits.inputBits_le_polynomial n B Q R J).trans
  unfold inputEnvelope SemiprimeNativeInputBits.polynomial
  gcongr

/-- Physical group polynomial with its actual local truth count separated. -/
def groupPolynomial (n F R J b s w A E Ew : ℕ) : ℕ :=
  let W := SemiprimeNativeGroupBits.groupWidth b R F s
  let loc := w*SemiprimeCorrectedPortBitsBounds.portBudget W A R J n+
    Ew*(E+(w+1)*SemiprimeLocalBitsBounds.nodeBudget J W)+
    (20*(w+1)*(J+1)*(W+1)*(Ew+1)+10*w+10)
  F*(loc+(3*J+1)+SemiprimeNativeGroupBitsBudget.multiplyBudget W J+J+3)+
    (3*J+1)+SemiprimeNativeGroupBits.groupControl n F J W+
    J*(20000*(2*W+1)^3+5)+2*J+1+
    SemiprimeNativeBitsCounter.inputControl n F s R W

/-- Exact equality, including the old harmless nonnegative group-boundary overestimate. -/
theorem groupBudget_eq_polynomial (n F R J b s w A E : ℕ) :
    SemiprimeNativeBitsCounterBudget.groupBudget n F R J b s w A E=
      groupPolynomial n F R J b s w A E (2^w) := by
  rfl

/-- A diagonal physical group envelope uses only the LOCAL count resource. -/
def groupEnvelope (S : ℕ) : ℕ :=
  groupPolynomial S S S S (inputEnvelope S) S S (S+1) S S

/-- Scalar monotonicity keeps 2^w independent of the coarse resource S. -/
theorem groupBudget_le_envelope (n F R J b s w E S : ℕ)
    (hn : n ≤ S) (hF : F ≤ S) (hR : R ≤ S) (hJ : J ≤ S) (hb : b ≤ inputEnvelope S)
    (hs : s ≤ S) (hw : w ≤ S) (hE : E ≤ S) (hEw : 2^w ≤ S) :
    SemiprimeNativeBitsCounterBudget.groupBudget n F R J b s w (R+1) E ≤ groupEnvelope S := by
  rw [groupBudget_eq_polynomial]
  unfold groupEnvelope groupPolynomial
  dsimp only
  simp only [SemiprimeNativeGroupBits.groupWidth,SemiprimeNativeGroupBits.factorExponent,
    SemiprimeNativeLocalBits.publicWidth,SemiprimeNativeLocalBits.portExponent,
    SemiprimeCorrectedPortBits.portWidth,SemiprimeLocalBitsBounds.bufferWidth,
    SemiprimeCorrectedPortBitsBounds.portBudget,SemiprimeCorrectedPortBitsBounds.shiftStepBudget,
    SemiprimeCorrectedPortBitsBounds.maskBudget,SemiprimeCorrectedPortBitsBounds.addBudget,
    SemiprimeCorrectedPortBitsBounds.multiplyBudget,SemiprimeLocalBitsBounds.nodeBudget,
    SemiprimeLocalBitsBounds.scaleBudget,SemiprimeLocalBitsBounds.addBudget,
    SemiprimeLocalBitsBounds.multiplyBudget,SemiprimeLocalBitsBounds.accessBudget,
    SemiprimeNativeGroupBitsBudget.multiplyBudget,SemiprimeNativeGroupBits.groupControl,
    SemiprimeNativeBitsCounter.inputControl]
  gcongr

/-- A HEAD count is separated in the physical head and support node polynomial. -/
def nodePolynomial (W n J r H M B Y Cq Eh : ℕ) : ℕ :=
  let head := 3*J+1+Eh*(B+2*M+4*H+3*J+5+SemiprimeWordFoldBounds.addBudget W J)
  let one := r*(head+SemiprimeNativeGroupBitsBudget.multiplyBudget W J+J+3)+(3*J+1)+
    r*(Eh*(2*M+3)+H+1)+r+1
  let fibre := 3*J+1+Y*(one+SemiprimeWordFoldBounds.addBudget W J)
  Cq*(fibre+SemiprimeWordFoldBounds.scaleBudget W J+3*n+1+
    n*(2*SemiprimeWordFoldBounds.addBudget W J+1))+
    (r*(Eh*(H+M*(4*H+2)+3))+r+1)

/-- Exact node traversal identity at its actual finite cardinalities. -/
theorem nodeBudget_eq_polynomial (W n J r H M B Y : ℕ) :
    SemiprimeMaterializedWordFibreBounds.nodeBudget W n J r H M B Y=
      nodePolynomial W n J r H M B Y
        (SemiprimeCounterEnumeration.weightedCount n (J-1)) (2^H) := by
  rfl

/-- Original head and group dimensions give a polynomial packet width. -/
def nodeWidthEnvelope (S : ℕ) : ℕ :=
  SemiprimeWordPacketWidth.packetWidth (inputEnvelope S) S S S S S S (1+S*S) S S

/-- Complete physical word-node envelope including actual parameter/control work. -/
def nodeEnvelope (S : ℕ) : ℕ :=
  nodePolynomial (nodeWidthEnvelope S) S S S S S (groupEnvelope S) S S S+
    40*(S+S+S+S+S*S+inputEnvelope S+S+S+nodeWidthEnvelope S+1)^2+20

/-- Actual head cap uses the given HEAD count, never a new 2^S bound. -/
theorem headCap_le {n F : ℕ} (d : RuntimeDesign n F) (H S : ℕ)
    (hr : d.r ≤ S) (hh : ∀ g,d.h g ≤ H) (hEh : 2^H ≤ S) :
    SemiprimeWordPacketCounter.headCap d ≤ 1+S*S := by
  have h : (∑ g,2^(d.h g)) ≤ d.r*2^H := by
    calc
      _  ≤  ∑ _g : Fin d.r,2^H := Finset.sum_le_sum (fun g _ => Nat.pow_le_pow_right (by decide) (hh g))
      _ = _ := by simp
  unfold SemiprimeWordPacketCounter.headCap
  exact Nat.add_le_add_left (h.trans (Nat.mul_le_mul hr hEh)) 1

/-- All actual width parameters, summary cardinalities and HEAD caps are acquired resources. -/
theorem nodeWidth_le_envelope {n F : ℕ} (b R J H S : ℕ) (arity : Fin F → ℕ)
    (d : RuntimeDesign n F) (hn : n ≤ S) (hF : F ≤ S) (hs : (∑ e,arity e) ≤ S)
    (hb : b ≤ inputEnvelope S) (hR : R ≤ S) (hJ : J ≤ S) (hr : d.r ≤ S)
    (hh : ∀ g,d.h g ≤ H) (hEh : 2^H ≤ S)
    (hY : SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W ≤ S)
    (hCq : SemiprimeCounterEnumeration.weightedCount n (J-1) ≤ S) :
    SemiprimeWordPacketCounter.nodeWidth b R J arity d ≤ nodeWidthEnvelope S := by
  have hp := headCap_le d H S hr hh hEh
  unfold SemiprimeWordPacketCounter.nodeWidth nodeWidthEnvelope
  simp only [SemiprimeWordPacketWidth.packetWidth,SemiprimeWordPacketWidth.productExponent,
    SemiprimeNativeGroupBitsHeight.exponent,SemiprimeNativeGroupBits.factorExponent,SemiprimeNativeGroupBits.groupWidth,
    SemiprimeNativeLocalBits.publicWidth,SemiprimeNativeLocalBits.portExponent,
    SemiprimeCorrectedPortBits.portWidth,SemiprimeLocalBitsBounds.bufferWidth]
  gcongr

/-- Full actual physical node bound, with independent head/local/support resources. -/
theorem nodeBudget_le_envelope {n F : ℕ} (b J R H M w E S : ℕ)
    (arity : Fin F → ℕ) (d : RuntimeDesign n F)
    (hn : n ≤ S) (hF : F ≤ S) (hs : (∑ e,arity e) ≤ S)
    (hb : b ≤ inputEnvelope S) (hJ : J ≤ S) (hR : R ≤ S)
    (hH : H ≤ S) (hM : M ≤ S) (hw : w ≤ S) (hE : E ≤ S)
    (hr : d.r ≤ S) (hh : ∀ g,d.h g ≤ H) (hm : ∀ g,d.m g ≤ M)
    (hY : SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W ≤ S)
    (hCq : SemiprimeCounterEnumeration.weightedCount n (J-1) ≤ S)
    (hEw : 2^w ≤ S) (hEh : 2^H ≤ S) :
    SemiprimeWordPacketCounterBudget.nodeBudget b J R H M
      (SemiprimeNativeBitsCounterBudget.groupBudget n F R J b (∑ e,arity e) w (R+1) E) arity d ≤
        nodeEnvelope S := by
  have hwidth := nodeWidth_le_envelope b R J H S arity d hn hF hs hb hR hJ hr hh hEh hY hCq
  have hg := groupBudget_le_envelope n F R J b (∑ e,arity e) w E S hn hF hR hJ hb hs hw hE hEw
  have hsum : (∑ g,d.m g) ≤ S*S := by
    calc
      _ ≤ ∑ _g : Fin d.r,M := Finset.sum_le_sum (fun g _ => hm g)
      _ = d.r*M := by simp
      _ ≤ S*S := Nat.mul_le_mul hr hM
  have hp : SemiprimeMaterializedWordFibreBounds.nodeBudget
      (SemiprimeWordPacketCounter.nodeWidth b R J arity d) n J d.r H M
      (SemiprimeNativeBitsCounterBudget.groupBudget n F R J b (∑ e,arity e) w (R+1) E)
      (SemiprimePacketArrayExecution.summaryCount d.r d.h d.m d.W) ≤
      nodePolynomial (nodeWidthEnvelope S) S S S S S (groupEnvelope S) S S S := by
    rw [nodeBudget_eq_polynomial]
    unfold nodePolynomial
    dsimp only
    simp only [SemiprimeWordFoldBounds.addBudget,SemiprimeWordFoldBounds.scaleBudget,
      SemiprimeCorrectedPortBitsBounds.addBudget,SemiprimeNativeGroupBitsBudget.multiplyBudget]
    gcongr
  have hc : SemiprimeWordPacketCounter.nodeControl b R J arity d ≤
      40*(S+S+S+S+S*S+inputEnvelope S+S+S+nodeWidthEnvelope S+1)^2+20 := by
    unfold SemiprimeWordPacketCounter.nodeControl
    gcongr
  unfold SemiprimeWordPacketCounterBudget.nodeBudget nodeEnvelope
  omega

end RiemannGaussian.SemiprimeHermiteReportStagePolynomial
