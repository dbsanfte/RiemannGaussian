/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteReportStagePolynomial
import RiemannGaussian.SemiprimeHermiteWidthPolynomial

/-! # Fixed polynomial resource envelope for the actual physical-Hermite report
Actual local/head/support/summary cardinalities remain separate paid resources.
Computed source bits are bounded by a polynomial; they are never assumed small.
-/
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 20000
namespace RiemannGaussian.SemiprimeHermiteReportEnvelope
open scoped BigOperators
open SemiprimeHermiteReportStagePolynomial
open SemiprimeNodeArrayExecution (RuntimeDesign)

/-- Common packet input height, from actual bounded node widths. -/
def packetBitsEnvelope (S : ℕ) : ℕ := 2*S*nodeWidthEnvelope S+1
/-- Polynomial Hermite width after deriving the actual packet input height. -/
def countWidthEnvelope (S : ℕ) : ℕ :=
  SemiprimeHermiteWidthPolynomial.polynomial (packetBitsEnvelope S) S S
/-- Actual retained native/Hermite/final-decode reduction polynomial. -/
def reductionEnvelope (S : ℕ) : ℕ :=
  S*nodeEnvelope S+S*SemiprimeHermiteNodeBitsBounds.budget (countWidthEnvelope S) S S S+
    S*(20000*(countWidthEnvelope S+1)^3+8*countWidthEnvelope S+8)+4+
    SemiprimeWordPacketCounterBudget.decodeBudget (countWidthEnvelope S) 1
/-- Full actual physical counter resource polynomial, including cached getters. -/
def nativeEnvelope (S : ℕ) : ℕ :=
  S*S*(2*S+6)+S*(4*(inputEnvelope S+1)+4)+reductionEnvelope S+
    SemiprimeNativeBitsCounter.inputControl S S S S (inputEnvelope S)+
    40*(S+S+S+inputEnvelope S+S+S+S+countWidthEnvelope S+1)^2+20+10*S+10
/-- Scalar source encoding is separately charged at its computed source-bit bound. -/
def encodingEnvelope (S : ℕ) : ℕ :=
  SemiprimeSourceWordAcquisition.encodingBudget S S (inputEnvelope S) S
/-- Setup, source encoding and the NEW actual physical counter report. -/
def polynomialEnvelope (S : ℕ) : ℕ :=
  SemiprimeSetupPolynomialEnvelope.polynomialEnvelope S+encodingEnvelope S+1+nativeEnvelope S

/-- Actual packet height is bounded without acquiring common-denominator values. -/
theorem packetBits_le_envelope {n F Q : ℕ} (b R J H S : ℕ) (arity : Fin F → ℕ)
    (design : Fin Q → RuntimeDesign n F)
    (hn : n ≤ S) (hF : F ≤ S) (hs : (∑ e,arity e) ≤ S) (hQ : Q ≤ S)
    (hb : b ≤ inputEnvelope S) (hR : R ≤ S) (hJ : J ≤ S)
    (hr : ∀ a,(design a).r ≤ S) (hh : ∀ a g,(design a).h g ≤ H) (hEh : 2^H ≤ S)
    (hY : ∀ a,SemiprimePacketArrayExecution.summaryCount (design a).r (design a).h (design a).m (design a).W ≤ S)
    (hCq : SemiprimeCounterEnumeration.weightedCount n (J-1) ≤ S) :
    SemiprimeWordPacketHermiteInput.packetBits b R J arity design ≤ packetBitsEnvelope S := by
  have hsum : (∑ a,SemiprimeWordPacketCounter.nodeWidth b R J arity (design a)) ≤ Q*nodeWidthEnvelope S := by
    calc
      _ ≤ ∑ _a : Fin Q,nodeWidthEnvelope S := Finset.sum_le_sum (fun a _ =>
        nodeWidth_le_envelope b R J H S arity (design a) hn hF hs hb hR hJ (hr a) (hh a) hEh (hY a) hCq)
      _ = _ := by simp
  unfold SemiprimeWordPacketHermiteInput.packetBits packetBitsEnvelope
  simpa only [Nat.mul_assoc] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 (hsum.trans (Nat.mul_le_mul_right _ hQ))) 1

/-- The runtime Hermite width has a fixed polynomial resource majorant. -/
theorem countWidth_le_envelope {n F Q : ℕ} (b R J H S : ℕ) (arity : Fin F → ℕ)
    (design : Fin Q → RuntimeDesign n F)
    (hn : n ≤ S) (hF : F ≤ S) (hs : (∑ e,arity e) ≤ S) (hQ : Q ≤ S)
    (hb : b ≤ inputEnvelope S) (hR : R ≤ S) (hJ : J ≤ S)
    (hr : ∀ a,(design a).r ≤ S) (hh : ∀ a g,(design a).h g ≤ H) (hEh : 2^H ≤ S)
    (hY : ∀ a,SemiprimePacketArrayExecution.summaryCount (design a).r (design a).h (design a).m (design a).W ≤ S)
    (hCq : SemiprimeCounterEnumeration.weightedCount n (J-1) ≤ S) :
    SemiprimeHermiteBitsCounter.countWidth b Q J R arity design ≤ countWidthEnvelope S := by
  exact (SemiprimeHermiteWidthPolynomial.width_le_polynomial _ Q J).trans
    (SemiprimeHermiteWidthPolynomial.polynomial_mono
      (packetBits_le_envelope b R J H S arity design hn hF hs hQ hb hR hJ hr hh hEh hY hCq) hQ hJ)

/-- The actual physical-Hermite budget is polynomial in the GIVEN separate resources. -/
theorem nativeBudget_le_envelope {n F Q : ℕ} (b J R H M w E Y S : ℕ)
    (arity : Fin F → ℕ) (design : Fin Q → RuntimeDesign n F)
    (hn : n ≤ S) (hF : F ≤ S) (hs : (∑ e,arity e) ≤ S) (hQ : Q ≤ S)
    (hJ : J ≤ S) (hR : R ≤ S) (hH : H ≤ S) (hM : M ≤ S)
    (hw : w ≤ S) (hE : E ≤ S) (hYs : Y ≤ S) (hb : b ≤ inputEnvelope S)
    (hr : ∀ a,(design a).r ≤ S) (hh : ∀ a g,(design a).h g ≤ H)
    (hm : ∀ a g,(design a).m g ≤ M)
    (hy : ∀ a,SemiprimePacketArrayExecution.summaryCount (design a).r (design a).h (design a).m (design a).W ≤ Y)
    (hCq : SemiprimeCounterEnumeration.weightedCount n (J-1) ≤ S)
    (hEw : 2^w ≤ S) (hEh : 2^H ≤ S) :
    SemiprimeHermiteBitsSetupBudget.nativeBudget n F (∑ e,arity e) b Q J R H M w E arity design ≤ nativeEnvelope S := by
  have hy' (a) := (hy a).trans hYs
  have hW := countWidth_le_envelope b R J H S arity design hn hF hs hQ hb hR hJ hr hh hEh hy' hCq
  have hnodes : (∑ a,SemiprimeWordPacketCounterBudget.nodeBudget b J R H M
      (SemiprimeNativeBitsCounterBudget.groupBudget n F R J b (∑ e,arity e) w (R+1) E) arity (design a)) ≤
      S*nodeEnvelope S := by
    calc
      _ ≤ ∑ _a : Fin Q,nodeEnvelope S := Finset.sum_le_sum (fun a _ =>
        nodeBudget_le_envelope b J R H M w E S arity (design a) hn hF hs hb hJ hR hH hM hw hE
          (hr a) (hh a) (hm a) (hy' a) hCq hEw hEh)
      _ = Q*nodeEnvelope S := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hQ
  have hreduction : SemiprimeHermiteBitsCounterBudget.reductionBudget b Q J R H M
      (SemiprimeNativeBitsCounterBudget.groupBudget n F R J b (∑ e,arity e) w (R+1) E) arity design ≤
        reductionEnvelope S := by
    unfold SemiprimeHermiteBitsCounterBudget.reductionBudget reductionEnvelope
    simp only [SemiprimeHermiteNodeBitsBounds.budget,SemiprimeHermiteNodeBitsBounds.quotientBudget,SemiprimeHermiteNodeBits.control,
      SemiprimeCardinalInputBits.budget,SemiprimeCardinalInputBits.slopeBudget,
      SemiprimeAffineJetBits.stepBudget,SemiprimeNormalizedInverseBitsBounds.stepBudget,
      SemiprimeWordPacketCounterBudget.decodeBudget]
    gcongr
  have hget : (∑ e,arity e)*n*(2*(∑ e,arity e)+6) ≤ S*S*(2*S+6) := by gcongr
  have henc : Q*(4*(b+1)+4) ≤ S*(4*(inputEnvelope S+1)+4) := by gcongr
  have hic : SemiprimeNativeBitsCounter.inputControl n F (∑ e,arity e) R b ≤
      SemiprimeNativeBitsCounter.inputControl S S S S (inputEnvelope S) := by
    unfold SemiprimeNativeBitsCounter.inputControl
    gcongr
  have hctrl : SemiprimeHermiteBitsCounter.control b Q J R arity design ≤
      40*(S+S+S+inputEnvelope S+S+S+S+countWidthEnvelope S+1)^2+20 := by
    unfold SemiprimeHermiteBitsCounter.control
    gcongr
  unfold SemiprimeHermiteBitsSetupBudget.nativeBudget nativeEnvelope
  omega

/-- Original source encoding bits are bounded via the computed input polynomial. -/
theorem encoding_le_envelope (n s B Q R J S : ℕ)
    (hn : n ≤ S) (hs : s ≤ S) (hB : B ≤ S) (hQ : Q ≤ S) (hR : R ≤ S) (hJ : J ≤ S) :
    SemiprimeSourceWordAcquisition.encodingBudget s n (SemiprimeSourceWordAcquisition.sourceBits B Q R) R ≤
      encodingEnvelope S := by
  have hb := inputBits_le_envelope n B Q R J S hn hB hQ hR hJ
  have hsource : SemiprimeSourceWordAcquisition.sourceBits B Q R ≤ inputEnvelope S :=
    (Nat.le_succ _).trans ((SemiprimeNativeInputBits.sourceWidth_le n B Q R J).trans hb)
  unfold encodingEnvelope SemiprimeSourceWordAcquisition.encodingBudget
  dsimp only
  gcongr

/-- The full original-source budget is dominated by one fixed polynomial.
All source menus are actual separate bounded resources; computed input bits are derived. -/
theorem fullBudget_le_envelope {n F Q : ℕ} (r R B J H M w E Y S : ℕ)
    (arity : Fin F → ℕ) (design : Fin Q → RuntimeDesign n F)
    (hn : n ≤ S) (hF : F ≤ S) (hs : (∑ e,arity e) ≤ S)
    (hrs : r ≤ S) (hQ : Q ≤ S) (hR : R ≤ S) (hB : B ≤ S) (hJ : J ≤ S)
    (hH : H ≤ S) (hM : M ≤ S) (hw : w ≤ S) (hE : E ≤ S) (hYs : Y ≤ S)
    (hD : r^(2*Q) ≤ S) (hA : r^Q ≤ S)
    (hr : ∀ a,(design a).r ≤ S) (hh : ∀ a g,(design a).h g ≤ H)
    (hm : ∀ a g,(design a).m g ≤ M)
    (hy : ∀ a,SemiprimePacketArrayExecution.summaryCount (design a).r (design a).h (design a).m (design a).W ≤ Y)
    (hCq : SemiprimeCounterEnumeration.weightedCount n (J-1) ≤ S)
    (hEw : 2^w ≤ S) (hEh : 2^H ≤ S) :
    SemiprimeFullSetupBudget.setupBudget n F (∑ e,arity e) r Q R B (r^(2*Q)) (r^Q)+
      SemiprimeSourceWordAcquisition.encodingBudget (∑ e,arity e) n
        (SemiprimeSourceWordAcquisition.sourceBits B Q R) R+1+
      SemiprimeHermiteBitsSetupBudget.nativeBudget n F (∑ e,arity e)
        (SemiprimeNativeInputBits.inputBits n B Q R J) Q J R H M w E arity design ≤ polynomialEnvelope S := by
  have hsetup := SemiprimeSetupPolynomialEnvelope.setupBudget_le_envelope n F (∑ e,arity e)
    r Q R B (r^(2*Q)) (r^Q) S hn hF hs hrs hQ hR hB hD hA
  have hencoding := encoding_le_envelope n (∑ e,arity e) B Q R J S hn hs hB hQ hR hJ
  have hnative := nativeBudget_le_envelope (SemiprimeNativeInputBits.inputBits n B Q R J)
    J R H M w E Y S arity design hn hF hs hQ hJ hR hH hM hw hE hYs
    (inputBits_le_envelope n B Q R J S hn hB hQ hR hJ) hr hh hm hy hCq hEw hEh
  exact Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add hsetup hencoding) 1) hnative

open SemiprimeReportPolynomialGrowth

/-- The actual physical counter diagonal has fixed monomial growth witnesses. -/
theorem native_monomial : Bound nativeEnvelope := by
  unfold nativeEnvelope reductionEnvelope countWidthEnvelope packetBitsEnvelope
    SemiprimeHermiteWidthPolynomial.polynomial nodeEnvelope nodePolynomial
    nodeWidthEnvelope groupEnvelope groupPolynomial inputEnvelope
    SemiprimeNativeInputBits.polynomial
    SemiprimeHermiteNodeBitsBounds.budget SemiprimeHermiteNodeBitsBounds.quotientBudget
    SemiprimeCardinalInputBits.budget SemiprimeCardinalInputBits.slopeBudget
    SemiprimeAffineJetBits.stepBudget SemiprimeAffineJetBits.width
    SemiprimeNormalizedInverseBitsBounds.stepBudget SemiprimeNormalizedInverseBits.inverseWidth
    SemiprimeHermiteEvaluationBitsBounds.evaluationWidth SemiprimeHermiteNodeBits.control
    SemiprimeWordPacketCounterBudget.decodeBudget
    SemiprimeWordPacketWidth.packetWidth SemiprimeWordPacketWidth.productExponent
    SemiprimeNativeGroupBitsHeight.exponent SemiprimeNativeGroupBits.groupWidth
    SemiprimeNativeGroupBits.factorExponent SemiprimeNativeLocalBits.publicWidth
    SemiprimeNativeLocalBits.portExponent SemiprimeCorrectedPortBits.portWidth
    SemiprimeLocalBitsBounds.bufferWidth SemiprimeCorrectedPortBitsBounds.portBudget
    SemiprimeCorrectedPortBitsBounds.shiftStepBudget SemiprimeCorrectedPortBitsBounds.maskBudget
    SemiprimeCorrectedPortBitsBounds.addBudget SemiprimeCorrectedPortBitsBounds.multiplyBudget
    SemiprimeLocalBitsBounds.nodeBudget SemiprimeLocalBitsBounds.scaleBudget
    SemiprimeLocalBitsBounds.addBudget SemiprimeLocalBitsBounds.multiplyBudget
    SemiprimeLocalBitsBounds.accessBudget SemiprimeNativeGroupBitsBudget.multiplyBudget
    SemiprimeNativeGroupBits.groupControl SemiprimeNativeBitsCounter.inputControl
    SemiprimeWordFoldBounds.addBudget SemiprimeWordFoldBounds.scaleBudget
  dsimp only
  simp only [SemiprimeCorrectedPortBitsBounds.addBudget]
  boundArithmetic

/-- The actual source encoding diagonal has fixed monomial growth witnesses. -/
theorem encoding_monomial : Bound encodingEnvelope := by
  unfold encodingEnvelope SemiprimeSourceWordAcquisition.encodingBudget inputEnvelope
    SemiprimeNativeInputBits.polynomial
  dsimp only
  boundArithmetic

/-- The new full setup/physical-Hermite bound has fixed, input-independent monomial witnesses. -/
theorem polynomialEnvelope_monomial : ∃ C k : ℕ,∀ S,polynomialEnvelope S ≤ C*(S+1)^k := by
  have hsetup : Bound SemiprimeSetupPolynomialEnvelope.polynomialEnvelope := by
    obtain ⟨C,k,h⟩ := setup_native_monomial
    exact ⟨C,k,fun S => (Nat.le_add_right _ _).trans (h S)⟩
  exact add_bound (add_bound (add_bound hsetup encoding_monomial) (constant_bound 1)) native_monomial

end RiemannGaussian.SemiprimeHermiteReportEnvelope
