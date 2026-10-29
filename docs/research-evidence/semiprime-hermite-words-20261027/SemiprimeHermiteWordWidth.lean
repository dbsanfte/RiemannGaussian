/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeAffineJetBits
import RiemannGaussian.SemiprimeNormalizedInverseBits
import RiemannGaussian.SemiprimeHermiteEvaluationBitsBounds

/-! # Original-input width for the whole physical Hermite node

All exponents are explicit fixed polynomials with natural logarithmic factors.
No cardinal input, inverse coefficient or intermediate Fits is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeHermiteWordWidth
open SemiprimeHermiteArrayHeight SemiprimeJetArrayHeight SemiprimeCardinalHeight

/-- Original factorial, node and precision input exponent. -/
def inputExponent (Q J : ℕ) : ℕ := Nat.clog 2 Q*Q+Q+J+1
/-- Intrinsic cardinal coefficient exponent, common to every node. -/
def cardinalExponent (Q J : ℕ) : ℕ := cardinalBits Q J+Q*J
/-- Common quotient denominator and coefficient numerator exponent. -/
def quotientExponent (b Q J : ℕ) : ℕ :=
  b+J+(cardinalBits Q J+inverseBits Q J)*J+1
/-- One literal public template for all actual Hermite stages and final sums. -/
def width (b Q J : ℕ) : ℕ :=
  b+Q+J+SemiprimeAffineJetBits.width (inputExponent Q J) (Q*J)+
  SemiprimeNormalizedInverseBits.inverseWidth (cardinalExponent Q J) J+
  SemiprimeHermiteEvaluationBitsBounds.evaluationWidth (inputExponent Q J) (Q*J)+
  SemiprimeHermiteEvaluationBitsBounds.evaluationWidth (quotientExponent b Q J+Q+1) J+
  quotientExponent b Q J+hermiteDenominatorBits Q J b+
  hermiteNumeratorBits Q J b+Q+10

/-- Factorial and integer node/precision bounds follow from the public exponent. -/
theorem input_guards (Q J : ℕ) :
    Q.factorial≤2^inputExponent Q J ∧ Q≤2^inputExponent Q J ∧ J≤2^inputExponent Q J := by
  have hf := factorial_dyadic Q
  have hq := (Nat.lt_two_pow_self (n:=Q)).le
  have hj := (Nat.lt_two_pow_self (n:=J)).le
  unfold inputExponent
  exact ⟨hf.trans (Nat.pow_le_pow_right (by decide) (by omega)),
    hq.trans (Nat.pow_le_pow_right (by decide) (by omega)),
    hj.trans (Nat.pow_le_pow_right (by decide) (by omega))⟩

/-- Intrinsic cardinal denominator and numerator share a computable exponent. -/
theorem cardinal_guards (Q J : ℕ) :
    cardinalDenominator Q J≤2^cardinalExponent Q J ∧
    cardinalDenominator Q J*2^(Q*J)≤2^cardinalExponent Q J := by
  have hc := cardinalDenominator_dyadic Q J
  refine ⟨hc.trans (Nat.pow_le_pow_right (by decide) (by unfold cardinalExponent;omega)),?_⟩
  calc
    _ ≤ 2^cardinalBits Q J*2^(Q*J) := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [← pow_add];rfl

/-- Original packet bounds imply actual cached quotient coefficient bounds. -/
theorem quotient_guards (b Q J DH BH : ℕ) (hDH : DH≤2^b) (hBH : BH≤2^b) :
    DH*cardinalDenominator Q J^J≤2^quotientExponent b Q J ∧
    J*BH*inverseBase J (cardinalDenominator Q J)
      (cardinalDenominator Q J*2^(Q*J))^J≤2^quotientExponent b Q J := by
  have hc := cardinalDenominator_dyadic Q J
  have hi := inverseBase_dyadic Q J
  have hj := (Nat.lt_two_pow_self (n:=J)).le
  constructor
  · calc
      _ ≤ 2^b*(2^cardinalBits Q J)^J := Nat.mul_le_mul hDH (Nat.pow_le_pow_left hc _)
      _ = 2^(b+cardinalBits Q J*J) := by rw [← pow_mul,← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold quotientExponent;nlinarith)
  · calc
      _ ≤ 2^J*2^b*(2^inverseBits Q J)^J :=
        Nat.mul_le_mul (Nat.mul_le_mul hj hBH) (Nat.pow_le_pow_left hi _)
      _ = 2^(J+b+inverseBits Q J*J) := by rw [← pow_mul,← pow_add,← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold quotientExponent;nlinarith)

/-- The actual physical template is nonempty. -/
theorem width_positive (b Q J : ℕ) : 0<width b Q J := by unfold width;omega
/-- Original packet exponent fits in the selected word width. -/
theorem input_width_le (b Q J : ℕ) : b≤width b Q J := by unfold width;omega
/-- Intrinsic affine array construction has its acquired width. -/
theorem affine_width_le (b Q J : ℕ) :
    SemiprimeAffineJetBits.width (inputExponent Q J) (Q*J)≤width b Q J := by unfold width;omega
/-- Cached normalized inversion has its acquired width. -/
theorem inverse_width_le (b Q J : ℕ) :
    SemiprimeNormalizedInverseBits.inverseWidth (cardinalExponent Q J) J≤width b Q J := by unfold width;omega
/-- Scalar affine-at-zero construction has its acquired width. -/
theorem affineValue_width_le (b Q J : ℕ) :
    SemiprimeHermiteEvaluationBitsBounds.evaluationWidth (inputExponent Q J) (Q*J)≤width b Q J := by unfold width;omega
/-- Quotient scalar evaluation has its acquired width. -/
theorem eval_width_le (b Q J : ℕ) :
    SemiprimeHermiteEvaluationBitsBounds.evaluationWidth (quotientExponent b Q J+Q+1) J≤width b Q J := by unfold width;omega
/-- The original factorial/node exponent fits in the selected width. -/
theorem inputExponent_le (b Q J : ℕ) : inputExponent Q J≤width b Q J := by
  have h := affine_width_le b Q J
  unfold SemiprimeAffineJetBits.width at h
  have hp : 2*inputExponent Q J+1≤(2*inputExponent Q J+1)*(Q*J+1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2*inputExponent Q J+1) (show 1≤Q*J+1 by omega)
  omega
/-- The intrinsic cardinal common exponent fits in the selected width. -/
theorem cardinalExponent_le (b Q J : ℕ) : cardinalExponent Q J≤width b Q J := by
  have h := inverse_width_le b Q J
  unfold SemiprimeNormalizedInverseBits.inverseWidth at h
  omega
/-- Literal original slope and integer-node encodings fit in the template. -/
theorem node_input_width_le (b Q J : ℕ) : Q+2≤width b Q J := by unfold width;omega
/-- Cached quotient height is strictly below the physical width. -/
theorem quotientExponent_lt (b Q J : ℕ) : quotientExponent b Q J<width b Q J := by unfold width;omega
/-- Cached quotient height is below the physical width. -/
theorem quotientExponent_le (b Q J : ℕ) : quotientExponent b Q J≤width b Q J := by unfold width;omega
/-- Final common denominator fits strictly, including all node-sum prefixes. -/
theorem denominatorBits_lt (b Q J : ℕ) : hermiteDenominatorBits Q J b<width b Q J := by unfold width;omega
/-- Final common numerator fits strictly, including all node-sum prefixes. -/
theorem numeratorBits_lt (b Q J : ℕ) : hermiteNumeratorBits Q J b<width b Q J := by unfold width;omega

/-- Actual quotient multiplication receives strict derived denominator/numerator caps. -/
theorem quotient_caps (b Q J DH BH : ℕ) (hDH : DH≤2^b) (hBH : BH≤2^b) :
    DH*cardinalDenominator Q J^J<2^width b Q J ∧
    J*BH*inverseBase J (cardinalDenominator Q J)
      (cardinalDenominator Q J*2^(Q*J))^J<2^width b Q J := by
  have h := quotient_guards b Q J DH BH hDH hBH
  have hp := Nat.pow_lt_pow_right (by decide : 1<2) (quotientExponent_lt b Q J)
  exact ⟨h.1.trans_lt hp,h.2.trans_lt hp⟩

/-- The original packet common bounds imply strict final scalar-sum caps. -/
theorem final_caps (b Q J DH BH : ℕ) (hDH : DH≤2^b) (hBH : BH≤2^b) :
    hermiteDenominator Q J DH<2^width b Q J ∧
    Q*hermiteNodeBound Q J BH<2^width b Q J := by
  exact ⟨(hermiteDenominator_dyadic Q J DH b hDH).trans_lt
      (Nat.pow_lt_pow_right (by decide) (denominatorBits_lt b Q J)),
    (hermiteNodeBound_dyadic Q J BH b hBH).trans_lt
      (Nat.pow_lt_pow_right (by decide) (numeratorBits_lt b Q J))⟩

/-- For an existing node, the same original sum cap also covers that one node. -/
theorem final_node_cap (b Q J BH : ℕ) (hQ : 0<Q) (hBH : BH≤2^b) :
    hermiteNodeBound Q J BH<2^width b Q J := by
  have h := (hermiteNodeBound_dyadic Q J BH b hBH).trans_lt
    (Nat.pow_lt_pow_right (by decide) (numeratorBits_lt b Q J))
  exact (show hermiteNodeBound Q J BH≤Q*hermiteNodeBound Q J BH by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (hermiteNodeBound Q J BH) hQ).trans_lt h

end RiemannGaussian.SemiprimeHermiteWordWidth
