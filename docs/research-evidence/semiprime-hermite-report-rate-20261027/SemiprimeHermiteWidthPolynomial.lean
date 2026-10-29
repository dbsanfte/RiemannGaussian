/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteWordWidth
import RiemannGaussian.SemiprimeReportPolynomialGrowth

/-! # Fixed polynomial majorant of the actual Hermite width
Natural logarithmic factors are bounded by their original dimensions. This
changes only an upper bound; the executed width and caller remain unchanged.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeHermiteWidthPolynomial
open SemiprimeReportPolynomialGrowth

/-- Explicit monotone polynomial obtained by bounding the actual logarithmic factors. -/
def polynomial (b Q J : ℕ) : ℕ :=
  let cardinal := Q*Q*(Q*J)
  let inverse := cardinal+Q*J+(J+1)+3
  let input := Q*Q+Q+J+1
  let quotient := b+J+(cardinal+inverse)*J+1
  b+Q+J+SemiprimeAffineJetBits.width input (Q*J)+
    SemiprimeNormalizedInverseBits.inverseWidth (cardinal+Q*J) J+
    SemiprimeHermiteEvaluationBitsBounds.evaluationWidth input (Q*J)+
    SemiprimeHermiteEvaluationBitsBounds.evaluationWidth (quotient+Q+1) J+
    quotient+(b+cardinal*(J+1))+
    ((Q+1)+(Q*Q+(Q+1))*(Q*J)+2*(J+1)+b+inverse*J+(Q+1)*J)+Q+10

/-- The actual chosen physical width lies below this explicit polynomial. -/
theorem width_le_polynomial (b Q J : ℕ) :
    SemiprimeHermiteWordWidth.width b Q J≤polynomial b Q J := by
  have hQ := SemiprimeHermiteArrayHeight.clog_two_le_self Q
  have hQ1 := SemiprimeHermiteArrayHeight.clog_two_le_self (Q+1)
  have hJ1 := SemiprimeHermiteArrayHeight.clog_two_le_self (J+1)
  simp only [SemiprimeHermiteWordWidth.width,polynomial,
    SemiprimeHermiteWordWidth.inputExponent,SemiprimeHermiteWordWidth.cardinalExponent,
    SemiprimeHermiteWordWidth.quotientExponent,SemiprimeHermiteArrayHeight.cardinalBits,
    SemiprimeHermiteArrayHeight.inverseBits,SemiprimeHermiteArrayHeight.cardinalZeroBits,
    SemiprimeHermiteArrayHeight.hermiteDenominatorBits,SemiprimeHermiteArrayHeight.hermiteNumeratorBits,
    SemiprimeAffineJetBits.width,SemiprimeNormalizedInverseBits.inverseWidth,
    SemiprimeHermiteEvaluationBitsBounds.evaluationWidth]
  gcongr

/-- Componentwise dimension bounds preserve the polynomial majorant. -/
theorem polynomial_mono {b Q J b' Q' J' : ℕ}
    (hb : b≤b') (hQ : Q≤Q') (hJ : J≤J') :
    polynomial b Q J≤polynomial b' Q' J' := by
  unfold polynomial SemiprimeAffineJetBits.width SemiprimeNormalizedInverseBits.inverseWidth
    SemiprimeHermiteEvaluationBitsBounds.evaluationWidth
  dsimp only
  gcongr

/-- A uniform diagonal bound suffices for all three actual dimensions. -/
theorem width_le_envelope (b Q J S : ℕ) (hb : b≤S) (hQ : Q≤S) (hJ : J≤S) :
    SemiprimeHermiteWordWidth.width b Q J≤polynomial S S S :=
  (width_le_polynomial b Q J).trans (polynomial_mono hb hQ hJ)

/-- The diagonal majorant has fixed monomial witnesses independent of the input. -/
theorem polynomial_monomial : ∃ C k : ℕ,∀ S,polynomial S S S≤C*(S+1)^k := by
  change Bound (fun S => polynomial S S S)
  unfold polynomial SemiprimeAffineJetBits.width SemiprimeNormalizedInverseBits.inverseWidth
    SemiprimeHermiteEvaluationBitsBounds.evaluationWidth
  dsimp only
  boundArithmetic

end RiemannGaussian.SemiprimeHermiteWidthPolynomial
