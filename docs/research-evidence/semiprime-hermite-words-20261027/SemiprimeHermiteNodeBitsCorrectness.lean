/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteNodeBits
import RiemannGaussian.SemiprimeHermiteWordWidth

/-! # Original-packet correctness of the executed physical Hermite node
All cardinal data are acquired internally. Original common packet bounds derive
all intermediate fits; the normalized inverse is actually executed and cached.
-/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace RiemannGaussian.SemiprimeHermiteNodeBitsCorrectness
open SemiprimeRationalBits SemiprimeJetBits SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeLocalExecutionHeight SemiprimeCardinalHeight
open SemiprimeHermiteNodeBits SemiprimeHermiteWordWidth
open SemiprimeHermiteArrayHeight (hermiteDenominator hermiteNodeBound cardinalJet cardinalZero)

/-- The full physical node equals intrinsic Hermite and retains its original
common denominator. Neither intermediate fits nor cardinal/inverse values are inputs. -/
theorem node_correct (template : List Bool) (b Q J d B : ℕ) (t : Fin Q) (H : JetReport)
    (hJ : 0<J) (hd : 0<d) (hH : Valid H.words)
    (hrep : ArrayBound (decode H.words) J d B) (hdb : d≤2^b) (hBb : B≤2^b)
    (hw : width b Q J≤template.length) :
    (node template Q J t H).word.value=
      (SemiprimeHermiteArrayHeight.hermiteNode (decode H.words) Q J t).value ∧
    (node template Q J t H).word.Valid ∧
    Representation (node template Q J t H).word.value
      (hermiteDenominator Q J d) (hermiteNodeBound Q J B) := by
  let inputs := SemiprimeCardinalInputBits.acquire Q J t
  let L := SemiprimeAffineJetBits.build template J inputs.slopes
  let C := SemiprimeHermiteEvaluationBits.affineValue template inputs.x inputs.slopes
  let I := SemiprimeNormalizedInverseBits.build template L.words J
  let A := multiplyBits template H.words I.words J
  let E := SemiprimeHermiteEvaluationBits.evalPrefix template A.words inputs.x J
  let dc := cardinalDenominator Q J
  let bc := dc*2^(Q*J)
  have hdc : 0<dc := cardinalDenominator_pos Q J
  have hin := input_guards Q J
  have hcard := cardinal_guards Q J
  have hslopes : ∀ c∈inputs.slopes,c.Valid ∧ Representation c.value Q.factorial Q.factorial := by
    intro c hc
    exact ⟨SemiprimeCardinalInputBits.slopes_valid Q J t c hc,
      SemiprimeCardinalInputBits.slopes_representation Q J t c hc⟩
  have hlen : inputs.slopes.length=Q*J := SemiprimeCardinalInputBits.slopes_length Q J t
  have hmap : inputs.slopes.map RationalWord.value=SemiprimeHermiteArrayHeight.cardinalSlopes Q J t.val :=
    SemiprimeCardinalInputBits.slopes_value Q J t
  have hL := SemiprimeAffineJetBits.build_correct template (inputExponent Q J) J Q.factorial inputs.slopes
    (Nat.factorial_pos Q) hin.1 hin.2.2 (by rw [hlen]; exact (affine_width_le b Q J).trans hw) hslopes
  have hLeq : decode L.words=(cardinalJet Q J t.val).coefficients := by
    rw [hmap] at hL
    exact hL.1
  have hLrep : ArrayBound (decode L.words) J dc bc := by
    rw [hLeq]
    exact SemiprimeHermiteArrayHeight.cardinalJet_intrinsic_representation Q J hJ t
  have hL0 : coefficient (decode L.words) 0=1 := by
    rw [hLeq]
    exact SemiprimeHermiteArrayHeight.cardinalJet_constant Q J hJ t
  have hI := SemiprimeNormalizedInverseBits.build_correct_of_width template L.words dc bc
    (cardinalExponent Q J) J hdc hL.2.1 hL0 hLrep hcard.1 hcard.2
    ((inverse_width_le b Q J).trans hw)
  have hIeq : decode I.words=(inverse (decode L.words) J).coefficients := by
    rw [hI.1]
    simp only [inverse,hL0,inv_one]
  have hIrep : ArrayBound (decode I.words) J (dc^J) (inverseBase J dc bc^J) := by
    rw [hIeq]
    exact cached_inverse_common_representation (decode L.words) dc bc J hdc hL0 hLrep
  have hcap := quotient_caps b Q J d B hdb hBb
  have hp := Nat.pow_le_pow_right (by decide : 0<2) hw
  have hA := multiplyBits_correct template H.words I.words J d (dc^J) B (inverseBase J dc bc^J)
    hH hI.2 hd (pow_pos hdc _) (hcap.1.trans_le hp) (hcap.2.trans_le hp) hrep hIrep
  have hAeq : decode A.words=(quotient (decode H.words) (decode L.words) J).coefficients := by
    have he : decode A.words=(multiply (decode H.words) (decode I.words) J).coefficients := by
      apply SemiprimeCorrectedPortBits.array_eq_of_coeff J
      · simp only [A,decode_size,multiplyBits_size]
      · exact multiply_size _ _ _
      · exact hA.1
    rw [he,hIeq]
    rfl
  have hArep : ArrayBound (decode A.words) J (d*dc^J) (J*B*inverseBase J dc bc^J) := by
    rw [hAeq]
    exact SemiprimeHermiteArrayHeight.quotient_representation (decode H.words) (decode L.words)
      d dc B bc J hdc hL0 hrep hLrep
  have hguard := quotient_guards b Q J d B hdb hBb
  have heqle : quotientExponent b Q J≤quotientExponent b Q J+Q+1 := by omega
  have hqle : Q≤quotientExponent b Q J+Q+1 := by omega
  have hE := SemiprimeHermiteEvaluationBitsBounds.evalPrefix_at_width template A.words inputs.x
    (SemiprimeCardinalInputBits.xInt t) (quotientExponent b Q J+Q+1)
    (d*dc^J) (J*B*inverseBase J dc bc^J) Q J J ((eval_width_le b Q J).trans hw)
    (Nat.mul_pos hd (pow_pos hdc _)) hA.2 (SemiprimeCardinalInputBits.x_valid Q J t)
    (SemiprimeCardinalInputBits.x_value Q J t) (SemiprimeCardinalInputBits.x_natAbs_le Q t) le_rfl hArep
    (hguard.1.trans (Nat.pow_le_pow_right (by decide) heqle))
    (hguard.2.trans (Nat.pow_le_pow_right (by decide) heqle))
    ((Nat.lt_two_pow_self (n:=Q)).le.trans (Nat.pow_le_pow_right (by decide) hqle))
  have hC := SemiprimeHermiteEvaluationBitsBounds.affineValue_at_width template inputs.x
    (SemiprimeCardinalInputBits.xInt t) inputs.slopes (inputExponent Q J) Q.factorial Q.factorial Q (Q*J)
    ((affineValue_width_le b Q J).trans hw) (Nat.factorial_pos Q)
    (SemiprimeCardinalInputBits.x_valid Q J t) (SemiprimeCardinalInputBits.x_value Q J t)
    (SemiprimeCardinalInputBits.x_natAbs_le Q t) hlen.le hslopes hin.1 hin.1 hin.2.1
  have hvalue : C.word.value*E.word.value=
      (SemiprimeHermiteArrayHeight.hermiteNode (decode H.words) Q J t).value := by
    rw [hC.1,hE.1,hAeq,hLeq,hmap]
    rfl
  have hresult : Representation (C.word.value*E.word.value)
      (hermiteDenominator Q J d) (hermiteNodeBound Q J B) := by
    rw [hvalue]
    exact SemiprimeHermiteArrayHeight.hermiteNode_representation (decode H.words) Q J d B hJ t hrep
  have hdenpos : 0<hermiteDenominator Q J d := by
    unfold hermiteDenominator
    exact Nat.mul_pos hdc (Nat.mul_pos hd (pow_pos hdc _))
  have hf := final_caps b Q J d B hdb hBb
  have hn := final_node_cap b Q J B (lt_of_le_of_lt (Nat.zero_le t.val) t.isLt) hBb
  have hm := executeOperation_correct .mul C.word E.word template hC.2.1 hE.2.2.1
    (SemiprimeRationalBits.fits_of_representation hdenpos hresult (hn.trans_le hp) (hf.1.trans_le hp))
  have hout : (node template Q J t H).word.value=
      (SemiprimeHermiteArrayHeight.hermiteNode (decode H.words) Q J t).value :=
    hm.1.trans hvalue
  exact ⟨hout,hm.2.1,by rw [hout]; exact
    SemiprimeHermiteArrayHeight.hermiteNode_representation (decode H.words) Q J d B hJ t hrep⟩

end RiemannGaussian.SemiprimeHermiteNodeBitsCorrectness
