/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationSetup
import RiemannGaussian.SemiprimeD1StackRationalOperationProduct
import RiemannGaussian.SemiprimeD1StackRationalOperationAdd
/-! # Whole literal raw rational add/multiply/negate/invert acquisition -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalOperationRaw
open SemiprimeD1StackRationalOperation SemiprimeD1StackRationalOperationEncoding
open SemiprimeD1StackRationalOperationCalls SemiprimeD1StackRationalOperationSetup
open SemiprimeD1StackRationalOperationProduct SemiprimeD1StackRationalOperationAdd
open SemiprimeD1StackProcedureTrace
open SemiprimeBitArithmetic (mulBits)
/-- Proof-side exact raw output; no such object is a runtime operand or instruction. -/
def rawWord (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd:List Bool) :SemiprimeRationalBits.RationalWord:=
  match op with
  | .add=>⟨(SemiprimeBitIndexClipping.addSignedBits ⟨sx,(mulBits xn yd).bits⟩ ⟨sy,(mulBits yn xd).bits⟩).word,(mulBits xd yd).bits⟩
  | .mul=>⟨⟨Bool.xor sx sy,(mulBits xn yn).bits⟩,(mulBits xd yd).bits⟩
  | .neg=>⟨⟨!sx,xn⟩,xd⟩ | .inv=>⟨⟨sx,xd⟩,xn⟩
/-- Every raw byte agrees with legacy operation orientation/sign/padding, including signed cancellation zeros. -/
theorem rawWord_legacy (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd:List Bool) :
    rawWord op sx xn xd sy yn yd=(SemiprimeRationalBits.rawOperation (operation op) ⟨⟨sx,xn⟩,xd⟩ ⟨⟨sy,yn⟩,yd⟩).word:=by
  cases op <;> simp only [rawWord,operation,SemiprimeRationalBits.rawOperation,SemiprimeRationalBits.rawAddBits,
    SemiprimeRationalBits.rawMulBits,SemiprimeRationalBits.rawNegBits,SemiprimeRationalBits.rawInvBits,
    SemiprimeBitIndexClipping.mulSignedBits,SemiprimeBitIndexClipping.negateWord,Bool.xor_false]
/-- Whole acquired raw bank retains original inputs/magnitudes and actual cross-products until the following paid drains. -/
def rawResult (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :Words:=
  let raw:=rawWord op sx xn xd sy yn yd
  {ready op sx xn xd sy yn yd template with
    originalSigned:=raw.numerator.negative::raw.numerator.magnitude,originalRight:=raw.denominator,
    originalLeft:=if op=.add then (mulBits xn yd).bits else [],
    output:=if op=.add then (mulBits yn xd).bits else []}
/-- Exact elapsed raw stage clock comes only from the actual calls, actual sign push and actual drains. -/
def rawTime (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd:List Bool) :Nat:=match op with
  | .add=>productTime xn yd+productTime yn xd+
      sumTime sx (mulBits xn yd).bits sy (mulBits yn xd).bits+1+productTime xd yd
  | .mul=>productTime xn yn+1+productTime xd yd
  | .neg=>(5*xn.length+4)+(5*xd.length+4)+1
  | .inv=>(5*xd.length+4)+(5*xn.length+4)+1
/-- Actual add computes both oriented cross-products, borrow-driven signed sum and exact denominator product. -/
theorem add_run (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    Runs program (rawTime .add sx xn xd sy yn yd) (localLabel .dispatch .add sx sy)
      (bank (ready .add sx xn xd sy yn yd template)) (localLabel .clearMagnitudeLeft .add sx sy)
      (bank (rawResult .add sx xn xd sy yn yd template)):=by
  let w0:=ready .add sx xn xd sy yn yd template
  let w1:Words:={w0 with originalLeft:=(mulBits xn yd).bits}
  let w2:Words:={w1 with output:=(mulBits yn xd).bits}
  let sum:SemiprimeBitIndexClipping.SignedWord:=
    (SemiprimeBitIndexClipping.addSignedBits ⟨sx,(mulBits xn yd).bits⟩ ⟨sy,(mulBits yn xd).bits⟩).word
  let w3:Words:={w2 with originalSigned:=sum.magnitude}
  let w4:Words:={w3 with originalSigned:=sum.negative::sum.magnitude}
  have h0:=product_run .crossLeft .add sx sy w0 (localLabel .dispatch .add sx sy) rfl rfl rfl
  change Runs program (productTime xn yd) _ (bank w0) _ (bank w1) at h0
  have h1:=product_run .crossRight .add sx sy w1 (localLabel (.productLeft .crossRight) .add sx sy) rfl rfl rfl
  change Runs program (productTime yn xd) _ (bank w1) _ (bank w2) at h1
  have h2:=sum_run .add sx sy w2 rfl rfl
  change Runs program (sumTime sx (mulBits xn yd).bits sy (mulBits yn xd).bits) _ (bank w2) _ (bank w3) at h2
  have h3:=P.push_run (localLabel (.rawSign sum.negative) .add sx sy) (localLabel (.productLeft .denominator) .add sx sy)
    rawSigned sum.negative (bank w3) rfl
  change Runs _ _ _ _ _ (Function.update (bank w3) (normalizeStack (SemiprimeD1StackRationalNormalize.aux .originalSigned)) (sum.negative::sum.magnitude)) at h3
  rw [update_originalSigned] at h3
  have h4:=product_run .denominator .add sx sy w4 (localLabel (.productLeft .denominator) .add sx sy) rfl rfl rfl
  change Runs program (productTime xd yd) _ (bank w4) _ (bank (rawResult .add sx xn xd sy yn yd template)) at h4
  exact P.join (P.join (P.join (P.join h0 h1) h2) h3) h4
/-- Actual multiply computes both oriented full products and pushes the XOR of the two parsed signs. -/
theorem mul_run (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    Runs program (rawTime .mul sx xn xd sy yn yd) (localLabel .dispatch .mul sx sy)
      (bank (ready .mul sx xn xd sy yn yd template)) (localLabel .clearMagnitudeLeft .mul sx sy)
      (bank (rawResult .mul sx xn xd sy yn yd template)):=by
  let w0:=ready .mul sx xn xd sy yn yd template
  let w1:Words:={w0 with originalSigned:=(mulBits xn yn).bits}
  let w2:Words:={w1 with originalSigned:=(Bool.xor sx sy)::(mulBits xn yn).bits}
  have h0:=product_run .numerator .mul sx sy w0 (localLabel .dispatch .mul sx sy) rfl rfl rfl
  change Runs program (productTime xn yn) _ (bank w0) _ (bank w1) at h0
  have h1:=P.push_run (localLabel (.rawSign (Bool.xor sx sy)) .mul sx sy) (localLabel (.productLeft .denominator) .mul sx sy)
    rawSigned (Bool.xor sx sy) (bank w1) rfl
  change Runs _ _ _ _ _ (Function.update (bank w1) (normalizeStack (SemiprimeD1StackRationalNormalize.aux .originalSigned)) ((Bool.xor sx sy)::(mulBits xn yn).bits)) at h1
  rw [update_originalSigned] at h1
  have h2:=product_run .denominator .mul sx sy w2 (localLabel (.productLeft .denominator) .mul sx sy) rfl rfl rfl
  change Runs program (productTime xd yd) _ (bank w2) _ (bank (rawResult .mul sx xn xd sy yn yd template)) at h2
  exact P.join (P.join h0 h1) h2
/-- Actual unary operation copies the physical magnitude/denominator in the selected swap orientation. -/
theorem unary_run (inv:Bool) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    let op:=if inv then Op.inv else .neg
    Runs program (rawTime op sx xn xd sy yn yd) (localLabel .dispatch op sx false)
      (bank (ready op sx xn xd sy yn yd template)) (localLabel .clearMagnitudeLeft op sx false)
      (bank (rawResult op sx xn xd sy yn yd template)):=by
  dsimp only
  let op:=if inv then Op.inv else .neg
  let num:=if inv then xd else xn
  let den:=if inv then xn else xd
  let neg:=if inv then sx else !sx
  let w0:=ready op sx xn xd sy yn yd template
  let w1:Words:={w0 with originalSigned:=num}
  let w2:Words:={w1 with originalRight:=den}
  have hc0:program (localLabel .dispatch op sx false)=.call (.copier (.unaryNumerator inv) 0) (localLabel .unaryDenominator op sx false):=by cases inv <;> rfl
  have hx:bank w0 (copyStack (.unaryNumerator inv) 0)=num:=by cases inv <;> rfl
  have h0:=P.copy_call (.unaryNumerator inv) (localLabel .dispatch op sx false) (localLabel .unaryDenominator op sx false)
    hc0 (bank w0) num [] hx rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank w0) (normalizeStack (SemiprimeD1StackRationalNormalize.aux .originalSigned)) (num++[])) at h0
  rw [List.append_nil,update_originalSigned] at h0
  have hc1:program (localLabel .unaryDenominator op sx false)=.call (.copier (.unaryDenominator inv) 0) (localLabel (.rawSign neg) op sx false):=by cases inv <;> rfl
  have hy:bank w1 (copyStack (.unaryDenominator inv) 0)=den:=by cases inv <;> rfl
  have h1:=P.copy_call (.unaryDenominator inv) (localLabel .unaryDenominator op sx false) (localLabel (.rawSign neg) op sx false)
    hc1 (bank w1) den [] hy rfl rfl
  change Runs _ _ _ _ _ (Function.update (bank w1) (normalizeStack SemiprimeD1StackRationalNormalize.denominator) (den++[])) at h1
  rw [List.append_nil,update_originalRight] at h1
  have hc2:program (localLabel (.rawSign neg) op sx false)=.base (.push rawSigned neg (localLabel .clearMagnitudeLeft op sx false)):=by cases inv <;> rfl
  have h2:=P.push_run (localLabel (.rawSign neg) op sx false) (localLabel .clearMagnitudeLeft op sx false) rawSigned neg (bank w2) hc2
  change Runs _ _ _ _ _ (Function.update (bank w2) (normalizeStack (SemiprimeD1StackRationalNormalize.aux .originalSigned)) (neg::num)) at h2
  rw [update_originalSigned] at h2
  have h:=P.join (P.join h0 h1) h2
  cases inv <;> exact h
/-- One fixed actual raw-operation stage, with no raw-answer/evaluator operand. -/
theorem raw_run (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    Runs program (rawTime op sx xn xd sy yn yd)
      (localLabel .dispatch op sx (if binary op then sy else false))
      (bank (ready op sx xn xd sy yn yd template))
      (localLabel .clearMagnitudeLeft op sx (if binary op then sy else false))
      (bank (rawResult op sx xn xd sy yn yd template)):=by
  cases op with
  | add=>exact add_run sx xn xd sy yn yd template
  | mul=>exact mul_run sx xn xd sy yn yd template
  | neg=>exact unary_run false sx xn xd sy yn yd template
  | inv=>exact unary_run true sx xn xd sy yn yd template
end RiemannGaussian.SemiprimeD1StackRationalOperationRaw
