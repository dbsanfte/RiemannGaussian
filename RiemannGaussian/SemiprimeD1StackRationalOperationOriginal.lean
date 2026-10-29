/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalOperationStorage
/-! # Exact legacy operation bytes and physical fixed-width iteration boundary
A caller can reuse a physically acquired width template after every operation.
Both output magnitudes are actually fitted; raw multiplication/division padding
never becomes an unbounded persistent representation in such an iteration.
Acquiring operation order, rational operands and canonical Hermite/grid rows is
separate work; this source has an honest five-tape prepared front door.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalOperationOriginal
open SemiprimeD1StackRationalOperation SemiprimeD1StackRationalOperationEncoding
open SemiprimeD1StackRationalOperationExecution SemiprimeD1StackRationalOperationBounds
/-- Exact entire operation source and literal executeOperation result from only original actual input words. -/
theorem source_original (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    ∃q ≤ polynomial (sx::xn) xd (sy::yn) yd template,
      SemiprimeD1StackCalls.run program q (initial op (sx::xn) xd (sy::yn) yd template)=some (done op sx xn xd sy yn yd template) ∧
      outputWord (done op sx xn xd sy yn yd template).data=
        (SemiprimeRationalBits.executeOperation (operation op) ⟨⟨sx,xn⟩,xd⟩ ⟨⟨sy,yn⟩,yd⟩ template).word:=by
  obtain ⟨q,hq,hr⟩:=source_run_bounded op sx xn xd sy yn yd template
  exact ⟨q,hq,hr,output_legacy op sx xn xd sy yn yd template⟩
/-- Both actual stopped magnitude words have precisely the physical template width, even if truncation is necessary. -/
theorem output_lengths (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    ((done op sx xn xd sy yn yd template).data (aux .numeratorOutput)).length=template.length ∧
    ((done op sx xn xd sy yn yd template).data (aux .denominatorOutput)).length=template.length:=by
  have h:=SemiprimeRationalBits.fitRationalBits_width
    (SemiprimeRationalBits.rawOperation (operation op) ⟨⟨sx,xn⟩,xd⟩ ⟨⟨sy,yn⟩,yd⟩).word template
  have he:=output_legacy op sx xn xd sy yn yd template
  have hn:=congrArg (fun w:SemiprimeRationalBits.RationalWord=>w.numerator.magnitude.length) he
  have hd:=congrArg (fun w:SemiprimeRationalBits.RationalWord=>w.denominator.length) he
  exact ⟨hn.trans h.1,hd.trans h.2⟩
/-- Actual left sign-prefixed word is retained byte for byte, independently of operation branch. -/
theorem left_signed_retained (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    (done op sx xn xd sy yn yd template).data (aux .leftSigned)=sx::xn:=rfl
/-- Actual left unsigned denominator is retained byte for byte. -/
theorem left_den_retained (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    (done op sx xn xd sy yn yd template).data (aux .leftDen)=xd:=rfl
/-- Unary operations retain the unread right signed input, as do both binary branches. -/
theorem right_signed_retained (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    (done op sx xn xd sy yn yd template).data (aux .rightSigned)=sy::yn:=rfl
/-- Actual right unsigned denominator is retained byte for byte. -/
theorem right_den_retained (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    (done op sx xn xd sy yn yd template).data (aux .rightDen)=yd:=rfl
/-- Real fit calls retain the literal supplied template, including every false cell. -/
theorem template_retained (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    (done op sx xn xd sy yn yd template).data (aux .template)=template:=rfl
/-- Every acquired GCD/Divider18 role is physically empty at whole halt, including the retained raw denominator. -/
theorem arithmetic_clear (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool)
    (k:SemiprimeD1StackEuclidGCD.Stack) :
    (done op sx xn xd sy yn yd template).data (normalizeStack (SemiprimeD1StackRationalNormalize.gcdStack k))=[]:=by
  rcases k with k|k
  · rcases k with k|k <;> cases k <;> rfl
  · cases k <;> rfl
/-- All five additional multiplier words are physically empty, with no displaced bank/shadow omitted. -/
theorem multiplier_clear (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) (k:Fin 3⊕Bool) :
    (done op sx xn xd sy yn yd template).data (.inr (.inl k))=[]:=by
  rcases k with k|k
  · fin_cases k <;> rfl
  · cases k <;> rfl
/-- Both parsed magnitude caches are actually drained before normalization. -/
theorem magnitudes_clear (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    (done op sx xn xd sy yn yd template).data (aux .leftMagnitude)=[] ∧
    (done op sx xn xd sy yn yd template).data (aux .rightMagnitude)=[]:=⟨rfl,rfl⟩
/-- Both intermediate normalized magnitude outputs are consumed by the TWO actual fit calls. -/
theorem normalized_outputs_clear (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) :
    (done op sx xn xd sy yn yd template).data (normalizeStack (SemiprimeD1StackRationalNormalize.aux .originalSigned))=[] ∧
    (done op sx xn xd sy yn yd template).data (normalizeStack (SemiprimeD1StackRationalNormalize.aux .numeratorOutput))=[] ∧
    (done op sx xn xd sy yn yd template).data (normalizeStack (SemiprimeD1StackRationalNormalize.aux .denominatorOutput))=[]:=⟨rfl,rfl,rfl⟩
/-- Fixed physical width closes the byte-growth recurrence for EACH real operation; no semantic height alone is used to charge bytes. -/
theorem polynomial_at_width (op:Op) (sx:Bool) (xn xd:List Bool) (sy:Bool) (yn yd template:List Bool) (W:Nat)
    (hxn:xn.length ≤ W) (hxd:xd.length ≤ W) (hyn:yn.length ≤ W) (hyd:yd.length ≤ W) (hw:template.length ≤ W) :
    runBound op sx xn xd sy yn yd template ≤(100000000000000000000*5^6)*(W+1)^6:=by
  have hs:inputSize (sx::xn) xd (sy::yn) yd template ≤5*(W+1):=by unfold inputSize;simp only [List.length_cons];omega
  have hp: (inputSize (sx::xn) xd (sy::yn) yd template)^6 ≤(5*(W+1))^6:=Nat.pow_le_pow_left hs 6
  have ht:=runBound_le op sx xn xd sy yn yd template
  unfold polynomial at ht
  nlinarith only [ht,hp]
end RiemannGaussian.SemiprimeD1StackRationalOperationOriginal
