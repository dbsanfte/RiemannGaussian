/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRationalNormalizeStorage
import RiemannGaussian.SemiprimeD1StackWordFitExecution
import RiemannGaussian.SemiprimeD1StackMultiplierExecution
/-! # Literal rational operations, normalization and both physical width fits
Only four original operand words and one actual width template are supplied.
The complete multiplier, signed add/subtract, canonical normalization and both
fits execute on these words. All original inputs are retained. Shared arithmetic
banks are physically emptied between calls; no raw answer or width is supplied.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 262144
namespace RiemannGaussian.SemiprimeD1StackRationalOperation
namespace C
export SemiprimeD1StackCalls (Instruction State)
end C
namespace N
export SemiprimeD1StackRationalNormalize (Stack Label program)
end N
namespace M
export SemiprimeD1StackMultiplier (Stack Label code)
end M
namespace A
export SemiprimeD1StackAdder (Stack Label code)
end A
namespace S
export SemiprimeD1StackSubtractor (Label code)
end S
namespace F
export SemiprimeD1StackWordFit (Label program)
end F
/-- Four finite operations, fixed before every operand and template. -/
inductive Op where | add | mul | neg | inv deriving DecidableEq,Repr
/-- Complete finite operation inventory. -/
instance :Fintype Op:=Fintype.ofList [.add,.mul,.neg,.inv] (by intro k;cases k <;> simp)
/-- Mathematical interpretation of the actual finite operation entry. -/
def operation :Op→SemiprimeRationalBits.Operation
  | .add=>.add | .mul=>.mul | .neg=>.neg | .inv=>.inv
/-- Five retained original tapes, two acquired magnitude caches and two fitted outputs. -/
inductive Aux where | leftSigned | leftDen | rightSigned | rightDen | template | leftMagnitude | rightMagnitude | numeratorOutput | denominatorOutput
  deriving DecidableEq,Repr
/-- Complete literal caller inventory. -/
instance :Fintype Aux:=Fintype.ofList [.leftSigned,.leftDen,.rightSigned,.rightDen,.template,
  .leftMagnitude,.rightMagnitude,.numeratorOutput,.denominatorOutput] (by intro k;cases k <;> simp)
/-- All22 normalization words, five additional multiplier words and nine caller words. -/
abbrev Stack:=N.Stack⊕((Fin 3⊕Bool)⊕Aux)
/-- Complete actual normalization inclusion. -/
def normalizeStack :N.Stack→Stack:=Sum.inl
/-- Actual caller addresses. -/
def aux (k:Aux) :Stack:=.inr (.inr k)
/-- Shared four-word ripple bank, reused only after complete real cleanup. -/
def adderStack (k:A.Stack) :Stack:=normalizeStack (SemiprimeD1StackRationalNormalize.dividerStack (.inl k))
/-- Multiplier's four ripple words share the actual normalization bank; five words are additional. -/
def multiplierStack :M.Stack→Stack
  | .inl k=>adderStack k | .inr k=>.inr (.inl k)
/-- Actual shared preserving-copy scratch. -/
def copyScratch :Stack:=normalizeStack SemiprimeD1StackRationalNormalize.copyScratch
/-- Raw acquired signed numerator directly feeds the real normalization front door. -/
def rawSigned :Stack:=normalizeStack (SemiprimeD1StackRationalNormalize.aux .originalSigned)
/-- Raw acquired denominator directly feeds the real normalization front door. -/
def rawDen :Stack:=normalizeStack SemiprimeD1StackRationalNormalize.denominator
/-- First cross-product temporarily uses a normalization magnitude word, drained before its call. -/
def crossLeft :Stack:=normalizeStack SemiprimeD1StackRationalNormalize.numerator
/-- Second cross-product temporarily uses the GCD output word, drained before normalization. -/
def crossRight :Stack:=normalizeStack SemiprimeD1StackRationalNormalize.gcdOutput
/-- Exact normalized sign, retained by both magnitude fits. -/
def signOutput :Stack:=normalizeStack (SemiprimeD1StackRationalNormalize.aux .signOutput)
/-- Four exact multiplication orientations used by legacy rational add/multiply. -/
inductive Product where | crossLeft | crossRight | numerator | denominator deriving DecidableEq,Repr
/-- Complete finite multiplication inventory. -/
instance :Fintype Product:=Fintype.ofList [.crossLeft,.crossRight,.numerator,.denominator] (by intro k;cases k <;> simp)
/-- Fourteen physically distinct preserving-copy routes. -/
inductive Copy where | signedLeft | signedRight | productLeft (p:Product) | productRight (p:Product) | productSave (p:Product)
  | addLeft (reverse:Bool) | addRight (reverse:Bool) | addSave | unaryNumerator (inverse:Bool) | unaryDenominator (inverse:Bool)
  deriving DecidableEq,Fintype,Repr
/-- Original/current operands for each actual oriented product. -/
def productOperand (p:Product) (right:Bool) :Stack:=match p,right with
  | .crossLeft,false|.numerator,false=>aux .leftMagnitude
  | .crossRight,false|.numerator,true=>aux .rightMagnitude
  | .crossLeft,true|.denominator,true=>aux .rightDen
  | .crossRight,true|.denominator,false=>aux .leftDen
/-- Literal acquired destination of each completed product. -/
def productOutput :Product→Stack
  | .crossLeft=>crossLeft | .crossRight=>crossRight | .numerator=>rawSigned | .denominator=>rawDen
/-- Every copy has three distinct literal physical operands. -/
def copyStack (what:Copy) (k:Fin 3) :Stack:=
  if k=0 then match what with
    | .signedLeft=>aux .leftSigned | .signedRight=>aux .rightSigned
    | .productLeft p=>productOperand p false | .productRight p=>productOperand p true
    | .productSave _=>adderStack .right
    | .addLeft rev=>if rev then crossRight else crossLeft
    | .addRight rev=>if rev then crossLeft else crossRight
    | .addSave=>adderStack .output
    | .unaryNumerator inv=>if inv then aux .leftDen else aux .leftMagnitude
    | .unaryDenominator inv=>if inv then aux .leftMagnitude else aux .leftDen
  else if k=1 then match what with
    | .signedLeft=>aux .leftMagnitude | .signedRight=>aux .rightMagnitude
    | .productLeft _=>multiplierStack SemiprimeD1StackMultiplier.input
    | .productRight _=>multiplierStack SemiprimeD1StackMultiplier.factor
    | .productSave p=>productOutput p
    | .addLeft _=>adderStack .left | .addRight _=>adderStack .right
    | .addSave|.unaryNumerator _=>rawSigned | .unaryDenominator _=>rawDen
  else copyScratch
/-- Five distinct fit addresses; both fit calls retain the actual caller template. -/
def fitStack (den:Bool) (k:Fin 5) :Stack:=
  if k=0 then normalizeStack (SemiprimeD1StackRationalNormalize.aux (if den then .denominatorOutput else .numeratorOutput))
  else if k=1 then aux .template
  else if k=2 then normalizeStack SemiprimeD1StackRationalNormalize.x
  else if k=3 then normalizeStack SemiprimeD1StackRationalNormalize.y
  else aux (if den then .denominatorOutput else .numeratorOutput)
/-- All actual local stages; only operation bits, parsed signs and finite call routes enter control. -/
inductive Phase where
  | start | parseLeft | rightCopy | parseRight | dispatch
  | productLeft (p:Product) | productRight (p:Product) | multiply (p:Product) | productSave (p:Product) | productClear (p:Product)
  | addLeft (reverse:Bool) | addRight (reverse:Bool) | combine (reverse:Bool) | borrow (reverse:Bool)
  | discardDifference | addSave (negative:Bool) | clearDifference (negative:Bool)
  | unaryNumerator | unaryDenominator | rawSign (negative:Bool)
  | clearMagnitudeLeft | clearMagnitudeRight | clearCrossLeft | clearCrossRight
  | normalize | fit (den:Bool) | clearRawSigned | clearRawDen | done | abort
  deriving DecidableEq,Fintype,Repr
/-- Finite local controls and real included-program labels. -/
inductive Label where
  | local (phase:Phase) (op:Op) (sx sy:Bool)
  | normalize (pc:N.Label) | multiply (pc:M.Label) | adder (pc:A.Label) | subtractor (pc:S.Label)
  | copier (what:Copy) (pc:Fin 9) | fit (den:Bool) (pc:F.Label)
  deriving Fintype
/-- Literal local label constructor. -/
def localLabel (p:Phase) (op:Op) (sx sy:Bool) :Label:=.local p op sx sy
/-- Next actual product stage, never a numerical instruction. -/
def afterProduct (p:Product) (op:Op) (sx sy:Bool) :Label:=localLabel (match p with
  | .crossLeft=>.productLeft .crossRight | .crossRight=>.addLeft false
  | .numerator=>.rawSign (Bool.xor sx sy) | .denominator=>.clearMagnitudeLeft) op sx sy
/-- One fixed finite source; all arithmetic, sign selection, normalization and both fits are actual calls. -/
def program :Label→C.Instruction Stack Label
  | .normalize pc=>SemiprimeD1StackValidationLink.instruction normalizeStack Label.normalize (N.program pc)
  | .multiply pc=>SemiprimeD1StackValidationLink.instruction multiplierStack Label.multiply (M.code pc)
  | .adder pc=>SemiprimeD1StackMultiplierLink.instruction adderStack Label.adder (A.code pc)
  | .subtractor pc=>SemiprimeD1StackMultiplierLink.instruction adderStack Label.subtractor (S.code pc)
  | .copier what pc=>SemiprimeD1StackMultiplierLink.instruction (copyStack what) (Label.copier what) (SemiprimeD1StackCopy.code pc)
  | .fit den pc=>SemiprimeD1StackValidationLink.instruction (fitStack den) (Label.fit den) (F.program pc)
  | .local phase op sx sy=>
    let go:=fun p=>localLabel p op sx sy
    match phase with
    | .start=>.call (.copier .signedLeft 0) (go .parseLeft)
    | .parseLeft=>.base (.pop (aux .leftMagnitude) (go .abort)
        (localLabel (if op=.add ∨ op=.mul then .rightCopy else .dispatch) op false false)
        (localLabel (if op=.add ∨ op=.mul then .rightCopy else .dispatch) op true false))
    | .rightCopy=>.call (.copier .signedRight 0) (go .parseRight)
    | .parseRight=>.base (.pop (aux .rightMagnitude) (go .abort) (localLabel .dispatch op sx false) (localLabel .dispatch op sx true))
    | .dispatch=>match op with
      | .add=>.call (.copier (.productLeft .crossLeft) 0) (go (.productRight .crossLeft))
      | .mul=>.call (.copier (.productLeft .numerator) 0) (go (.productRight .numerator))
      | .neg|.inv=>.call (.copier (.unaryNumerator (op=.inv)) 0) (go .unaryDenominator)
    | .productLeft p=>.call (.copier (.productLeft p) 0) (go (.productRight p))
    | .productRight p=>.call (.copier (.productRight p) 0) (go (.multiply p))
    | .multiply p=>.call (.multiply (.control .start)) (go (.productSave p))
    | .productSave p=>.call (.copier (.productSave p) 0) (go (.productClear p))
    | .productClear p=>.base (.pop (adderStack .right) (afterProduct p op sx sy) (go (.productClear p)) (go (.productClear p)))
    | .addLeft rev=>.call (.copier (.addLeft rev) 0) (go (.addRight rev))
    | .addRight rev=>.call (.copier (.addRight rev) 0) (go (.combine rev))
    | .combine rev=>if sx=sy then .call (.adder (.start false)) (go (.addSave sx))
      else .call (.subtractor (.start false)) (go (.borrow rev))
    | .borrow rev=>.base (.pop (adderStack .output) (go .abort)
        (go (.addSave (if rev then sy else sx))) (if rev then go (.addSave sy) else go .discardDifference))
    | .discardDifference=>.base (.pop (adderStack .output) (go (.addLeft true)) (go .discardDifference) (go .discardDifference))
    | .addSave negative=>.call (.copier .addSave 0) (go (.clearDifference negative))
    | .clearDifference negative=>.base (.pop (adderStack .output) (go (.rawSign negative))
        (go (.clearDifference negative)) (go (.clearDifference negative)))
    | .unaryNumerator=>.call (.copier (.unaryNumerator (op=.inv)) 0) (go .unaryDenominator)
    | .unaryDenominator=>.call (.copier (.unaryDenominator (op=.inv)) 0) (go (.rawSign (if op=.neg then !sx else sx)))
    | .rawSign negative=>.base (.push rawSigned negative (if op=.add ∨ op=.mul then go (.productLeft .denominator) else go .clearMagnitudeLeft))
    | .clearMagnitudeLeft=>.base (.pop (aux .leftMagnitude) (go .clearMagnitudeRight) (go .clearMagnitudeLeft) (go .clearMagnitudeLeft))
    | .clearMagnitudeRight=>.base (.pop (aux .rightMagnitude) (go .clearCrossLeft) (go .clearMagnitudeRight) (go .clearMagnitudeRight))
    | .clearCrossLeft=>.base (.pop crossLeft (go .clearCrossRight) (go .clearCrossLeft) (go .clearCrossLeft))
    | .clearCrossRight=>.base (.pop crossRight (go .normalize) (go .clearCrossRight) (go .clearCrossRight))
    | .normalize=>.call (.normalize .start) (go (.fit false))
    | .fit den=>.call (.fit den .start) (go (if den then .clearRawSigned else .fit true))
    | .clearRawSigned=>.base (.pop rawSigned (go .clearRawDen) (go .clearRawSigned) (go .clearRawSigned))
    | .clearRawDen=>.base (.pop rawDen (go .done) (go .clearRawDen) (go .clearRawDen))
    | .done|.abort=>.base .halt
/-- The honest five-tape source initializes no arithmetic/cache/output word. -/
def input (ls ld rs rd template:List Bool) :Stack→List Bool:=
  Sum.elim (fun _=>[]) (Sum.elim (fun _=>[]) (fun k=>match k with
    | .leftSigned=>ls | .leftDen=>ld | .rightSigned=>rs | .rightDen=>rd | .template=>template | _=>[]))
/-- Finite operation entry and only five actual input tapes. -/
def initial (op:Op) (ls ld rs rd template:List Bool) :C.State Stack Label:=
  ⟨some (localLabel .start op false false),none,none,input ls ld rs rd template,[]⟩
/-- Actual fixed finite36-role machine; the finite operation chooses only its entry. -/
def machine (op:Op) :Turing.FinTM2:=SemiprimeD1StackCalls.machine (aux .leftSigned) (aux .numeratorOutput) (localLabel .start op false false) program
/-- Every allocated data role, including five additional multiplier words, is counted. -/
theorem stack_card :Fintype.card Stack=36:=by decide
/-- The complete normalization bank is injectively included. -/
theorem normalize_injective :Function.Injective normalizeStack:=Sum.inl_injective
/-- Shared four-word ripple operands are distinct. -/
theorem adder_injective :Function.Injective adderStack:=normalize_injective.comp (SemiprimeD1StackRationalNormalize.divider_injective.comp Sum.inl_injective)
/-- All nine multiplier roles are distinct despite the four-word bank reuse. -/
theorem multiplier_injective :Function.Injective multiplierStack:=by decide
/-- Every literal copy route has distinct actual operands. -/
theorem copy_injective (what:Copy) :Function.Injective (copyStack what):=by cases what <;> first | decide | (rename_i a;cases a <;> decide)
/-- Both real fit calls have five pairwise distinct actual words. -/
theorem fit_injective (den:Bool) :Function.Injective (fitStack den):=by cases den <;> decide
/-- Transient control is finite before all original data and template words. -/
theorem control_finite (op:Op) :Finite (machine op).σ:=SemiprimeD1StackCalls.control_finite _ _ _ _
/-- Boolean data and genuine finite return alphabets are finite on every actual role. -/
theorem alphabets_finite (op:Op) :∀k,Finite ((machine op).Γ k):=SemiprimeD1StackCalls.all_alphabets_finite _ _ _ _
end RiemannGaussian.SemiprimeD1StackRationalOperation
