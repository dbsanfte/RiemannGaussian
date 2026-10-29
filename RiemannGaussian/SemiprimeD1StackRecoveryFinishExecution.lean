/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishNewtonOriginal
import RiemannGaussian.SemiprimeD1StackRecoveryFinishSign
import RiemannGaussian.SemiprimeD1StackRecoveryFinishCleanup
import RiemannGaussian.SemiprimeD1StackRecoveryFinishResidue
/-! # Complete actual three-input signed recovery finish source
The SAME35-role program copies/parses/strips/rounds, prepares its actual scalar
caches, performs every precision round, applies the actual sign, computes the
real final product, drains all sixteen helpers, and genuinely halts.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishExecution
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackProcedureTrace
open SemiprimeBitIndexClipping (SignedWord)
namespace N
export SemiprimeD1StackRecoveryFinishNewton (states budget Stable Clean)
export SemiprimeD1StackRecoveryFinishNewtonOriginal
  (states_clean states_preserved prepared_clean prepared_width prepared_negative source_inverse inverse_original)
end N
namespace P
export SemiprimeD1StackRecoveryFinishPreparation (result time)
end P
namespace S
export SemiprimeD1StackRecoveryFinishSign (result word time source_run clean_result)
end S
namespace G
export SemiprimeD1StackRecoveryFinishCleanup (cleared mass source_run)
end G
namespace MP
export SemiprimeD1StackRecoveryFinishMultiply (result word time source_call)
end MP
namespace F
export SemiprimeD1StackRecoveryFinishFloor (floorTime)
end F
namespace B
export SemiprimeD1StackRecoveryFinishSetup (signedTape)
end B
local notation "ctl"=>Label.local
/-- Exact actually reached all35-role inverse boundary. -/
def inverseValues (n:SignedWord) (d:List Bool) (p:Nat):Values:=N.states p (P.result n d (List.replicate p true))
/-- Exact actual sign/copy-or-product boundary. -/
def signedValues (n:SignedWord) (d:List Bool) (p:Nat):Values:=S.result (inverseValues n d p) n.negative
/-- Exact actually reached final modular-product result, before helper drains. -/
def finalValues (n:SignedWord) (d:List Bool) (p:Nat):Values:=MP.result (signedValues n d p) .final
/-- All35 actual roles after all sixteen real helper/cache drains. -/
def resultValues (n:SignedWord) (d:List Bool) (p:Nat):Values:=G.cleared (finalValues n d p)
/-- Actual full halt has clear finite flags and no outstanding real return symbols. -/
def done (n:SignedWord) (d:List Bool) (p:Nat):C.State Stack Label:=⟨none,none,none,data (resultValues n d p),[]⟩
/-- SAME whole-source exact clock through all real cleanup, immediately before its real final halt. -/
def bodyTime (n:SignedWord) (d:List Bool) (p:Nat):Nat:=
  (F.floorTime n d+P.time n d (List.replicate p true)+N.budget p (P.result n d (List.replicate p true)))+
    S.time (inverseValues n d p) n.negative+MP.time (signedValues n d p) .final+
      (G.mass (finalValues n d p) 0+48)
/-- SAME whole-source exact transition count, including its genuine final halt. -/
def timeBound (n:SignedWord) (d:List Bool) (p:Nat):Nat:=bodyTime n d p+1
/-- Every actual arithmetic and copy workspace is clean when the complete inverse loop has returned. -/
theorem inverse_clean (n:SignedWord) (d:List Bool) (p:Nat):N.Clean (inverseValues n d p):=
  N.states_clean p _ (N.prepared_clean n d _)
/-- The physically parsed actual original sign survives the complete inverse source. -/
theorem inverse_sign (n:SignedWord) (d:List Bool) (p:Nat):inverseValues n d p (.aux .sign)=[n.negative]:=
  (N.states_preserved p _ (.aux .sign) (by simp [N.Stable]) (by decide)).trans rfl
/-- The actual destination for signed residue remains physically empty before the sign branch. -/
theorem inverse_signed_empty (n:SignedWord) (d:List Bool) (p:Nat):inverseValues n d p (.aux .signedResidue)=[]:=
  (N.states_preserved p _ (.aux .signedResidue) (by simp [N.Stable]) (by decide)).trans rfl
/-- Complete actual source through sign, final product and every actual helper drain. -/
theorem source_trace (n:SignedWord) (d:List Bool) (hd:0<SemiprimeBitArithmetic.bitValue d) (p:Nat):
    Runs program (bodyTime n d p) (ctl .start) (initial (B.signedTape n) d (List.replicate p true)).data
      (ctl .done) (data (resultValues n d p)):=by
  have h0:=N.source_inverse n d hd p
  have h1:=S.source_run (inverseValues n d p) n.negative (inverse_clean n d p)
    (inverse_sign n d p) (inverse_signed_empty n d p)
  have hc:=S.clean_result (inverseValues n d p) n.negative (inverse_clean n d p)
  have h2:=MP.source_call .final (ctl .final) (ctl (.clear 0)) (signedValues n d p) hc.multiply hc.scratch rfl
  have h3:=G.source_run (finalValues n d p)
  exact join (join (join h0 h1) h2) h3
/-- Exact real whole-program halt from ONLY the three physical signed/binary/unary inputs. -/
theorem source_run (n:SignedWord) (d:List Bool) (hd:0<SemiprimeBitArithmetic.bitValue d) (p:Nat):
    SemiprimeD1StackCalls.run program (timeBound n d p) (initial (B.signedTape n) d (List.replicate p true))=
      some (done n d p):=by
  have ht:=source_trace n d hd p
  obtain ⟨out,hr,ha⟩:=ht [] (initial (B.signedTape n) d (List.replicate p true)) ⟨rfl,rfl,rfl⟩
  have hh:=halt_run program (ctl .done) rfl (data (resultValues n d p)) [] out ha
  rw [timeBound,SemiprimeD1StackReturnLink.run_add,hr,Option.bind_some]
  exact hh
/-- Generic actual final result projection is proved before instantiating original recovery operands. -/
theorem output_projection (v:Values) (negative:Bool):
    data (G.cleared (MP.result (S.result v negative) .final)) output=
      (SemiprimeD1JetScalarBits.mul (v .width).length (S.word v negative) (v (.aux .current))).bits:=by
  rw [show output=address .output from rfl,data_get]
  simp [G.cleared,MP.result,SemiprimeD1StackRecoveryFinishMultiply.target,MP.word,
    SemiprimeD1StackRecoveryFinishPrimitives.multiplyFromLeft,SemiprimeD1StackRecoveryFinishPrimitives.multiplyFromRight,S.result]
/-- The actual physically supplied unary precision cache is retained through the inverse loop. -/
theorem inverse_width (n:SignedWord) (d:List Bool) (p:Nat):inverseValues n d p .width=List.replicate p true:=
  (N.states_preserved p _ .width (by simp [N.Stable]) (by decide)).trans rfl
/-- The actual inverse cache is EXACTthe original inverse word, not an assumed modular unit. -/
theorem inverse_word (n:SignedWord) (d:List Bool) (p:Nat):inverseValues n d p (.aux .current)=
    (SemiprimeD1OddInverseBits.inverse p (SemiprimeD1StackRecoveryFinishWords.odd d)).bits:=N.inverse_original n d p
/-- The physically copied negative-one word survives literally throughout the inverse loop. -/
theorem inverse_negative (n:SignedWord) (d:List Bool) (p:Nat):inverseValues n d p (.aux .negative)=
    (SemiprimeD1OddInverseBits.negativeOne p).bits:=
  (N.states_preserved p _ (.aux .negative) (by simp [N.Stable]) (by decide)).trans rfl
/-- The actual canonical floor magnitude cache survives all actual inverse stages. -/
theorem inverse_magnitude (n:SignedWord) (d:List Bool) (p:Nat):inverseValues n d p (.aux .numeratorResidue)=
    (SemiprimeD1JetScalarBits.reduce p (SemiprimeD1StackRecoveryFinishWords.corrected n.negative d n.magnitude)).bits:=by
  have h:(inverseValues n d p) (.aux .numeratorResidue)=
      (SemiprimeD1JetScalarBits.reduce (List.replicate p true).length
        (SemiprimeD1StackRecoveryFinishWords.corrected n.negative d n.magnitude)).bits:=
    (N.states_preserved p _ (.aux .numeratorResidue) (by simp [N.Stable]) (by decide)).trans rfl
  simpa only [List.length_replicate] using h
/-- Actual post-inverse sign circuit has the exact original compact signed-floor residue bytes. -/
theorem sign_word (n:SignedWord) (d:List Bool) (p:Nat):S.word (inverseValues n d p) n.negative=
    SemiprimeD1StackRecoveryFinishResidue.signedWord p n d:=by
  unfold S.word SemiprimeD1StackRecoveryFinishResidue.signedWord SemiprimeD1StackRecoveryFinishResidue.magnitudeResidue
  rw [inverse_width,List.length_replicate,inverse_negative,inverse_magnitude]
/-- Exact final actual scalar output is the ORIGINAL RecoveryStripBits.finish word for all signed operand padding. -/
theorem output_original (n:SignedWord) (d:List Bool) (p:Nat):
    (done n d p).data output=(SemiprimeD1RecoveryStripBits.finish p n d).bits:=by
  change data (G.cleared (MP.result (S.result (inverseValues n d p) n.negative) .final)) output=_
  rw [output_projection,inverse_width,List.length_replicate,sign_word,inverse_word]
  exact SemiprimeD1StackRecoveryFinishResidue.output_original p n d
/-- SAME actual whole source and exact original binary output, without any native-clock identification. -/
theorem source_original (n:SignedWord) (d:List Bool) (hd:0<SemiprimeBitArithmetic.bitValue d) (p:Nat):
    ∃q≤timeBound n d p,SemiprimeD1StackCalls.run program q (initial (B.signedTape n) d (List.replicate p true))=
      some (done n d p) ∧(done n d p).data output=(SemiprimeD1RecoveryStripBits.finish p n d).bits:=
  ⟨timeBound n d p,le_rfl,source_run n d hd p,output_original n d p⟩
end RiemannGaussian.SemiprimeD1StackRecoveryFinishExecution
