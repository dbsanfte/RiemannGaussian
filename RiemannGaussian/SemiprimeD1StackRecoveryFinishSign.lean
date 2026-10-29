/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishNewton
/-! # Actual finite sign branch after original inverse acquisition
The branch peeks the actual parsed sign tape. Negative numerators execute the
real cached negative-one product; positive numerators execute a real preserving
copy of the already acquired canonical floor-magnitude residue.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishSign
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishPrimitives SemiprimeD1StackRecoveryFinishMoves
open SemiprimeD1StackRecoveryFinishNewton SemiprimeD1StackProcedureTrace
local notation "ctl"=>Label.local
/-- Exact acquired signed residue word; numerical binary words are never decoded or reencoded. -/
def word (v:Values) (negative:Bool):List Bool:=
  if negative then (SemiprimeD1JetScalarBits.mul (v .width).length (v (.aux .negative)) (v (.aux .numeratorResidue))).bits
  else v (.aux .numeratorResidue)
/-- Full actual finite sign/read/copy-or-product source clock. -/
def time (v:Values) (negative:Bool):Nat:=
  1+(if negative then MP.time v .signed else 5*(v (.aux .numeratorResidue)).length+4)
/-- All real scalar/copy workspace remains clear; only the actual signed cache is written. -/
def result (v:Values) (negative:Bool):Values:=Function.update v (.aux .signedResidue) (word v negative)
/-- The SAME literal sign branch physically writes the actual signed residue and preserves every original/cache word. -/
theorem source_run (v:Values) (negative:Bool) (hc:Clean v) (hn:v (.aux .sign)=[negative])
    (ht:v (.aux .signedResidue)=[]):
    Runs program (time v negative) (ctl .signChoice) (data v) (ctl .final) (data (result v negative)):=by
  have h0:=peek_view (ctl .signChoice) (ctl .abort) (ctl .positive) (ctl .signed) (.aux .sign) v rfl
  rw [hn] at h0
  cases negative with
  | false=>
    have h1:=copy_view .positive (ctl .positive) (ctl .final) v rfl hc.scratch
    simp only [copyFrom,copyTo,ht,List.append_nil] at h1
    exact join h0 h1
  | true=>
    have h1:=MP.source_call .signed (ctl .signed) (ctl .final) v hc.multiply hc.scratch rfl
    exact join h0 h1
/-- The actual full sign stage preserves every real operator/copy cleanup invariant. -/
theorem clean_result (v:Values) (negative:Bool) (hc:Clean v):Clean (result v negative):=
  ⟨⟨hc.multiply.left,hc.multiply.right,hc.multiply.counter,hc.multiply.accumulator,hc.multiply.output⟩,
    ⟨hc.add.left,hc.add.right,hc.add.output⟩,hc.scratch⟩
end RiemannGaussian.SemiprimeD1StackRecoveryFinishSign
