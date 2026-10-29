/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishNewton
import RiemannGaussian.SemiprimeD1StackRecoveryFinishPreparation
/-! # Exact original inverse bytes from the real precision-marker Newton loop
The actual loop repeats the literal old step in its exact word order. Native
functions below describe results only; every actual step was physically joined
from the existing real scalar programs and paid restoring copies.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishNewtonOriginal
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishWords SemiprimeD1StackRecoveryFinishNewton SemiprimeD1StackProcedureTrace
open SemiprimeBitIndexClipping (SignedWord)
namespace P
export SemiprimeD1StackRecoveryFinishPreparation (result source_prepared time)
end P
local notation "ctl"=>Label.local
/-- Every non-stage, non-counter field is retained across an actual marker and complete actual stage. -/
theorem advance_preserved (v:Values) (s:Slot) (hs:Stable s) (ht:s≠.aux .todo):advance v s=v s:=by
  rw [advance,step_preserved _ s hs,Function.update_of_ne ht]
/-- The literal old step word is acquired on every actual marker. -/
theorem advance_current (v:Values):advance v (.aux .current)=
    (SemiprimeD1OddInverseBits.step (v .width).length (v (.aux .inverseInput))
      (v (.aux .negative)) (v (.aux .two)) (v (.aux .current))).bits:=by
  rw [advance,step_current]
  rfl
/-- Every retained original/source/precision/scalar cache field survives the entire actual marker traversal. -/
theorem states_preserved (n:Nat) (v:Values) (s:Slot) (hs:Stable s) (ht:s≠.aux .todo):states n v s=v s:=by
  induction n generalizing v with
  | zero=>rfl
  | succ n ih=>rw [states,ih,advance_preserved v s hs ht]
/-- All real operator/copy workspace stays clean at the complete loop boundary. -/
theorem states_clean (n:Nat) (v:Values) (hc:Clean v):Clean (states n v):=by
  induction n generalizing v with
  | zero=>exact hc
  | succ n ih=>exact ih (advance v) (clean_advance v hc)
/-- Actual marker count entails literal empty todo tape at the loop exit, with no counter answer supplied. -/
theorem states_todo (n:Nat) (v:Values) (ht:v (.aux .todo)=List.replicate n true):states n v (.aux .todo)=[]:=by
  induction n generalizing v with
  | zero=>exact ht
  | succ n ih=>
    apply ih
    rw [advance,step_preserved _ (.aux .todo) (by simp [Stable]),Function.update_same,ht]
    rfl
/-- Proof-side literal word iteration in the actual source's tail order; not an instruction or input function. -/
def iterateWord (p:Nat) (a negative two current:List Bool):Nat→List Bool
  | 0=>current
  | n+1=>iterateWord p a negative two (SemiprimeD1OddInverseBits.step p a negative two current).bits n
/-- Exact actual current word after all actual source stages, preserving all native padding/circuit order. -/
theorem states_current (n:Nat) (v:Values):states n v (.aux .current)=
    iterateWord (v .width).length (v (.aux .inverseInput)) (v (.aux .negative)) (v (.aux .two)) (v (.aux .current)) n:=by
  induction n generalizing v with
  | zero=>rfl
  | succ n ih=>
    have hw:=advance_preserved v .width (by simp [Stable]) (by decide)
    have ha:=advance_preserved v (.aux .inverseInput) (by simp [Stable]) (by decide)
    have hn:=advance_preserved v (.aux .negative) (by simp [Stable]) (by decide)
    have ht:=advance_preserved v (.aux .two) (by simp [Stable]) (by decide)
    rw [states,ih,iterateWord,hw,ha,hn,ht,advance_current]
/-- Literal tail iteration is repeated composition of the exact same scalar-word step. -/
theorem iterateWord_iterate (p:Nat) (a negative two current:List Bool) (n:Nat):
    iterateWord p a negative two current n=(fun x=>(SemiprimeD1OddInverseBits.step p a negative two x).bits)^[n] current:=by
  induction n generalizing current with
  | zero=>rfl
  | succ n ih=>rw [iterateWord,Function.iterate_succ_apply,ih]
/-- The original inverse report loop has exactly the same repeated scalar-word step composition. -/
theorem native_iterate (p:Nat) (a negative two:List Bool) (n:Nat):
    (SemiprimeD1OddInverseBits.loop p a negative two n).bits=
      (fun x=>(SemiprimeD1OddInverseBits.step p a negative two x).bits)^[n]
        (SemiprimeD1JetScalarBits.reduce p [true]).bits:=by
  induction n with
  | zero=>rfl
  | succ n ih=>
    simpa only [SemiprimeD1OddInverseBits.loop,Function.iterate_succ_apply'] using
      congrArg (fun x=>(SemiprimeD1OddInverseBits.step p a negative two x).bits) ih
/-- The actual loop seeded by real reduced one agrees with the exact original inverse loop BYTES. -/
theorem iterateWord_native (p:Nat) (a negative two:List Bool) (n:Nat):
    iterateWord p a negative two (SemiprimeD1JetScalarBits.reduce p [true]).bits n=
      (SemiprimeD1OddInverseBits.loop p a negative two n).bits:=by
  rw [iterateWord_iterate,native_iterate]
/-- Entire actually prepared real scalar bank satisfies the actual operator cleanup invariant. -/
theorem prepared_clean (n:SignedWord) (d w:List Bool):Clean (P.result n d w):=
  ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,⟨rfl,rfl,rfl⟩,rfl⟩
/-- Actual WIDTH copied into the physical marker tape, not supplied as a decoded count. -/
theorem prepared_todo (n:SignedWord) (d w:List Bool):P.result n d w (.aux .todo)=w:=rfl
/-- Actual physically supplied precision cache is retained in all scalar calls. -/
theorem prepared_width (n:SignedWord) (d w:List Bool):P.result n d w .width=w:=rfl
/-- Exact odd-input scalar bytes physically acquired by the actual reducer. -/
theorem prepared_a (n:SignedWord) (d w:List Bool):P.result n d w (.aux .inverseInput)=
    (SemiprimeD1JetScalarBits.reduce w.length (odd d)).bits:=rfl
/-- Exact negative-one word physically acquired by real WIDTH copy. -/
theorem prepared_negative (n:SignedWord) (d w:List Bool):P.result n d w (.aux .negative)=w:=rfl
/-- Exact two word physically acquired by constant pushes and real reduction. -/
theorem prepared_two (n:SignedWord) (d w:List Bool):P.result n d w (.aux .two)=
    (SemiprimeD1JetScalarBits.reduce w.length [false,true]).bits:=rfl
/-- Exact one seed physically acquired by its actual constant push and reduction. -/
theorem prepared_one (n:SignedWord) (d w:List Bool):P.result n d w (.aux .current)=
    (SemiprimeD1JetScalarBits.reduce w.length [true]).bits:=rfl
/-- Actual current cache after exactly the physically present WIDTH markers is the ORIGINAL inverse word, without any inverse oracle. -/
theorem inverse_original (n:SignedWord) (d:List Bool) (p:Nat):
    states p (P.result n d (List.replicate p true)) (.aux .current)=
      (SemiprimeD1OddInverseBits.inverse p (odd d)).bits:=by
  rw [states_current,prepared_width,prepared_a,prepared_negative,prepared_two,prepared_one]
  simp only [List.length_replicate]
  exact iterateWord_native p _ _ _ p
/-- SAME original three-input program physically reaches the sign/final-product stage with its whole actual inverse loop paid. -/
theorem source_inverse (n:SignedWord) (d:List Bool) (hd:0<SemiprimeBitArithmetic.bitValue d) (p:Nat):
    Runs program (SemiprimeD1StackRecoveryFinishFloor.floorTime n d+P.time n d (List.replicate p true)+
      budget p (P.result n d (List.replicate p true))) (ctl .start)
      (initial (SemiprimeD1StackRecoveryFinishSetup.signedTape n) d (List.replicate p true)).data
      (ctl .signChoice) (data (states p (P.result n d (List.replicate p true)))):=
  SemiprimeD1StackRecoveryFinishPrimitives.join (P.source_prepared n d hd (List.replicate p true))
    (loop_run p (P.result n d (List.replicate p true)) (prepared_clean n d _) rfl)
end RiemannGaussian.SemiprimeD1StackRecoveryFinishNewtonOriginal
