/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackRecoveryFinishExecution
/-! # Literal retained inputs and cleared full35-role final bank
Every original input word is preserved. Every other allocated role except the
actual compact output is physically empty, including the unused add WIDTH shadow.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 65536
namespace RiemannGaussian.SemiprimeD1StackRecoveryFinishRetention
open SemiprimeD1StackRecoveryFinish SemiprimeD1StackRecoveryFinishState
open SemiprimeD1StackRecoveryFinishExecution
open SemiprimeBitIndexClipping (SignedWord)
/-- Actual original numerator survives all physically executed inverse stages. -/
theorem inverse_numerator (n:SignedWord) (d:List Bool) (p:Nat):inverseValues n d p (.aux .numerator)=B.signedTape n:=
  (N.states_preserved p _ (.aux .numerator) (by simp [N.Stable]) (by decide)).trans rfl
/-- Actual original binary denominator survives every physically executed inverse stage. -/
theorem inverse_denominator (n:SignedWord) (d:List Bool) (p:Nat):inverseValues n d p (.aux .denominator)=d:=
  (N.states_preserved p _ (.aux .denominator) (by simp [N.Stable]) (by decide)).trans rfl
/-- Generic actual finalization preserves every original input; the statement is proved before original operands are instantiated. -/
theorem original_projection (v:Values) (negative:Bool) (s:Slot)
    (hs:s=.width ∨s=.aux .numerator ∨s=.aux .denominator):
    data (G.cleared (MP.result (S.result v negative) .final)) (address s)=v s:=by
  rw [data_get]
  rcases hs with rfl|rfl|rfl <;> rfl
/-- Generic all35-role finalization empties every actual private/cache/operand word except its actual result. -/
theorem work_projection (v:Values) (negative:Bool) (hc:N.Clean v) (k:Stack)
    (hn:k≠aux .numerator) (hd:k≠aux .denominator) (hw:k≠width) (ho:k≠output):
    data (G.cleared (MP.result (S.result v negative) .final)) k=[]:=by
  by_cases hex:∃s,k=address s
  · obtain ⟨s,rfl⟩:=hex
    rw [data_get]
    cases s with
    | width=>exact (hw rfl).elim
    | output=>exact (ho rfl).elim
    | mulLeft=>exact hc.multiply.left
    | mulRight=>exact hc.multiply.right
    | reduceWidth=>exact hc.multiply.counter
    | reduceInput=>exact hc.multiply.accumulator
    | addLeft=>exact hc.add.left
    | addRight=>exact hc.add.right
    | addOutput=>exact hc.add.output
    | aux a=>
      cases a with
      | numerator=>exact (hn rfl).elim
      | denominator=>exact (hd rfl).elim
      | _=>rfl
  · exact data_other _ k (by simpa only [not_exists] using hex)
/-- The original complete signed binary numerator is retained literally at the actual halt. -/
theorem numerator_retained (n:SignedWord) (d:List Bool) (p:Nat):(done n d p).data (aux .numerator)=B.signedTape n:=
  (original_projection (inverseValues n d p) n.negative (.aux .numerator) (Or.inr (Or.inl rfl))).trans
    (inverse_numerator n d p)
/-- The original binary denominator is retained literally at the actual halt. -/
theorem denominator_retained (n:SignedWord) (d:List Bool) (p:Nat):(done n d p).data (aux .denominator)=d:=
  (original_projection (inverseValues n d p) n.negative (.aux .denominator) (Or.inr (Or.inr rfl))).trans
    (inverse_denominator n d p)
/-- The original physically supplied unary WIDTH is retained literally at the actual halt. -/
theorem width_retained (n:SignedWord) (d:List Bool) (p:Nat):(done n d p).data width=List.replicate p true:=
  (original_projection (inverseValues n d p) n.negative .width (Or.inl rfl)).trans (inverse_width n d p)
/-- Every one of the other31allocated roles is physically empty; no alias-shadow or operator workspace is ignored. -/
theorem work_empty (n:SignedWord) (d:List Bool) (p:Nat) (k:Stack)
    (hn:k≠aux .numerator) (hd:k≠aux .denominator) (hw:k≠width) (ho:k≠output):
    (done n d p).data k=[]:=
  work_projection (inverseValues n d p) n.negative (inverse_clean n d p) k hn hd hw ho
/-- Exact physical all35-role final store consists only of retained three inputs and the actual old compact output. -/
theorem result_eq (n:SignedWord) (d:List Bool) (p:Nat):
    (done n d p).data=Function.update (input (B.signedTape n) d (List.replicate p true)) output
      (SemiprimeD1RecoveryStripBits.finish p n d).bits:=by
  funext k
  by_cases hk:k=output
  · subst k
    rw [Function.update_same,output_original]
  · rw [Function.update_of_ne hk]
    by_cases hn:k=aux .numerator
    · subst k
      exact numerator_retained n d p
    · by_cases hd:k=aux .denominator
      · subst k
        exact denominator_retained n d p
      · by_cases hw:k=width
        · subst k
          exact width_retained n d p
        · rw [work_empty n d p k hn hd hw hk]
          simp only [input,Function.update_of_ne hw,Function.update_of_ne hd,Function.update_of_ne hn]
end RiemannGaussian.SemiprimeD1StackRecoveryFinishRetention
