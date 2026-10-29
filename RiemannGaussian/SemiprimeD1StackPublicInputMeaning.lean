/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeD1StackPublicInput
import RiemannGaussian.SemiprimeD1StackPublicZeroOriginal
/-! # Pure original-entry meaning of the actual public input checker
All definitions below describe actually acquired cells. They are proof-side
postconditions, not runtime/cache/width/truth advice. No clock is transferred.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
namespace RiemannGaussian.SemiprimeD1StackPublicInputMeaning
open SemiprimeMacroGraph SemiprimeMacroParameters SemiprimeBitArithmetic
open SemiprimeMacroEntryBitCheck SemiprimeMacroEntryBitPrimitives
/-- The SAME physically acquired public width cache. -/
abbrev cached := SemiprimeD1StackPublicZeroExecution.cached
/-- Actual unchanged-padding word emitted by WordBlock. -/
def word (bits raw : List Bool) : List Bool := SemiprimeD1StackWordBlockExecution.result raw (cached bits)
/-- Actual flag byte immediately AFTER the acquired word-width block. -/
def rawFlag (bits raw : List Bool) : Bool := ((raw.drop (cached bits).length).head?).getD false
/-- Actual completed bound, derived from N and the physical index. -/
def actualBound (bits index : List Bool) : List Bool :=
  SemiprimeD1StackInputWidthExecution.bound (SemiprimeD1StackPublicInputWidthExecution.cache bits index)
/-- Semantic postcondition of the literal executed branches, not a supplied predicate. -/
def expected (bits raw index : List Bool) : Bool :=
  if 0<SemiprimeD1StackInputWidthExecution.width (SemiprimeD1StackPublicInputWidthExecution.cache bits index) then
    SemiprimeD1StackWordLessExecution.answer (word bits raw) (actualBound bits index) &&
      decide (rawFlag bits raw= !(if index.isEmpty then
        SemiprimeD1StackWordLessExecution.answer (word bits raw) [false,true]
        else decide (bitValue (word bits raw)=0)))
  else decide (bitValue (word bits raw)=0)
/-- Core's actual comparison orientation is exactly the old flag equality. -/
theorem flag_orientation (test flag : Bool) : ((!test)==flag)=decide (flag= !test) := by
  cases test <;> cases flag <;> rfl
/-- Acquired word bytes equal the original ordered first word block, including
ALL zero padding; the optional active flag is NOT part of the word. -/
theorem word_slots (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits)))) )→Bool) :
    word bits (List.ofFn input)=localWord (fun bit=>input (localSlotFinEquiv (.input side i) (.inl bit))) := by
  have hw:=SemiprimeD1StackPublicZeroOriginal.public_width bits hc
  have hl : (cached bits).length≤(List.ofFn input).length := by
    rw [List.length_ofFn,hw]
    simp only [arity]
    omega
  unfold word
  rw [SemiprimeD1StackWordBlockExecution.result_take _ _ hl]
  unfold localWord portBits
  apply List.ext_getElem
  · rw [List.length_take,Nat.min_eq_left hl,List.length_ofFn,hw]
  · intro j hj hj'
    simp only [List.getElem_take,List.getElem_ofFn]
    congr 1
/-- The next actual raw cell is EXACTLY the original active flag slot. -/
theorem flag_slot (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (ha : i.val<digitCount (bitLength (bitValue bits)))
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits)))) )→Bool) :
    rawFlag bits (List.ofFn input)=input (localSlotFinEquiv (.input side i) (.inr ⟨⟨i.val,ha⟩,rfl⟩)) := by
  have hw:=SemiprimeD1StackPublicZeroOriginal.public_width bits hc
  have hl : (cached bits).length<(List.ofFn input).length := by
    rw [List.length_ofFn,hw]
    simp only [arity,ha,ite_true]
    omega
  unfold rawFlag
  rw [List.head?_drop,List.getElem?_eq_getElem hl]
  simp only [List.getElem_ofFn,Option.getD_some]
  congr 1
  apply Fin.ext
  change (cached bits).length=firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))+1+0
  omega
/-- Numeric zero comparison has exactly the old physical equalBits meaning. -/
theorem zero_answer (w : List Bool) : decide (bitValue w=0)=(equalBits w []).accepted := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq,equalBits_correct]
  rfl
/-- Actual empty/nonempty physical index gives exactly the original first/nonfirst flag rule. -/
theorem flag_answer (index w : List Bool) (flag : Bool) :
    decide (flag= !(if index.isEmpty then SemiprimeD1StackWordLessExecution.answer w [false,true]
      else decide (bitValue w=0)))=(flagRun index.length w flag).accepted := by
  cases index <;> simp [flagRun,SemiprimeD1StackWordLessExecution.original_answer,zero_answer]
/-- Exact old bound word from the actual bound producer, for every position. -/
theorem bound_original (bits index : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits) :
    actualBound bits index=boundBits (activeDigitBits (bitLength (bitValue bits)) index.length) := by
  rw [show actualBound bits index=(SemiprimeD1StackPublicInputWidthExecution.done bits index).data
    SemiprimeD1StackPublicInputWidth.output from
      (SemiprimeD1StackPublicInputWidthExecution.output_bound bits index).symm]
  exact SemiprimeD1StackPublicInputWidthOriginal.output_original bits index hc
/-- ALL original ordered input assignments, active or inactive, have EXACTLY
the old public input entry verdict. No bound/flag/word/truth answer is assumed. -/
theorem expected_original (bits : List Bool) (hc : SemiprimeSourceCompactBits.Compact bits)
    (hN : 0<bitValue bits) (side : Fin 2)
    (i : Fin (firstAxis (bitLength (bitValue bits))*secondAxis (bitLength (bitValue bits))))
    (index : List Bool) (hi : index.length=i.val)
    (input : Fin (arity (.input side i : Vertex (firstAxis (bitLength (bitValue bits)))
      (secondAxis (bitLength (bitValue bits))) (digitCount (bitLength (bitValue bits)))))→Bool) :
    expected bits (List.ofFn input) index=
      (publicBitEntry (bitValue bits) hN (.input side i) input).accepted := by
  let p:=SemiprimePublicFactorCount.publicConfig (bitValue bits) hN
  have hp:=publicBitEntry_correct (bitValue bits) hN (.input side i) input
  have he:=entryRun_correct p (configTargets p) (.input side i) input
  have hz : expected bits (List.ofFn input) index=
      (entryRun p (configTargets p) (.input side i) input).accepted := by
    have hw:=word_slots bits hc side i input
    have hact : 0<SemiprimeD1StackInputWidthExecution.width
        (SemiprimeD1StackPublicInputWidthExecution.cache bits index) ↔
        i.val<digitCount (bitLength (bitValue bits)) := by
      simpa only [hi] using SemiprimeD1StackPublicInputWidthOriginal.active_iff bits index hc hN
    unfold expected
    rw [bound_original bits index hc,SemiprimeD1StackWordLessExecution.original_answer,
      flag_answer,hi,hw]
    dsimp only [entryRun,localRun]
    by_cases ha : i.val<digitCount (bitLength (bitValue bits))
    · rw [ite_eq_left (hact.mpr ha)]
      have hap : i.val<p.digits := ha
      simp only [hap,dite_true]
      let w:=localWord (fun bit=>input (localSlotFinEquiv (.input side i) (.inl bit)))
      exact congrArg (fun flag : Bool=>
        (lessBits w (boundBits (activeDigitBits (bitLength (bitValue bits)) i.val))).accepted &&
          (flagRun i.val w flag).accepted) (flag_slot bits hc side i ha input)
    · rw [ite_eq_right (by intro h;exact ha (hact.mp h))]
      have hap : ¬i.val<p.digits := ha
      simp only [hap,dite_false]
      exact zero_answer _
  exact hz.trans (he.trans hp.symm)

end RiemannGaussian.SemiprimeD1StackPublicInputMeaning
