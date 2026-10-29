/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCorrectedPortBits

/-! # Physical corrected-port buffer widths and clocks
Every lower arithmetic report is retained. Initial cache acquisition and the
execution of natural clock/address metadata remain explicitly separate.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
namespace RiemannGaussian.SemiprimeCorrectedPortBitsBounds
open SemiprimeCorrectedPortBits SemiprimeRationalBits SemiprimeDotBits SemiprimeJetBits

/-- Literal zero occupies one denominator bit and no numerator magnitude bits. -/
theorem zero_width {W : ℕ} (hW : 0< W) : Width zeroWord W := by
  constructor <;> simp only [zeroWord,List.length_nil,List.length_cons] <;> omega

/-- Actual allocated zero buffers fit every positive common width. -/
theorem zeroBits_bounded (J W : ℕ) (hW : 0< W) : Bounded (zeroBits J).words W := by
  intro i hi
  simpa only [zeroBits,Array.getElem_replicate] using zero_width hW

/-- The constant copy preserves the acquired source word width. -/
theorem constantBits_bounded (template : List Bool) (a : Array RationalWord) (start J : ℕ)
    (ht : 0< template.length) (ha : Bounded a template.length) :
    Bounded (constantBits template a start J).words template.length := by
  intro i hi
  simp only [constantBits,Array.getElem_ofFn]
  split_ifs
  · exact wordAt_width a ht ha _
  · exact zero_width ht

/-- Independent Boolean masks only copy existing words or literal zeros. -/
theorem maskShift_bounded (template : List Bool) (a : Array RationalWord) (base correction : Bool) (J : ℕ)
    (ht : 0< template.length) (ha : Bounded a template.length) :
    Bounded (maskShift template a base correction J).words template.length := by
  intro i hi
  simp only [maskShift,Array.getElem_ofFn]
  split_ifs <;> first | exact wordAt_width a ht ha _ | exact zero_width ht

/-- All physical Horner outputs occupy the common executed template width. -/
theorem shiftFrom_bounded (template : List Bool) (a : Array RationalWord) (t : RationalWord)
    (J start len : ℕ) (ht : 0< template.length) :
    Bounded (shiftFrom template a t J start len).words template.length := by
  cases len with
  | zero => exact zeroBits_bounded J _ ht
  | succ len => exact addBits_bounded template _ _ J

/-- Full corrected-port outputs occupy the same physical width. -/
theorem acquireCorrected_bounded (template : List Bool) (source : ℕ → Array RationalWord)
    (t : RationalWord) (R J : ℕ) (base correction : ℕ → Bool) (n : ℕ) (ht : 0< template.length) :
    Bounded (acquireCorrected template source t R J base correction n).words template.length := by
  cases n with
  | zero => exact zeroBits_bounded J _ ht
  | succ n => exact addBits_bounded template _ _ J

/-- Finite-source counterpart of the physical output width theorem. -/
theorem acquireCorrectedFin_bounded {n : ℕ} (template : List Bool) (source : Fin n → Array RationalWord)
    (t : RationalWord) (R J : ℕ) (base correction : Fin n → Bool) (ht : 0< template.length) :
    Bounded (acquireCorrectedFin template source t R J base correction).words template.length :=
  acquireCorrected_bounded template _ t R J _ _ n ht

/-- Finite physical port output has exactly the requested retained precision. -/
@[simp] theorem acquireCorrectedFin_size {n : ℕ} (template : List Bool) (source : Fin n → Array RationalWord)
    (t : RationalWord) (R J : ℕ) (base correction : Fin n → Bool) :
    (acquireCorrectedFin template source t R J base correction).words.size=J :=
  acquireCorrected_size template _ t R J _ _ n

/-- The affine physical Horner multiplier has no hidden coefficient supplier. -/
theorem linear_bounded (template : List Bool) (tw : RationalWord)
    (ht : 0< template.length) (htw : Width tw template.length) :
    Bounded #[tw,oneWord] template.length := by
  intro i hi
  have hi' : i<2 := by simpa using hi
  interval_cases i
  · simpa using htw
  · simpa using oneWord_width ht

/-- Physical truncated product budget, with actual source/buffer addressing. -/
def multiplyBudget (W J : ℕ) : ℕ :=
  J*(J*(40000*(W+1)^3+4)+4+J*((J+1)*(2*W+3)+3*(2*W+3)))+(2*J+1)

/-- Physical addition budget for two acquired buffers of exactly J words. -/
def addBudget (W J : ℕ) : ℕ :=
  J*(20000*(W+1)^3+(J+1)*(2*W+3)+(J+1)*(2*W+3))+(2*J+1)

/-- Every Horner step includes product, original coefficient copy, final add
and finite call/branch/control work. -/
def shiftStepBudget (W A J : ℕ) : ℕ :=
  multiplyBudget W J+(J*(2*W+4)+(A+1)*(2*W+3)+3)+addBudget W J+7

/-- Literal mask clock for an already acquired J-word row. -/
def maskBudget (W J : ℕ) : ℕ := J*((J+1)*(2*W+3)+2*W+6)+3

/-- Complete physical corrected-port clock polynomial, before initial source
cache acquisition and any caller-specific abstract source-array getter. -/
def portBudget (W A R J n : ℕ) : ℕ :=
  n*((R+1)*shiftStepBudget W A J+(3*J+1)+maskBudget W J+addBudget W J+8)+(3*J+1)

/-- Exact physical Horner clock, derived from all invoked scalar instructions. -/
theorem shiftFrom_clock (template : List Bool) (a : Array RationalWord) (tw : RationalWord)
    (J start len A : ℕ) (ht : 0< template.length) (ha : Bounded a template.length)
    (htw : Width tw template.length) (hsize : a.size≤ A) :
    (shiftFrom template a tw J start len).clock≤
      len*shiftStepBudget template.length A J+(3*J+1) := by
  induction len generalizing start with
  | zero => simp [shiftFrom,zeroBits]
  | succ len ih =>
    let old := shiftFrom template a tw J (start+1) len
    have ho := ih (start+1)
    have hm := multiplyBits_cost template ht old.words #[tw,oneWord] J
      (shiftFrom_bounded template a tw J (start+1) len ht) (linear_bounded template tw ht htw)
    have hlin : #[tw,oneWord].size=2 := by simp
    have hm' : (multiplyBits template old.words #[tw,oneWord] J).clock≤ multiplyBudget template.length J := by
      simpa only [multiplyBudget,accessCost,shiftFrom_size,hlin,old] using hm
    have hc : (constantBits template a start J).clock≤
        J*(2*template.length+4)+(A+1)*(2*template.length+3)+3 := by
      unfold constantBits accessCost
      dsimp only
      gcongr
    have hh := addBits_cost template ht (constantBits template a start J).words
      (multiplyBits template old.words #[tw,oneWord] J).words J
      (constantBits_bounded template a start J ht ha) (multiplyBits_bounded template ht _ _ J)
    have hh' : (addBits template (constantBits template a start J).words
        (multiplyBits template old.words #[tw,oneWord] J).words J).clock≤ addBudget template.length J := by
      simpa only [addBudget,accessCost,constantBits_size,multiplyBits_size] using hh
    dsimp only [old] at ho hm' hh' ⊢
    change _+_+_+_+7≤_
    calc
      _ ≤ (len*shiftStepBudget template.length A J+(3*J+1))+multiplyBudget template.length J+
          (J*(2*template.length+4)+(A+1)*(2*template.length+3)+3)+addBudget template.length J+7 := by omega
      _ = _ := by unfold shiftStepBudget; ring

/-- All actual row shifts, masks, prefix additions and finite controls are paid. -/
theorem acquireCorrected_clock (template : List Bool) (source : ℕ → Array RationalWord)
    (tw : RationalWord) (R J n A : ℕ) (base correction : ℕ → Bool)
    (ht : 0< template.length) (htw : Width tw template.length)
    (ha : ∀ v< n,Bounded (source v) template.length) (hsize : ∀ v< n,(source v).size≤ A) :
    (acquireCorrected template source tw R J base correction n).clock≤
      portBudget template.length A R J n := by
  induction n with
  | zero => simp [acquireCorrected,zeroBits,portBudget]
  | succ n ih =>
    have ho := ih (fun v hv => ha v (by omega)) (fun v hv => hsize v (by omega))
    have hr := shiftFrom_clock template (source n) tw J 0 (R+1) A ht (ha n (by omega)) htw (hsize n (by omega))
    have hm : (maskShift template (shiftRow template (source n) tw R J).words
        (base n) (correction n) J).clock=maskBudget template.length J := by
      simp only [maskShift,maskBudget,accessCost,shiftRow,shiftFrom_size]
    have hh := addBits_cost template ht
      (acquireCorrected template source tw R J base correction n).words
      (maskShift template (shiftRow template (source n) tw R J).words (base n) (correction n) J).words J
      (acquireCorrected_bounded template source tw R J base correction n ht)
      (maskShift_bounded template _ _ _ J ht (shiftFrom_bounded template (source n) tw J 0 (R+1) ht))
    have hh' : (addBits template (acquireCorrected template source tw R J base correction n).words
        (maskShift template (shiftRow template (source n) tw R J).words (base n) (correction n) J).words J).clock≤
        addBudget template.length J := by
      simpa only [addBudget,accessCost,acquireCorrected_size,maskShift_size] using hh
    change _+_+_+_+8≤_
    change (shiftRow template (source n) tw R J).clock≤_ at hr
    rw [hm]
    unfold portBudget at ho ⊢
    nlinarith only [ho,hr,hh']

/-- Finite source cache wrapper retains the same physical clock. -/
theorem acquireCorrectedFin_clock {n : ℕ} (template : List Bool) (source : Fin n → Array RationalWord)
    (tw : RationalWord) (R J A : ℕ) (base correction : Fin n → Bool)
    (ht : 0< template.length) (htw : Width tw template.length)
    (ha : ∀ v,Bounded (source v) template.length) (hsize : ∀ v,(source v).size≤ A) :
    (acquireCorrectedFin template source tw R J base correction).clock≤ portBudget template.length A R J n := by
  apply acquireCorrected_clock template _ tw R J n A _ _ ht htw
  · intro v hv
    simpa only [dite_eq_left hv] using ha ⟨v,hv⟩
  · intro v hv
    simpa only [dite_eq_left hv] using hsize ⟨v,hv⟩

end RiemannGaussian.SemiprimeCorrectedPortBitsBounds
