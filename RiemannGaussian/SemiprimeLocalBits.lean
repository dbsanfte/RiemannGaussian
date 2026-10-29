/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeJetBits
import RiemannGaussian.SemiprimeLocalExecutionBitBounds

/-! # Physical-word local multilinear interpolation
Truth entries are actual signed words. Recursive branches and all rational word
operations are executed, cached, and charged; interpretation is proof-only.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeLocalBits
open scoped BigOperators
open SemiprimeRationalBits SemiprimeDotBits SemiprimeJetBits
open SemiprimeBitIndexClipping SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeLocalArrayFrontend SemiprimeLocalExecutionHeight

/-- Actual signed integer entry and the callback's paid bit work. -/
structure EntryWord where
  /-- Physical signed integer output. -/
  bits : SignedWord
  /-- Actual callback work. -/
  clock : ℕ

/-- Denominator-one encoding; no rational-valued supplier is called. -/
def EntryWord.rational (e : EntryWord) : RationalWord := ⟨e.bits,[true]⟩

/-- The frozen integer table used only by the refinement statement. -/
def table {w : ℕ} (T : (Fin w → Bool) → EntryWord) (eta : Fin w → Bool) : EntryReport :=
  ⟨(T eta).bits.value,0,0⟩

@[simp] theorem entry_value (e : EntryWord) : e.rational.value=(e.bits.value : ℚ) := by
  simp [EntryWord.rational,RationalWord.value,SemiprimeBitArithmetic.bitValue,SemiprimeBitArithmetic.bitNat]

/-- Every integer-entry word has a legal literal denominator. -/
theorem entry_valid (e : EntryWord) : e.rational.Valid := by change 0<1; decide

/-- Materialized literal one jet. -/
def oneArray (J : ℕ) : Array RationalWord :=
  Array.ofFn (fun i : Fin J => if i.val=0 then oneWord else zeroWord)

@[simp] theorem oneArray_size (J : ℕ) : (oneArray J).size=J := by simp [oneArray]

theorem oneArray_valid (J : ℕ) : Valid (oneArray J) := by
  intro i hi
  simp only [oneArray,Array.getElem_ofFn]
  split_ifs <;> exact (by change 0<1; decide)

theorem oneArray_bounded (J W : ℕ) (hW : 0<W) : Bounded (oneArray J) W := by
  intro i hi
  simp only [oneArray,Array.getElem_ofFn]
  split_ifs
  · exact oneWord_width hW
  · simp only [zeroWord,Width,List.length_nil,List.length_cons]
    omega

theorem oneArray_coefficient (J i : ℕ) (hi : i<J) :
    coefficient (decode (oneArray J)) i = coefficient (SemiprimeArrayOps.oneJet J).coefficients i := by
  simp [oneArray,decode,coefficient,hi,SemiprimeArrayOps.oneJet,apply_ite,zeroWord_value]

/-- Cached depth-first physical evaluator, with the actual leaf callback clock. -/
def localEvaluateBits (template : List Bool) (J : ℕ) : (w : ℕ) →
    ((Fin w → Bool) → EntryWord) → (Fin w → Array RationalWord) → JetReport
  | 0,T,_ =>
      let e := T Fin.elim0
      let one := oneArray J
      let out := scaleBits template one e.rational J
      ⟨out.words,e.clock+out.clock+3*J+4⟩
  | w+1,T,inputs =>
      let lo := localEvaluateBits template J w (fun eta => T (Fin.cons false eta)) (fun i => inputs i.succ)
      let hi := localEvaluateBits template J w (fun eta => T (Fin.cons true eta)) (fun i => inputs i.succ)
      let one := oneArray J
      let neg := scaleBits template (inputs 0) negOneWord J
      let no := addBits template one neg.words J
      let left := multiplyBits template no.words lo.words J
      let right := multiplyBits template (inputs 0) hi.words J
      let out := addBits template left.words right.words J
      ⟨out.words,lo.clock+hi.clock+neg.clock+no.clock+left.clock+right.clock+out.clock+3*J+12⟩

/-- Every physical branch result has the retained width. -/
theorem localEvaluateBits_size (template : List Bool) (J w : ℕ)
    (T : (Fin w → Bool) → EntryWord) (inputs : Fin w → Array RationalWord) :
    (localEvaluateBits template J w T inputs).words.size=J := by
  cases w <;> simp [localEvaluateBits]

/-- Physical fitting gives bounded buffers without assuming arithmetic correctness. -/
theorem localEvaluateBits_bounded (template : List Bool) (J w : ℕ)
    (T : (Fin w → Bool) → EntryWord) (inputs : Fin w → Array RationalWord) :
    Bounded (localEvaluateBits template J w T inputs).words template.length := by
  cases w with
  | zero => exact scaleBits_bounded _ _ _ _
  | succ w => exact addBits_bounded _ _ _ _

/-- Numeric cap derived from port denominators, coefficient bounds and branch arity. -/
def cap (J d B w : ℕ) : ℕ := (d+1)^w + (localBase J d B+1)^w + d+B+2

/-- Restricting a truth branch never increases the numeric cap. -/
theorem cap_mono (J d B : ℕ) {s w : ℕ} (h : s ≤ w) : cap J d B s≤cap J d B w := by
  unfold cap
  have h₁ := Nat.pow_le_pow_right (show 0<d+1 by omega) h
  have h₂ := Nat.pow_le_pow_right (show 0<localBase J d B+1 by omega) h
  omega

/-- Low-coefficient equality, used for intermediate primitive refinements. -/
def EqualBelow (J : ℕ) (a b : Array ℚ) : Prop := ∀ i<J, coefficient a i=coefficient b i

/-- A frozen addition depends only on its retained input coefficients. -/
theorem add_congr (J : ℕ) {a b c d : Array ℚ} (h₁ : EqualBelow J a b) (h₂ : EqualBelow J c d) :
    EqualBelow J (SemiprimeArrayOps.addJet a c J).coefficients (SemiprimeArrayOps.addJet b d J).coefficients := by
  intro i hi
  rw [SemiprimeArrayOps.addJet_coefficient _ _ J i hi,SemiprimeArrayOps.addJet_coefficient _ _ J i hi,h₁ i hi,h₂ i hi]

/-- A frozen convolution depends only on its retained input coefficients. -/
theorem multiply_congr (J : ℕ) {a b c d : Array ℚ} (h₁ : EqualBelow J a b) (h₂ : EqualBelow J c d) :
    EqualBelow J (multiply a c J).coefficients (multiply b d J).coefficients := by
  intro i hi
  rw [multiply_coefficient _ _ J i hi,multiply_coefficient _ _ J i hi]
  apply Finset.sum_congr rfl
  intro k hk
  have hki : k ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [h₁ k (by omega),h₂ (i-k) (by omega)]
end RiemannGaussian.SemiprimeLocalBits
