/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeWordFoldArithmetic

/-! # Physical finite-word fold clocks and buffer widths
Each bound concerns the actual report-preserving program. Source/table/test
acquisition is included through its input reports, not a free value oracle.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeWordFoldBounds
open SemiprimeWordFoldArithmetic SemiprimeRationalBits SemiprimeJetBits
open SemiprimeRepresentativeExecution

/-- Literal allocated zero buffers fit the actual template. -/
theorem zero_bounded (J W : ℕ) (hW : 0< W) : Bounded (zero J).words W :=
  SemiprimeCorrectedPortBitsBounds.zeroBits_bounded J W hW
/-- Literal allocated one buffers fit the actual template. -/
theorem one_bounded (J W : ℕ) (hW : 0< W) : Bounded (one J).words W :=
  SemiprimeLocalBits.oneArray_bounded J W hW

/-- Actual fitting makes every physical addition buffer occupy the template. -/
theorem add_bounded (template : List Bool) (J : ℕ) (a b : JetReport) :
    Bounded (add template J a b).words template.length := addBits_bounded template _ _ J
/-- Actual fitting makes every physical multiplication buffer occupy the template. -/
theorem mul_bounded (template : List Bool) (J : ℕ) (a b : JetReport) (ht : 0< template.length) :
    Bounded (mul template J a b).words template.length := multiplyBits_bounded template ht _ _ J
/-- Sign scaling uses the same physically bounded output buffers. -/
theorem scale_bounded (template : List Bool) (J : ℕ) (a : JetReport) (negative : Bool) :
    Bounded (scale template J a negative).words template.length := scaleBits_bounded template _ _ J

/-- A gate copies its acquired body or allocates physical zero. -/
theorem gate_bounded (J : ℕ) (test : TestReport) (body : Unit → JetReport) (W : ℕ)
    (hW : 0< W) (hb : Bounded (body ()).words W) : Bounded (gate J test body).words W := by
  cases he : test.accepted
  · simpa only [gate,he,Bool.false_eq_true,ite_false] using zero_bounded J W hW
  · simpa only [gate,he,ite_true] using hb

/-- The finite sum retains bounded physical accumulator buffers at every step. -/
theorem sumFrom_bounded (template : List Bool) (J : ℕ) (f : ℕ → JetReport)
    (fuel start : ℕ) (acc : JetReport) (ha : Bounded acc.words template.length) :
    Bounded (sumFrom template J f fuel start acc).words template.length := by
  induction fuel generalizing start acc with
  | zero => exact ha
  | succ fuel ih => exact ih (start+1) _ (add_bounded template J acc (f start))

/-- A finite sum preserves exact precision after every accumulator update. -/
theorem sumFrom_size (template : List Bool) (J : ℕ) (f : ℕ → JetReport)
    (fuel start : ℕ) (acc : JetReport) (ha : acc.words.size=J) :
    (sumFrom template J f fuel start acc).words.size=J := by
  induction fuel generalizing start acc with
  | zero => exact ha
  | succ fuel ih => exact ih (start+1) _ (add_size template J acc (f start))

@[simp] theorem sumCodes_size (template : List Bool) (J N : ℕ) (f : Fin N → JetReport) :
    (sumCodes template J N f).words.size=J := sumFrom_size template J _ N 0 _ (zero_size J)

theorem sumCodes_bounded (template : List Bool) (J N : ℕ) (f : Fin N → JetReport)
    (ht : 0< template.length) : Bounded (sumCodes template J N f).words template.length :=
  sumFrom_bounded template J _ N 0 _ (zero_bounded J _ ht)

/-- Physical add instructions, actual coefficient addressing and fold control. -/
def addBudget (W J : ℕ) : ℕ :=
  SemiprimeCorrectedPortBitsBounds.addBudget W J+J+1
/-- Physical multiplication instructions and fold control. -/
def mulBudget (W J : ℕ) : ℕ := SemiprimeNativeGroupBitsBudget.multiplyBudget W J+J+1
/-- Literal sign scaling includes its actual physical source access and control. -/
def scaleBudget (W J : ℕ) : ℕ :=
  J*(20000*(W+1)^3+(J+1)*(2*W+3)+(2*W+3))+(2*J+1)+J+4

/-- Actual addition retains both acquired reports and all new bit work. -/
theorem add_clock (template : List Bool) (J : ℕ) (a b : JetReport)
    (ht : 0< template.length) (ha : Bounded a.words template.length) (hb : Bounded b.words template.length)
    (hsa : a.words.size≤ J) (hsb : b.words.size≤ J) :
    (add template J a b).clock≤ a.clock+b.clock+addBudget template.length J := by
  have hp := addBits_cost template ht a.words b.words J ha hb
  have h : (addBits template a.words b.words J).clock≤ SemiprimeCorrectedPortBitsBounds.addBudget template.length J := by
    apply hp.trans
    unfold SemiprimeCorrectedPortBitsBounds.addBudget accessCost
    gcongr
  unfold add addBudget
  dsimp only
  omega

/-- Actual convolution retains both acquired reports and all new bit work. -/
theorem mul_clock (template : List Bool) (J : ℕ) (a b : JetReport)
    (ht : 0< template.length) (ha : Bounded a.words template.length) (hb : Bounded b.words template.length)
    (hsa : a.words.size≤ J) (hsb : b.words.size≤ J) :
    (mul template J a b).clock≤ a.clock+b.clock+mulBudget template.length J := by
  have hp := multiplyBits_cost template ht a.words b.words J ha hb
  have h : (multiplyBits template a.words b.words J).clock≤ SemiprimeNativeGroupBitsBudget.multiplyBudget template.length J := by
    apply hp.trans
    unfold SemiprimeNativeGroupBitsBudget.multiplyBudget accessCost
    gcongr
  unfold mul mulBudget
  dsimp only
  omega

/-- Literal sign multiplication is physically acquired with constant-sized words, not advice. -/
theorem scale_clock (template : List Bool) (J : ℕ) (a : JetReport) (negative : Bool)
    (ht : 0< template.length) (ha : Bounded a.words template.length) (hsa : a.words.size≤ J) :
    (scale template J a negative).clock≤ a.clock+scaleBudget template.length J := by
  have hc : Width (if negative then negOneWord else oneWord) template.length := by
    cases negative
    · exact oneWord_width ht
    · exact negOneWord_width ht
  have hp := scaleBits_cost template ht a.words (if negative then negOneWord else oneWord) J ha hc
  have h : (scaleBits template a.words (if negative then negOneWord else oneWord) J).clock≤
      J*(20000*(template.length+1)^3+(J+1)*(2*template.length+3)+(2*template.length+3))+(2*J+1) := by
    apply hp.trans
    unfold accessCost
    gcongr
  unfold scale scaleBudget
  dsimp only
  omega

/-- A rejected test pays its actual report and zero allocation, skipping body. -/
theorem gate_clock (J B : ℕ) (test : TestReport) (body : Unit → JetReport)
    (hb : (body ()).clock≤ B) : (gate J test body).clock≤ test.work+B+3*J+2 := by
  cases he : test.accepted <;> simp only [gate,he,Bool.false_eq_true,ite_false,ite_true]
  · simp only [zero,SemiprimeCorrectedPortBits.zeroBits]
    omega
  · omega

/-- Complete sum clock: original accumulator, EVERY callback and EVERY physical
addition are retained, without regenerating old callbacks inside a closure. -/
theorem sumFrom_clock (template : List Bool) (J fuel start B : ℕ) (f : ℕ → JetReport)
    (acc : JetReport) (ht : 0< template.length) (ha : Bounded acc.words template.length)
    (hsize : acc.words.size≤ J)
    (hf : ∀ i,start≤ i → i< start+fuel → (f i).clock≤ B ∧ Bounded (f i).words template.length ∧ (f i).words.size≤ J) :
    (sumFrom template J f fuel start acc).clock≤ acc.clock+fuel*(B+addBudget template.length J) := by
  induction fuel generalizing start acc with
  | zero => simp [sumFrom]
  | succ fuel ih =>
    have hi := hf start (by omega) (by omega)
    have hh := add_clock template J acc (f start) ht ha hi.2.1 hsize hi.2.2
    have ho := ih (start+1) (add template J acc (f start)) (add_bounded template J acc (f start))
      (by simp) (fun i h₁ h₂ => hf i (by omega) (by omega))
    change (sumFrom template J f fuel (start+1) (add template J acc (f start))).clock≤_
    nlinarith only [hi.1,hh,ho]

/-- Literal finite code acquisition has the same linear-in-code count clock. -/
theorem sumCodes_clock (template : List Bool) (J N B : ℕ) (f : Fin N → JetReport)
    (ht : 0< template.length)
    (hf : ∀ i,(f i).clock≤ B ∧ Bounded (f i).words template.length ∧ (f i).words.size≤ J) :
    (sumCodes template J N f).clock≤3*J+1+N*(B+addBudget template.length J) := by
  have h := sumFrom_clock template J N 0 B
    (fun i => if hi : i<N then f ⟨i,hi⟩ else zero J) (zero J) ht (zero_bounded J _ ht) (by simp) (by
    intro i _ hi
    have hi' : i< N := by omega
    simpa only [dite_eq_left hi'] using hf ⟨i,hi'⟩)
  simpa only [sumCodes,zero,SemiprimeCorrectedPortBits.zeroBits] using h

/-- Product suffix clocks reuse the actual native physical multiplication fold. -/
theorem productList_clock {A : Type} (template : List Bool) (J B : ℕ) (xs : List A)
    (f : A → JetReport) (ht : 0< template.length)
    (hf : ∀ e∈xs,(f e).clock≤ B) (hw : ∀ e∈xs,Bounded (f e).words template.length)
    (hs : ∀ e∈xs,(f e).words.size≤ J) :
    (productList template J xs f).clock≤
      xs.length*(B+SemiprimeNativeGroupBitsBudget.multiplyBudget template.length J+J+3)+(3*J+1) :=
  SemiprimeNativeGroupBitsBudget.productList_clock template J B xs f ht hf hw hs

end RiemannGaussian.SemiprimeWordFoldBounds
