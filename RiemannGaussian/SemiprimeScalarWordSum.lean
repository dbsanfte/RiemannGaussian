/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeHermiteEvaluationBitsBounds

/-! # Chronological physical scalar accumulation
Each callback is acquired once. Its word, its actual clock, physical addition,
and finite word-copy/control work are retained. One ORIGINAL common denominator
controls every accumulator; no intermediate Fits advice is accepted.
-/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace RiemannGaussian.SemiprimeScalarWordSum
open scoped BigOperators
open SemiprimeRationalBits SemiprimeJetArrayHeight SemiprimeHermiteEvaluationBitsBounds

/-- Literal chronological physical scalar sum with a cached callback per step. -/
def sumFrom (template : List Bool) (f : ℕ → RationalReport) :
    ℕ → ℕ → RationalReport → RationalReport
  | 0, _, acc => acc
  | fuel+1, start, acc =>
    let next := f start
    let out := executeOperation .add acc.word next.word template
    sumFrom template f fuel (start+1)
      ⟨out.word,acc.clock+next.clock+out.clock+8*template.length+8⟩

/-- One original denominator and the total numerator bound suffice at every step. -/
theorem sumFrom_correct (template : List Bool) (f : ℕ → RationalReport)
    (fuel start : ℕ) (acc : RationalReport) (d Bacc B : ℕ)
    (hd : 0<d) (hden : d<2^template.length)
    (hnum : Bacc+fuel*B<2^template.length)
    (hacc : acc.word.Valid ∧ Representation acc.word.value d Bacc)
    (hf : ∀ i<fuel,(f (start+i)).word.Valid ∧ Representation (f (start+i)).word.value d B) :
    (sumFrom template f fuel start acc).word.value=
      acc.word.value+∑ i∈Finset.range fuel,(f (start+i)).word.value ∧
    (sumFrom template f fuel start acc).word.Valid ∧
    Representation (sumFrom template f fuel start acc).word.value d (Bacc+fuel*B) := by
  induction fuel generalizing start acc Bacc with
  | zero => simpa only [sumFrom,Finset.range_zero,Finset.sum_empty,add_zero,Nat.zero_mul] using
      (show acc.word.value=acc.word.value ∧ acc.word.Valid ∧ Representation acc.word.value d Bacc from
        ⟨rfl,hacc.1,hacc.2⟩)
  | succ fuel ih =>
    have hn := hf 0 (by omega)
    simp only [Nat.add_zero] at hn
    have hr := representation_add hacc.2 hn.2
    have hc := executeOperation_correct .add acc.word (f start).word template hacc.1 hn.1
      (SemiprimeHermiteEvaluationBits.fits_of_representation hd hr hden (by
        have he : Bacc+B≤Bacc+(fuel+1)*B := by nlinarith
        exact he.trans_lt hnum))
    have hh := ih (start+1)
      ⟨(executeOperation .add acc.word (f start).word template).word,
        acc.clock+(f start).clock+(executeOperation .add acc.word (f start).word template).clock+
          8*template.length+8⟩
      (Bacc+B) (by nlinarith) ⟨hc.2.1,by rw [hc.1];exact hr⟩ (by
        intro i hi
        have he : start+1+i=start+(i+1) := by omega
        rw [he]
        exact hf (i+1) (by omega))
    refine ⟨?_,hh.2.1,?_⟩
    · change (sumFrom template f fuel (start+1) _).word.value=_
      rw [hh.1,hc.1,Operation.value,Finset.sum_range_succ']
      simp only [Nat.add_zero]
      have he : (∑ i∈Finset.range fuel,(f (start+1+i)).word.value)=
          ∑ i∈Finset.range fuel,(f (start+(i+1))).word.value := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun k => (f k).word.value) (by omega)
      rw [he]
      ring
    · change Representation (sumFrom template f fuel (start+1) _).word.value d _
      have he : Bacc+B+fuel*B=Bacc+(fuel+1)*B := by ring
      simpa only [he] using hh.2.2

/-- Every chronological prefix has a derived valid word and the SAME denominator. -/
theorem sumFrom_prefix (template : List Bool) (f : ℕ → RationalReport)
    (fuel start p : ℕ) (acc : RationalReport) (d Bacc B : ℕ)
    (hd : 0<d) (hden : d<2^template.length)
    (hnum : Bacc+fuel*B<2^template.length) (hp : p≤fuel)
    (hacc : acc.word.Valid ∧ Representation acc.word.value d Bacc)
    (hf : ∀ i<fuel,(f (start+i)).word.Valid ∧ Representation (f (start+i)).word.value d B) :
    (sumFrom template f p start acc).word.Valid ∧
    Representation (sumFrom template f p start acc).word.value d (Bacc+p*B) := by
  have hn : Bacc+p*B<2^template.length :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right B hp) Bacc).trans_lt hnum
  exact (sumFrom_correct template f p start acc d Bacc B hd hden hn hacc
    (fun i hi => hf i (hi.trans_le hp))).2

/-- Physical scalar storage is bounded without assuming output fits. -/
theorem sumFrom_width (template : List Bool) (f : ℕ → RationalReport)
    (fuel start : ℕ) (acc : RationalReport) (hacc : Width acc.word template.length) :
    Width (sumFrom template f fuel start acc).word template.length := by
  induction fuel generalizing start acc with
  | zero => exact hacc
  | succ fuel ih => exact ih (start+1) _ (operation_width _ _ _ _)

/-- Retained actual callback clocks plus the executed Boolean-add/copy cost. -/
theorem sumFrom_clock (template : List Bool) (f : ℕ → RationalReport)
    (fuel start : ℕ) (acc : RationalReport)
    (hacc : Width acc.word template.length)
    (hf : ∀ i<fuel,Width (f (start+i)).word template.length) :
    (sumFrom template f fuel start acc).clock≤acc.clock+
      ∑ i∈Finset.range fuel,(f (start+i)).clock+
      fuel*(20000*(template.length+1)^3+8*template.length+8) := by
  induction fuel generalizing start acc with
  | zero => simp [sumFrom]
  | succ fuel ih =>
    have hn := hf 0 (by omega)
    simp only [Nat.add_zero] at hn
    have hc := executeOperation_cost .add acc.word (f start).word template hacc hn (le_refl _)
    have hh := ih (start+1)
      ⟨(executeOperation .add acc.word (f start).word template).word,
        acc.clock+(f start).clock+(executeOperation .add acc.word (f start).word template).clock+
          8*template.length+8⟩ (operation_width _ _ _ _) (by
        intro i hi
        have he : start+1+i=start+(i+1) := by omega
        rw [he]
        exact hf (i+1) (by omega))
    change (sumFrom template f fuel (start+1) _).clock≤_
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero]
    have he : (∑ i∈Finset.range fuel,(f (start+1+i)).clock)=
        ∑ i∈Finset.range fuel,(f (start+(i+1))).clock := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun k => (f k).clock) (by omega)
    rw [he] at hh
    dsimp only at hh
    nlinarith

end RiemannGaussian.SemiprimeScalarWordSum
