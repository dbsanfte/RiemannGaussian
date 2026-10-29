/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeWordFoldArithmetic
import RiemannGaussian.SemiprimeHermiteArrayHeight

/-! # Physical Hermite scalar evaluation

The actual ascending evaluation caches its scalar and integer power. Affine
products retain one suffix result. Input acquisition is separate; every arithmetic
instruction here executes on Boolean rational words and retains its clock.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeHermiteEvaluationBits
open SemiprimeRationalBits SemiprimeJetBits SemiprimeDotBits
open SemiprimeJetArrayHeight SemiprimeHermiteArrayHeight

/-- Actual physical evaluation state. -/
structure EvalReport where
  /-- Cached accumulated value. -/
  word : RationalWord
  /-- Cached argument power. -/
  power : RationalWord
  /-- Retained arithmetic and finite-cell work. -/
  clock : ℕ

/-- Ascending-power evaluation, matching the scalar recurrence literally. -/
def evalPrefix (template : List Bool) (a : Array RationalWord) (x : RationalWord) : ℕ → EvalReport
  | 0 => ⟨zeroWord,oneWord,4⟩
  | len+1 =>
    let old := evalPrefix template a x len
    let term := executeOperation .mul (wordAt a len) old.power template
    let value := executeOperation .add old.word term.word template
    let power := executeOperation .mul old.power x template
    ⟨value.word,power.word,old.clock+term.clock+value.clock+power.clock+accessCost template a+8*template.length+12⟩

/-- The exact suffix product of the acquired affine factors. -/
def affineValue (template : List Bool) (x : RationalWord) : List RationalWord → RationalReport
  | [] => ⟨oneWord,4⟩
  | c::cs =>
    let old := affineValue template x cs
    let term := executeOperation .mul c x template
    let factor := executeOperation .add oneWord term.word template
    let out := executeOperation .mul old.word factor.word template
    ⟨out.word,old.clock+term.clock+factor.clock+out.clock+8*template.length+12⟩

/-- A common representation gives an instruction's reduced binary bounds. -/
theorem fits_of_representation {q : ℚ} {d B W : ℕ} (hd : 0<d)
    (hq : Representation q d B) (hden : d<2^W) (hnum : B<2^W) : Fits q W := by
  have h := representation_reduced_bound hd hq
  exact ⟨h.2.trans_lt hnum,h.1.trans_lt hden⟩

/-- Exact physical evaluation from original coefficient and integer-argument bounds.
The two numeric caps concern original input data, not intermediate advice. -/
theorem evalPrefix_correct (template : List Bool) (a : Array RationalWord)
    (xw : RationalWord) (x : ℤ) (d B T J len : ℕ)
    (hd : 0<d) (ha : Valid a) (hxw : xw.Valid) (hxval : xw.value=(x:ℚ))
    (hx : x.natAbs≤T) (hlen : len≤J)
    (hcoeff : ∀ i<J,Representation (SemiprimeJetArray.coefficient (decode a) i) d B)
    (hden : d<2^template.length)
    (hnum : (J+1)*(B+1)*(T+1)^(J+1)<2^template.length) :
    (evalPrefix template a xw len).word.value=
      (SemiprimeHermiteArrayHeight.evalPrefix (decode a) x len).value ∧
    (evalPrefix template a xw len).power.value=(x:ℚ)^len ∧
    (evalPrefix template a xw len).word.Valid ∧
    (evalPrefix template a xw len).power.Valid := by
  have hpow : ∀ k≤J+1,(x^k).natAbs≤(T+1)^(J+1) := by
    intro k hk
    rw [Int.natAbs_pow]
    exact (Nat.pow_le_pow_left (by omega : x.natAbs≤T+1) k).trans
      (Nat.pow_le_pow_right (by omega) hk)
  have hbase : 1≤(T+1)^(J+1) := Nat.one_le_pow _ _ (by omega)
  have hone : 1<2^template.length := by
    have hb : 1≤(J+1)*(B+1)*(T+1)^(J+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hpfit : ∀ k≤J+1,Fits ((x:ℚ)^k) template.length := by
    intro k hk
    have hr := representation_integer (x^k)
    have hn : (x^k).natAbs<2^template.length := by
      have he : (T+1)^(J+1)≤(J+1)*(B+1)*(T+1)^(J+1) := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right ((T+1)^(J+1))
          (Nat.one_le_iff_ne_zero.mpr (by positivity))
      exact (hpow k hk).trans_lt (he.trans_lt hnum)
    simpa only [Int.cast_pow] using fits_of_representation (by decide : 0<1) hr hone hn
  induction len with
  | zero => simp [evalPrefix,SemiprimeHermiteArrayHeight.evalPrefix,zeroWord_value,
      oneWord_valid,zeroWord_valid]
  | succ len ih =>
    have ho := ih (by omega)
    have hterm : Representation ((wordAt a len).value*(x:ℚ)^len) d
        (B*(T+1)^(J+1)) := by
      have hc := hcoeff len (by omega)
      rw [coefficient_decode] at hc
      simpa only [Int.cast_pow] using representation_integer_mul hc (x^len) (hpow len (by omega))
    have htfit := fits_of_representation hd hterm hden (by
      have he : B*(T+1)^(J+1)≤(J+1)*(B+1)*(T+1)^(J+1) := by
        exact Nat.mul_le_mul_right _ ((Nat.le_add_right B 1).trans
          (by simpa only [Nat.one_mul] using Nat.mul_le_mul_right (B+1) (show 1≤J+1 by omega)))
      exact he.trans_lt hnum)
    have ht := executeOperation_correct .mul (wordAt a len) (evalPrefix template a xw len).power
      template (wordAt_valid a ha len) ho.2.2.2 (by simpa only [Operation.value,ho.2.1] using htfit)
    have hvrep' := evalPrefix_representation (decode a) x d B T J (len+1) hx hlen hcoeff
    have hvnum : (len+1)*B*(T+1)^J<2^template.length := by
      have hp : (T+1)^J≤(T+1)^(J+1) := Nat.pow_le_pow_right (by omega) (by omega)
      have he : (len+1)*B*(T+1)^J≤(J+1)*(B+1)*(T+1)^(J+1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) hp
      exact he.trans_lt hnum
    have hvfit := fits_of_representation hd hvrep' hden hvnum
    have hv := executeOperation_correct .add (evalPrefix template a xw len).word
      (executeOperation .mul (wordAt a len) (evalPrefix template a xw len).power template).word
      template ho.2.2.1 ht.2.1 (by
        simpa only [Operation.value,ho.1,ht.1,Operation.value,ho.2.1,
          SemiprimeHermiteArrayHeight.evalPrefix,coefficient_decode,evalPrefix_power] using hvfit)
    have hp := executeOperation_correct .mul (evalPrefix template a xw len).power xw template
      ho.2.2.2 hxw (by simpa only [Operation.value,ho.2.1,hxval,pow_succ] using hpfit (len+1) (by omega))
    refine ⟨?_,?_,hv.2.1,hp.2.1⟩
    · simpa only [evalPrefix,Operation.value,ho.1,ht.1,ho.2.1,
        SemiprimeHermiteArrayHeight.evalPrefix,coefficient_decode,evalPrefix_power] using hv.1
    · simpa only [evalPrefix,Operation.value,ho.2.1,hxval,pow_succ] using hp.1

/-- Every affine suffix has a power of the ORIGINAL common denominator.
The scalar product uses no inverse and no intermediate height advice. -/
theorem affineValue_correct (template : List Bool) (xw : RationalWord) (x : ℤ)
    (cs : List RationalWord) (d B T J : ℕ) (hd : 0<d)
    (hxw : xw.Valid) (hxval : xw.value=(x:ℚ)) (hx : x.natAbs≤T)
    (hlen : cs.length≤J)
    (hc : ∀ c∈cs,c.Valid ∧ Representation c.value d B)
    (hden : d^J<2^template.length)
    (hnum : (d+B*T+1)^(J+1)<2^template.length) :
    (affineValue template xw cs).word.value=
      (SemiprimeHermiteArrayHeight.affineValue x (cs.map RationalWord.value)).value ∧
    (affineValue template xw cs).word.Valid ∧
    Representation (affineValue template xw cs).word.value
      (d^cs.length) ((d+B*T+1)^cs.length) := by
  have hone : 1<2^template.length :=
    (Nat.one_le_pow J d (by omega)).trans_lt hden
  have hdsmall : d<2^template.length := by
    have hp : d≤d+B*T+1 := by omega
    exact (hp.trans (Nat.le_self_pow (by omega : J+1≠0) (d+B*T+1))).trans_lt hnum
  induction cs with
  | nil =>
    simp only [affineValue,List.map_nil,SemiprimeHermiteArrayHeight.affineValue,
      oneWord_value,oneWord_valid,List.length_nil,pow_zero,true_and]
    exact representation_one 1 (by decide)
  | cons c cs ih =>
    have hi := ih (by simpa only [List.length_cons] using (show cs.length+1≤J from hlen) |> fun h => by omega)
      (fun z hz => hc z (List.mem_cons_of_mem c hz))
    have hc' := hc c List.mem_cons_self
    have hr := representation_integer_mul hc'.2 x hx
    have hnterm : B*T<2^template.length := by
      exact (show B*T≤d+B*T+1 by omega).trans_lt
        ((Nat.le_self_pow (by omega : J+1≠0) (d+B*T+1)).trans_lt hnum)
    have ht := executeOperation_correct .mul c xw template hc'.1 hxw
      (by simpa only [Operation.value,hxval] using fits_of_representation hd hr hdsmall hnterm)
    have hfRep := representation_add_one hr hd
    have hnf : d+B*T<2^template.length := by
      exact (Nat.le_succ _).trans_lt
        ((Nat.le_self_pow (by omega : J+1≠0) (d+B*T+1)).trans_lt hnum)
    have hf := executeOperation_correct .add oneWord
      (executeOperation .mul c xw template).word template oneWord_valid ht.2.1
      (by simpa only [Operation.value,oneWord_value,ht.1,hxval] using
        fits_of_representation hd hfRep hdsmall hnf)
    have hfrep : Representation
        (executeOperation .add oneWord (executeOperation .mul c xw template).word template).word.value
        d (d+B*T+1) := by
      rw [hf.1,Operation.value,oneWord_value,ht.1,Operation.value,hxval]
      exact representation_mono hfRep (by omega)
    have hmrep := representation_mul hi.2.2 hfrep
    have hmd : d^cs.length*d<2^template.length := by
      rw [← pow_succ]
      exact (Nat.pow_le_pow_right (by omega) (by simpa only [List.length_cons] using hlen)).trans_lt hden
    have hmn : (d+B*T+1)^cs.length*(d+B*T+1)<2^template.length := by
      rw [← pow_succ]
      exact (Nat.pow_le_pow_right (by omega) (by simp only [List.length_cons] at hlen; omega)).trans_lt hnum
    have hm := executeOperation_correct .mul (affineValue template xw cs).word
      (executeOperation .add oneWord (executeOperation .mul c xw template).word template).word
      template hi.2.1 hf.2.1 (fits_of_representation (Nat.mul_pos (Nat.pow_pos hd) hd) hmrep hmd hmn)
    refine ⟨?_,hm.2.1,?_⟩
    · simp only [affineValue,hm.1,Operation.value,hi.1,hf.1,oneWord_value,
        ht.1,hxval,List.map_cons,SemiprimeHermiteArrayHeight.affineValue]
    · change Representation (executeOperation .mul _ _ template).word.value _ _
      rw [hm.1]
      simpa only [List.length_cons,pow_succ,Operation.value] using hmrep

/-- The output representation follows from the ORIGINAL common coefficient bound. -/
theorem evalPrefix_representation (template : List Bool) (a : Array RationalWord)
    (xw : RationalWord) (x : ℤ) (d B T J len : ℕ)
    (hd : 0<d) (ha : Valid a) (hxw : xw.Valid) (hxval : xw.value=(x:ℚ))
    (hx : x.natAbs≤T) (hlen : len≤J)
    (hcoeff : ∀ i<J,Representation (SemiprimeJetArray.coefficient (decode a) i) d B)
    (hden : d<2^template.length)
    (hnum : (J+1)*(B+1)*(T+1)^(J+1)<2^template.length) :
    Representation (evalPrefix template a xw len).word.value d (len*B*(T+1)^J) := by
  rw [(evalPrefix_correct template a xw x d B T J len hd ha hxw hxval hx hlen hcoeff hden hnum).1]
  exact SemiprimeHermiteArrayHeight.evalPrefix_representation (decode a) x d B T J len hx hlen hcoeff

end RiemannGaussian.SemiprimeHermiteEvaluationBits
