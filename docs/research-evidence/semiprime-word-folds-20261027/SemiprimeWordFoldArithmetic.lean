/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNativeGroupBitsBudget
import RiemannGaussian.SemiprimePacketArrayExecution

/-! # Report-preserving physical jet folds
Runtime arithmetic uses actual physical words only. Decoding and rational
representations occur in specifications. All input callback/test reports are
retained; initial word/table acquisition is separately supplied by the caller.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
namespace RiemannGaussian.SemiprimeWordFoldArithmetic
open scoped BigOperators
open SemiprimeRationalBits SemiprimeDotBits SemiprimeJetBits SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeArrayOps SemiprimeLocalExecutionHeight SemiprimeRepresentativeExecution
open SemiprimeHermiteArrayHeight SemiprimeLocalArrayFrontend
open SemiprimeCorrectedPortBits (array_eq_of_coeff)

/-- Actual allocated physical zero. -/
def zero (J : ℕ) : JetReport := SemiprimeCorrectedPortBits.zeroBits J
/-- Actual allocated physical one. -/
def one (J : ℕ) : JetReport := SemiprimeNativeGroupBits.oneBits J

/-- Both already acquired reports and every physical addition step survive. -/
def add (template : List Bool) (J : ℕ) (a b : JetReport) : JetReport :=
  let out := addBits template a.words b.words J
  ⟨out.words,a.clock+b.clock+out.clock+J+1⟩

/-- Both acquired reports and the actual convolution survive multiplication. -/
def mul (template : List Bool) (J : ℕ) (a b : JetReport) : JetReport :=
  let out := multiplyBits template a.words b.words J
  ⟨out.words,a.clock+b.clock+out.clock+J+1⟩

/-- Literal sign scaling needs no rational coefficient supplier. -/
def scale (template : List Bool) (J : ℕ) (a : JetReport) (negative : Bool) : JetReport :=
  let out := scaleBits template a.words (if negative then negOneWord else oneWord) J
  ⟨out.words,a.clock+out.clock+J+4⟩

/-- Executed negation through the same physical rational instructions. -/
def neg (template : List Bool) (J : ℕ) (a : JetReport) : JetReport := scale template J a true

/-- A rejected actual test skips the body and retains its complete test report. -/
def gate (J : ℕ) (test : TestReport) (body : Unit → JetReport) : JetReport :=
  if test.accepted then
    let out := body ()
    ⟨out.words,out.clock+test.work+1⟩
  else
    let out := zero J
    ⟨out.words,out.clock+test.work+1⟩

/-- Same chronological, tail-recursive finite-code fold as the scalar executor.
Every callback and the growing accumulator report is retained exactly once. -/
def sumFrom (template : List Bool) (J : ℕ) (f : ℕ → JetReport) : ℕ → ℕ → JetReport → JetReport
  | 0,_,acc => acc
  | fuel+1,start,acc =>
    let item := f start
    let next := add template J acc item
    sumFrom template J f fuel (start+1) next

/-- The physical same-order product is the already executed native-group fold. -/
def productList {A : Type} (template : List Bool) (J : ℕ) (xs : List A)
    (f : A → JetReport) : JetReport := SemiprimeNativeGroupBits.productList template J xs f

/-- Literal finite code range, with no list of attained summaries supplied. -/
def sumCodes (template : List Bool) (J N : ℕ) (f : Fin N → JetReport) : JetReport :=
  sumFrom template J (fun i => if hi : i< N then f ⟨i,hi⟩ else zero J) N 0 (zero J)

/-- Actual zero-array decoding. -/
theorem zero_decode (J : ℕ) : decode (zero J).words=(SemiprimeFibreArrayExecution.zeroRun J).jet.coefficients :=
  SemiprimeCorrectedPortBits.zeroBits_decode J
/-- Actual one-array decoding. -/
theorem one_decode (J : ℕ) : decode (one J).words=(SemiprimeFibreArrayExecution.oneRun J).jet.coefficients :=
  SemiprimeNativeGroupBits.oneBits_decode J

theorem zero_valid (J : ℕ) : Valid (zero J).words := SemiprimeCorrectedPortBits.zeroBits_valid J
theorem one_valid (J : ℕ) : Valid (one J).words := SemiprimeLocalBits.oneArray_valid J
@[simp] theorem zero_size (J : ℕ) : (zero J).words.size=J := by simp [zero]
@[simp] theorem one_size (J : ℕ) : (one J).words.size=J := by simp [one,SemiprimeNativeGroupBits.oneBits]
@[simp] theorem add_size (template : List Bool) (J : ℕ) (a b : JetReport) :
    (add template J a b).words.size=J := by simp [add]
@[simp] theorem mul_size (template : List Bool) (J : ℕ) (a b : JetReport) :
    (mul template J a b).words.size=J := by simp [mul]
@[simp] theorem scale_size (template : List Bool) (J : ℕ) (a : JetReport) (negative : Bool) :
    (scale template J a negative).words.size=J := by simp [scale]

/-- The actual add derives every fit and the new common numerator bound from
ORIGINAL input representations, rather than supplied intermediate Fits. -/
theorem add_correct (template : List Bool) (J d B C : ℕ) (a b : JetReport)
    (ha : Valid a.words) (hb : Valid b.words) (hd : 0< d)
    (hden : d<2^template.length) (hnum : B+C<2^template.length)
    (hra : ArrayBound (decode a.words) J d B) (hrb : ArrayBound (decode b.words) J d C) :
    decode (add template J a b).words=(addJet (decode a.words) (decode b.words) J).coefficients ∧
      Valid (add template J a b).words ∧ ArrayBound (decode (add template J a b).words) J d (B+C) := by
  have h := addBits_correct template a.words b.words J d B C ha hb hd hden hnum hra hrb
  have he : decode (add template J a b).words=(addJet (decode a.words) (decode b.words) J).coefficients := by
    apply array_eq_of_coeff J (by simp) (addJet_size _ _ _)
    exact h.1
  refine ⟨he,h.2,?_⟩
  rw [he]
  exact addJet_representation _ _ J d B C hra hrb

/-- Actual convolution derives every scalar product and partial-sum fit from
original input common representations. -/
theorem mul_correct (template : List Bool) (J d e B C : ℕ) (a b : JetReport)
    (ha : Valid a.words) (hb : Valid b.words) (hd : 0< d) (he : 0< e)
    (hden : d*e<2^template.length) (hnum : J*B*C<2^template.length)
    (hra : ArrayBound (decode a.words) J d B) (hrb : ArrayBound (decode b.words) J e C) :
    decode (mul template J a b).words=(multiply (decode a.words) (decode b.words) J).coefficients ∧
      Valid (mul template J a b).words ∧ ArrayBound (decode (mul template J a b).words) J (d*e) (J*B*C) := by
  have h := multiplyBits_correct template a.words b.words J d e B C ha hb hd he hden hnum hra hrb
  have heq : decode (mul template J a b).words=(multiply (decode a.words) (decode b.words) J).coefficients := by
    apply array_eq_of_coeff J (by simp) (multiply_size _ _ _)
    exact h.1
  refine ⟨heq,h.2,?_⟩
  rw [heq]
  exact multiply_representation _ _ d e B C J hra hrb

/-- Exact finite-code sum and output common representation; intermediate fits
are derived inductively from the ORIGINAL callback envelope Bacc+fuel*B. -/
theorem sumFrom_correct (template : List Bool) (J d B fuel start Bacc : ℕ)
    (f : ℕ → JetReport) (legacy : ℕ → SemiprimeFibreArrayExecution.Run)
    (acc : JetReport) (oldAcc : SemiprimeFibreArrayExecution.Run)
    (hd : 0< d) (hden : d<2^template.length) (hnum : Bacc+fuel*B<2^template.length)
    (ha : Valid acc.words) (hra : ArrayBound (decode acc.words) J d Bacc)
    (hea : decode acc.words=oldAcc.jet.coefficients)
    (hf : ∀ i,start≤ i → i< start+fuel →
      decode (f i).words=(legacy i).jet.coefficients ∧ Valid (f i).words ∧
        ArrayBound (decode (f i).words) J d B) :
    decode (sumFrom template J f fuel start acc).words=
      (SemiprimeFibreArrayExecution.sumFrom J legacy fuel start oldAcc).jet.coefficients ∧
      Valid (sumFrom template J f fuel start acc).words ∧
      ArrayBound (decode (sumFrom template J f fuel start acc).words) J d (Bacc+fuel*B) := by
  induction fuel generalizing start Bacc acc oldAcc with
  | zero => simpa only [sumFrom,SemiprimeFibreArrayExecution.sumFrom,Nat.zero_mul,Nat.add_zero] using
      (show decode acc.words=oldAcc.jet.coefficients ∧ Valid acc.words ∧ ArrayBound (decode acc.words) J d Bacc from ⟨hea,ha,hra⟩)
  | succ fuel ih =>
    have hi := hf start (by omega) (by omega)
    have hn : Bacc+B<2^template.length := by
      have hm : B≤(fuel+1)*B := by nlinarith
      omega
    have hh := add_correct template J d Bacc B acc (f start) ha hi.2.1 hd hden hn hra hi.2.2
    have heq : decode (add template J acc (f start)).words=
        (SemiprimeFibreArrayExecution.addRun J oldAcc (legacy start)).jet.coefficients := by
      rw [hh.1,hea,hi.1]
      rfl
    have ho := ih (start+1) (Bacc+B) (add template J acc (f start))
      (SemiprimeFibreArrayExecution.addRun J oldAcc (legacy start))
      (by nlinarith only [hnum]) hh.2.1 hh.2.2 heq
      (fun i h₁ h₂ => hf i (by omega) (by omega))
    simpa only [sumFrom,SemiprimeFibreArrayExecution.sumFrom,Nat.add_mul,Nat.one_mul,Nat.add_assoc,Nat.add_comm B] using ho

/-- Every prefix of a requested sum has the same original common denominator.
Only the number of callbacks already traversed enters its numerator bound. -/
theorem sumFrom_prefix (template : List Bool) (J d B fuel start Bacc p : ℕ)
    (f : ℕ → JetReport) (acc : JetReport) (hp : p≤ fuel)
    (hd : 0< d) (hden : d<2^template.length) (hnum : Bacc+fuel*B<2^template.length)
    (ha : Valid acc.words) (hra : ArrayBound (decode acc.words) J d Bacc)
    (hf : ∀ i,start≤ i → i< start+fuel → Valid (f i).words ∧ ArrayBound (decode (f i).words) J d B) :
    Valid (sumFrom template J f p start acc).words ∧
      ArrayBound (decode (sumFrom template J f p start acc).words) J d (Bacc+p*B) := by
  have h := sumFrom_correct template J d B p start Bacc f
    (fun i => ⟨⟨decode (f i).words,0,0⟩,0⟩) acc ⟨⟨decode acc.words,0,0⟩,0⟩
    hd hden (by exact (Nat.add_le_add_left (Nat.mul_le_mul_right B hp) Bacc).trans_lt hnum)
    ha hra rfl (by
      intro i h₁ h₂
      exact ⟨rfl,(hf i h₁ (by omega)).1,(hf i h₁ (by omega)).2⟩)
  exact h.2

/-- Literal sign multiplication preserves the original common denominator. -/
theorem scale_correct (template : List Bool) (J d B : ℕ) (a : JetReport) (negative : Bool)
    (ha : Valid a.words) (hd : 0< d) (hden : d<2^template.length) (hnum : B<2^template.length)
    (hra : ArrayBound (decode a.words) J d B) :
    decode (scale template J a negative).words=
      (scaleJet (decode a.words) (if negative then (-1:ℚ) else 1) J).coefficients ∧
      Valid (scale template J a negative).words ∧ ArrayBound (decode (scale template J a negative).words) J d B := by
  let c := if negative then negOneWord else oneWord
  have hc : c.Valid := by cases negative <;> exact (by change 0<1; decide)
  have hcv : c.value=(if negative then (-1:ℚ) else 1) := by
    cases negative <;> simp only [c,Bool.false_eq_true,ite_false,ite_true,oneWord_value,negOneWord_value]
  have hcr : Representation c.value 1 1 := by
    rw [hcv]
    cases negative
    · exact representation_one 1 (by decide)
    · exact representation_neg (representation_one 1 (by decide))
  have hs := scaleBits_correct template a.words c J d 1 B 1 ha hc hd (by decide)
    (by simpa only [Nat.one_mul] using hden) (by simpa only [Nat.one_mul] using hnum) hra hcr
  have he : decode (scale template J a negative).words=
      (scaleJet (decode a.words) (if negative then (-1:ℚ) else 1) J).coefficients := by
    apply array_eq_of_coeff J (by simp) (scaleJet_size _ _ _)
    intro i hi
    rw [← hcv]
    exact hs.1 i hi
  refine ⟨he,hs.2,?_⟩
  rw [he]
  intro i hi
  rw [scaleJet_coefficient _ _ J i hi]
  cases negative
  · simpa only [Bool.false_eq_true,ite_false,one_mul] using hra i hi
  · simpa only [ite_true,neg_one_mul] using representation_neg (hra i hi)

/-- Actual executed gate agrees with the original scalar branch and retains
common original callback representations on either branch. -/
theorem gate_correct (J d B : ℕ) (test : TestReport) (body : Unit → JetReport)
    (legacy : Unit → SemiprimeFibreArrayExecution.Run)
    (hb : decode (body ()).words=(legacy ()).jet.coefficients)
    (hv : Valid (body ()).words) (hr : ArrayBound (decode (body ()).words) J d B) :
    decode (gate J test body).words=(SemiprimeFibreArrayExecution.gateRun J test legacy).jet.coefficients ∧
      Valid (gate J test body).words ∧ ArrayBound (decode (gate J test body).words) J d B := by
  cases he : test.accepted
  · simpa only [gate,SemiprimeFibreArrayExecution.gateRun,he,Bool.false_eq_true,ite_false]
      using (show decode (zero J).words=(SemiprimeFibreArrayExecution.zeroRun J).jet.coefficients ∧
        Valid (zero J).words ∧ ArrayBound (decode (zero J).words) J d B from
          ⟨zero_decode J,zero_valid J,by rw [zero_decode]; exact zero_bound J d B⟩)
  · simpa only [gate,SemiprimeFibreArrayExecution.gateRun,he,ite_true] using
      (show decode (body ()).words=(legacy ()).jet.coefficients ∧ Valid (body ()).words ∧
        ArrayBound (decode (body ()).words) J d B from ⟨hb,hv,hr⟩)

/-- Complete finite-code sum, with all fits derived from the ORIGINAL common
callback envelope and the actual code count, not a generic 2^n traversal. -/
theorem sumCodes_correct (template : List Bool) (J N d B : ℕ)
    (f : Fin N → JetReport) (legacy : Fin N → SemiprimeFibreArrayExecution.Run)
    (hd : 0< d) (hden : d<2^template.length) (hnum : N*B<2^template.length)
    (hf : ∀ i,decode (f i).words=(legacy i).jet.coefficients ∧ Valid (f i).words ∧
      ArrayBound (decode (f i).words) J d B) :
    decode (sumCodes template J N f).words=(SemiprimePacketArrayExecution.sumCodes J N legacy).jet.coefficients ∧
      Valid (sumCodes template J N f).words ∧ ArrayBound (decode (sumCodes template J N f).words) J d (N*B) := by
  have hs := sumFrom_correct template J d B N 0 0
    (fun i => if hi : i< N then f ⟨i,hi⟩ else zero J)
    (fun i => if hi : i< N then legacy ⟨i,hi⟩ else SemiprimeFibreArrayExecution.zeroRun J)
    (zero J) (SemiprimeFibreArrayExecution.zeroRun J) hd hden (by simpa using hnum)
    (zero_valid J) (by rw [zero_decode]; exact zero_bound J d 0) (zero_decode J)
    (by
      intro i _ hi
      have hi' : i<N := by omega
      simpa only [dite_eq_left hi'] using hf ⟨i,hi'⟩)
  simpa only [sumCodes,SemiprimePacketArrayExecution.sumCodes,Nat.zero_add] using hs

/-- A deliberately generous polynomial width is allowed to depend on the
ACTUAL finite-code count. It never inserts a full global assignment count. -/
def sumWidth (b fuel : ℕ) : ℕ := 2*b+fuel+3

/-- Original dyadic coefficient bounds supply all sum-prefix fit inequalities. -/
theorem sum_numeric_bounds (b fuel d Bacc B : ℕ)
    (hd : d≤2^b) (ha : Bacc≤2^b) (hb : B≤2^b) :
    d<2^(sumWidth b fuel) ∧ Bacc+fuel*B<2^(sumWidth b fuel) := by
  have hf : fuel+1≤2^(fuel+1) := Nat.le_of_lt (show fuel+1<2^(fuel+1) from Nat.lt_two_pow_self)
  have hm : Bacc+fuel*B≤(fuel+1)*2^b := by nlinarith only [ha,hb]
  have hp := Nat.mul_le_mul_right (2^b) hf
  have he : 2^(fuel+1)*2^b=2^(b+fuel+1) := by rw [← pow_add]; congr 1; omega
  rw [he] at hp
  refine ⟨hd.trans_lt (Nat.pow_lt_pow_right (by decide) ?_),
    (hm.trans hp).trans_lt (Nat.pow_lt_pow_right (by decide) ?_)⟩ <;> unfold sumWidth <;> omega

/-- Same-order physical products and ALL suffix fits reuse the executed native
fold theorem; only ORIGINAL callback common representations are supplied. -/
theorem productList_correct {A : Type} (template : List Bool) (J D B N k : ℕ)
    (xs : List A) (f : A → JetReport) (legacy : A → SemiprimeFibreArrayExecution.Run)
    (hD : 0<D) (hDN : D≤N) (hBN : B≤N) (hJN : J≤N) (hNk : N≤2^k)
    (hwidth : k*(2*xs.length+2)<template.length)
    (hf : ∀ e∈xs,decode (f e).words=(legacy e).jet.coefficients ∧
      Valid (f e).words ∧ ArrayBound (decode (f e).words) J D B) :
    decode (productList template J xs f).words=
      (SemiprimeFibreArrayExecution.productList J xs legacy).jet.coefficients ∧
      Valid (productList template J xs f).words ∧
      ArrayBound (decode (productList template J xs f).words) J (D^xs.length) (N^(2*xs.length)) :=
  SemiprimeNativeGroupBits.productList_correct template J D B N k xs f legacy hD hDN hBN hJN hNk hwidth hf

end RiemannGaussian.SemiprimeWordFoldArithmetic
