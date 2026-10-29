/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeJetBits
import RiemannGaussian.SemiprimeLocalExecutionBitBounds

/-! # Executed physical corrected-port acquisition
The runtime consumes physical source/node words and performs word arithmetic.
Rational decoding appears only in specifications and proofs. Initial source
word acquisition and natural clock bookkeeping remain separate refinements.
-/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000
namespace RiemannGaussian.SemiprimeCorrectedPortBits
open scoped BigOperators
open SemiprimeDotBits SemiprimeRationalBits SemiprimeJetBits SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeArrayOps SemiprimeLocalExecutionHeight SemiprimeLocalArrayFrontend

/-- Actual zero-word array, including finite allocation/control work. -/
def zeroBits (J : ℕ) : JetReport := ⟨Array.replicate J zeroWord,3*J+1⟩

/-- Copy the original coefficient into the constant slot; no rational multiply
by one is needed on this value-equivalent physical path. -/
def constantBits (template : List Bool) (a : Array RationalWord) (start J : ℕ) : JetReport :=
  ⟨Array.ofFn (fun i : Fin J => if i.val=0 then wordAt a start else zeroWord),
    J*(2*template.length+4)+accessCost template a+3⟩

/-- Physical Horner shift. Each recursive buffer, convolution and addition is
cached once before collecting its output and ALL lower clocks. -/
def shiftFrom (template : List Bool) (a : Array RationalWord) (t : RationalWord)
    (J : ℕ) : ℕ → ℕ → JetReport
  | _,0 => zeroBits J
  | start,len+1 =>
    let old := shiftFrom template a t J (start+1) len
    let product := multiplyBits template old.words #[t,oneWord] J
    let constant := constantBits template a start J
    let out := addBits template constant.words product.words J
    ⟨out.words,old.clock+product.clock+constant.clock+out.clock+7⟩

/-- The physical row shift uses the complete supplied original coefficient span. -/
def shiftRow (template : List Bool) (a : Array RationalWord) (t : RationalWord) (R J : ℕ) : JetReport :=
  shiftFrom template a t J 0 (R+1)

/-- Literal independent base/correction mask on actual words. -/
def maskShift (template : List Bool) (a : Array RationalWord)
    (base correction : Bool) (J : ℕ) : JetReport :=
  ⟨Array.ofFn (fun i : Fin J => if i.val=0 then
      if base then wordAt a 0 else zeroWord else if correction then wordAt a i.val else zeroWord),
    J*(accessCost template a+2*template.length+6)+3⟩

/-- Every original row is actually shifted and masked, then added to the cached
prefix. No shifted coefficient or corrected-port answer is supplied. -/
def acquireCorrected (template : List Bool) (source : ℕ → Array RationalWord)
    (t : RationalWord) (R J : ℕ) (base correction : ℕ → Bool) : ℕ → JetReport
  | 0 => zeroBits J
  | n+1 =>
    let old := acquireCorrected template source t R J base correction n
    let row := shiftRow template (source n) t R J
    let masked := maskShift template row.words (base n) (correction n) J
    let out := addBits template old.words masked.words J
    ⟨out.words,old.clock+row.clock+masked.clock+out.clock+8⟩

/-- Finite indexed wrapper has no polynomial-valued runtime index. -/
def acquireCorrectedFin {n : ℕ} (template : List Bool) (source : Fin n → Array RationalWord)
    (t : RationalWord) (R J : ℕ) (base correction : Fin n → Bool) : JetReport :=
  acquireCorrected template (fun v => if h : v< n then source ⟨v,h⟩ else #[])
    t R J (fun v => if h : v< n then base ⟨v,h⟩ else false)
    (fun v => if h : v< n then correction ⟨v,h⟩ else false) n

/-- Low coefficients and equal finite sizes identify actual retained arrays. -/
theorem array_eq_of_coeff {a b : Array ℚ} (J : ℕ) (ha : a.size=J) (hb : b.size=J)
    (h : ∀ i< J,coefficient a i=coefficient b i) : a=b := by
  apply Array.ext (ha.trans hb.symm)
  intro i hi hj
  simpa only [coefficient,Array.getElem?_eq_getElem hi,Array.getElem?_eq_getElem hj,
    Option.getD_some] using h i (by omega)

@[simp] theorem zeroBits_size (J : ℕ) : (zeroBits J).words.size=J := by simp [zeroBits]
@[simp] theorem constantBits_size (template : List Bool) (a : Array RationalWord) (start J : ℕ) :
    (constantBits template a start J).words.size=J := by simp [constantBits]
@[simp] theorem maskShift_size (template : List Bool) (a : Array RationalWord) (base correction : Bool) (J : ℕ) :
    (maskShift template a base correction J).words.size=J := by simp [maskShift]
@[simp] theorem shiftFrom_size (template : List Bool) (a : Array RationalWord) (t : RationalWord)
    (J start len : ℕ) : (shiftFrom template a t J start len).words.size=J := by
  cases len <;> simp [shiftFrom]
@[simp] theorem acquireCorrected_size (template : List Bool) (source : ℕ → Array RationalWord)
    (t : RationalWord) (R J : ℕ) (base correction : ℕ → Bool) (n : ℕ) :
    (acquireCorrected template source t R J base correction n).words.size=J := by
  cases n <;> simp [acquireCorrected]

/-- Literal zero words decode to the frozen zero array. -/
theorem zeroBits_decode (J : ℕ) : decode (zeroBits J).words=(zeroJet J).coefficients := by
  simp [zeroBits,decode,zeroJet,zeroWord_value]

/-- Literal constant copy decodes to the frozen scale-one result. -/
theorem constantBits_decode (template : List Bool) (a : Array RationalWord) (start J : ℕ) :
    decode (constantBits template a start J).words=
      (scaleJet (oneJet J).coefficients (coefficient (decode a) start) J).coefficients := by
  apply array_eq_of_coeff J (by simp) (by simp [scaleJet_size])
  intro i hi
  rw [scaleJet_coefficient _ _ J i hi,oneJet_coefficient J i hi,coefficient_decode]
  simp only [constantBits,wordAt,Array.getElem?_ofFn,dite_eq_left hi,Option.getD_some]
  by_cases hz : i=0 <;> simp [hz,zeroWord_value,wordAt]

/-- Physical masks preserve the exact independent constant/positive-degree convention. -/
theorem maskShift_decode (template : List Bool) (a : Array RationalWord) (base correction : Bool) (J : ℕ) :
    decode (maskShift template a base correction J).words=
      (SemiprimeLocalArrayFrontend.maskShift (decode a) base correction J).coefficients := by
  apply array_eq_of_coeff J (by simp) (by simp [SemiprimeLocalArrayFrontend.maskShift])
  intro i hi
  simp only [coefficient_decode,maskShift,wordAt,Array.getElem?_ofFn,dite_eq_left hi,Option.getD_some,
    SemiprimeLocalArrayFrontend.maskShift_coefficient _ _ _ J i hi]
  split_ifs <;> simp [zeroWord_value]

/-- Physical zero/constant/mask buffers have legal denominators. -/
theorem zeroBits_valid (J : ℕ) : Valid (zeroBits J).words := by
  intro i hi
  simpa [zeroBits] using zeroWord_valid

theorem constantBits_valid (template : List Bool) (a : Array RationalWord) (start J : ℕ)
    (ha : Valid a) : Valid (constantBits template a start J).words := by
  intro i hi
  simp only [constantBits,Array.getElem_ofFn]
  split_ifs
  · exact wordAt_valid a ha _
  · exact zeroWord_valid

theorem maskShift_valid (template : List Bool) (a : Array RationalWord) (base correction : Bool) (J : ℕ)
    (ha : Valid a) : Valid (maskShift template a base correction J).words := by
  intro i hi
  simp only [maskShift,Array.getElem_ofFn]
  split_ifs <;> first | exact wordAt_valid a ha _ | exact zeroWord_valid

/-- The common Horner envelope covers the multiply-add at its next level. -/
theorem horner_step (J B T len : ℕ) :
    B+J*hornerBound J B T len*(T+1)≤ hornerBound J B T (len+1) := by
  have hp : 1≤(1+J*(T+1))^len := Nat.one_le_pow _ _ (by omega)
  unfold hornerBound
  rw [pow_succ]
  nlinarith

/-- Every earlier suffix fits the completed source-length envelope. -/
theorem horner_mono (J B T : ℕ) : Monotone (hornerBound J B T) := by
  intro a b hab
  exact Nat.mul_le_mul_left B (Nat.pow_le_pow_right (by omega) hab)

/-- Word-backed Horner refinement, deriving ALL arithmetic fits from the ORIGINAL
common source representation and the single numeric source-length envelope. -/
theorem shiftFrom_correct (template : List Bool) (a : Array RationalWord) (tw : RationalWord)
    (t : ℤ) (J d B T start len : ℕ) (ha : Valid a) (htw : tw.Valid)
    (htval : tw.value=(t:ℚ)) (hd : 0< d) (ht : t.natAbs≤ T)
    (hden : d<2^template.length) (hnum : hornerBound J B T len<2^template.length)
    (hsource : ∀ i,start≤ i → i< start+len → Representation (coefficient (decode a) i) d B) :
    decode (shiftFrom template a tw J start len).words=
      (SemiprimeLocalArrayFrontend.shiftFrom (decode a) (t:ℚ) J start len).coefficients ∧
      Valid (shiftFrom template a tw J start len).words := by
  induction len generalizing start with
  | zero => exact ⟨zeroBits_decode J,zeroBits_valid J⟩
  | succ len ih =>
    have hn := (horner_mono J B T (show len≤ len+1 by omega)).trans_lt hnum
    have hold := ih (start+1) hn (fun i h₁ h₂ => hsource i (by omega) (by omega))
    let old := shiftFrom template a tw J (start+1) len
    have hlinear : decode #[tw,oneWord]=#[(t:ℚ),1] := by simp [decode,htval]
    have hlvalid : Valid #[tw,oneWord] := by
      intro i hi
      have hi' : i<2 := by simpa using hi
      interval_cases i <;> simp_all [Valid,oneWord_valid]
    have hp := multiplyBits_correct template old.words #[tw,oneWord] J d 1
      (hornerBound J B T len) (T+1) hold.2 hlvalid hd (by decide)
      (by simpa using hden)
      ((Nat.le_add_left _ _).trans_lt ((horner_step J B T len).trans_lt hnum))
      (by
        rw [hold.1]
        exact shiftFrom_bound (decode a) t J d B T (start+1) len ht
          (fun i h₁ h₂ => hsource i (by omega) (by omega)))
      (by rw [hlinear]; exact shift_linear_bound t J T ht)
    have hpeq : decode (multiplyBits template old.words #[tw,oneWord] J).words=
        (multiply (SemiprimeLocalArrayFrontend.shiftFrom (decode a) (t:ℚ) J (start+1) len).coefficients
          #[(t:ℚ),1] J).coefficients := by
      apply array_eq_of_coeff J (by simp) (by simp [multiply_size])
      intro i hi
      rw [hp.1 i hi,hold.1,hlinear]
    have hc := constantBits_decode template a start J
    have hadd := addBits_correct template (constantBits template a start J).words
      (multiplyBits template old.words #[tw,oneWord] J).words J d B
      (J*hornerBound J B T len*(T+1)) (constantBits_valid template a start J ha) hp.2 hd hden
      ((horner_step J B T len).trans_lt hnum)
      (by rw [hc]; exact horner_constant_bound (decode a) start J d B (hsource start (by omega) (by omega)))
      (by
        rw [hpeq]
        exact shiftFrom_product_bound (decode a) t J d B T (start+1) len ht
          (fun i h₁ h₂ => hsource i (by omega) (by omega)))
    refine ⟨?_,hadd.2⟩
    change decode (addBits template _ _ J).words=_
    apply array_eq_of_coeff J (by simp) (by simp [SemiprimeLocalArrayFrontend.shiftFrom,addJet_size])
    intro i hi
    rw [hadd.1 i hi,hc,hpeq]
    rfl

/-- Full physical row shift refines the literal frozen Horner supplier. -/
theorem shiftRow_correct (template : List Bool) (a : Array RationalWord) (tw : RationalWord)
    (t : ℤ) (R J d B T : ℕ) (ha : Valid a) (htw : tw.Valid)
    (htval : tw.value=(t:ℚ)) (hd : 0< d) (ht : t.natAbs≤ T)
    (hden : d<2^template.length) (hnum : hornerBound J B T (R+1)<2^template.length)
    (hsource : ∀ i≤ R,Representation (coefficient (decode a) i) d B) :
    decode (shiftRow template a tw R J).words=
      (SemiprimeLocalArrayFrontend.shiftRow (decode a) (t:ℚ) R J).coefficients ∧
      Valid (shiftRow template a tw R J).words :=
  shiftFrom_correct template a tw t J d B T 0 (R+1) ha htw htval hd ht hden hnum
    (fun i _ hi => hsource i (by omega))

/-- Actual corrected-port addition prefixes refine the frozen interpreter;
all add/convolution fits come from the ORIGINAL source common denominator. -/
theorem acquireCorrected_correct (template : List Bool) (source : ℕ → Array RationalWord)
    (tw : RationalWord) (t : ℤ) (R J d B T n : ℕ) (base correction : ℕ → Bool)
    (hvalid : ∀ v< n,Valid (source v)) (htw : tw.Valid) (htval : tw.value=(t:ℚ))
    (hd : 0< d) (ht : t.natAbs≤ T) (hden : d<2^template.length)
    (hrow : hornerBound J B T (R+1)<2^template.length)
    (hnum : n*hornerBound J B T (R+1)<2^template.length)
    (hsource : ∀ v< n,∀ i≤ R,Representation (coefficient (decode (source v)) i) d B) :
    decode (acquireCorrected template source tw R J base correction n).words=
      (SemiprimeLocalArrayFrontend.acquireCorrected (fun v => decode (source v)) (t:ℚ)
        R J base correction n).coefficients ∧
      Valid (acquireCorrected template source tw R J base correction n).words := by
  induction n with
  | zero => exact ⟨zeroBits_decode J,zeroBits_valid J⟩
  | succ n ih =>
    have hp : n*hornerBound J B T (R+1)<2^template.length :=
      (Nat.mul_le_mul_right _ (by omega : n≤ n+1)).trans_lt hnum
    have hold := ih (fun v hv => hvalid v (by omega)) hp
      (fun v hv => hsource v (by omega))
    have hshift := shiftRow_correct template (source n) tw t R J d B T (hvalid n (by omega))
      htw htval hd ht hden hrow (hsource n (by omega))
    have hmask := maskShift_decode template (shiftRow template (source n) tw R J).words
      (base n) (correction n) J
    have hmaskEq : decode (maskShift template (shiftRow template (source n) tw R J).words
        (base n) (correction n) J).words=
        (SemiprimeLocalArrayFrontend.maskShift
          (SemiprimeLocalArrayFrontend.shiftRow (decode (source n)) (t:ℚ) R J).coefficients
            (base n) (correction n) J).coefficients := by rw [hmask,hshift.1]
    have hadd := addBits_correct template
      (acquireCorrected template source tw R J base correction n).words
      (maskShift template (shiftRow template (source n) tw R J).words (base n) (correction n) J).words
      J d (n*hornerBound J B T (R+1)) (hornerBound J B T (R+1)) hold.2
      (maskShift_valid template _ _ _ J hshift.2) hd hden
      (by simpa only [Nat.add_mul,Nat.one_mul] using hnum)
      (by
        rw [hold.1]
        exact acquireCorrected_bound (fun v => decode (source v)) t R J d B T n
          base correction ht (fun v hv => hsource v (by omega)))
      (by
        rw [hmaskEq]
        exact maskShift_bound _ _ _ J d _
          (shiftRow_bound (decode (source n)) t R J d B T ht (hsource n (by omega))))
    refine ⟨?_,hadd.2⟩
    change decode (addBits template _ _ J).words=_
    apply array_eq_of_coeff J (by simp) (by simp [SemiprimeLocalArrayFrontend.acquireCorrected,addJet_size])
    intro i hi
    rw [hadd.1 i hi,hold.1,hmaskEq]
    rfl

/-- Exact finite-source refinement, requiring no coefficient or corrected-port output oracle. -/
theorem acquireCorrectedFin_correct {n : ℕ} (template : List Bool) (source : Fin n → Array RationalWord)
    (tw : RationalWord) (t : ℤ) (R J d B T : ℕ) (base correction : Fin n → Bool)
    (hvalid : ∀ v,Valid (source v)) (htw : tw.Valid) (htval : tw.value=(t:ℚ))
    (hd : 0< d) (ht : t.natAbs≤ T) (hden : d<2^template.length)
    (hrow : hornerBound J B T (R+1)<2^template.length)
    (hnum : n*hornerBound J B T (R+1)<2^template.length)
    (hsource : ∀ v i,i≤ R → Representation (coefficient (decode (source v)) i) d B) :
    decode (acquireCorrectedFin template source tw R J base correction).words=
      (SemiprimeLocalArrayFrontend.acquireCorrectedFin (fun v => decode (source v)) (t:ℚ)
        R J base correction).coefficients ∧
      Valid (acquireCorrectedFin template source tw R J base correction).words := by
  unfold acquireCorrectedFin SemiprimeLocalArrayFrontend.acquireCorrectedFin
  have h := acquireCorrected_correct template (fun v => if h : v< n then source ⟨v,h⟩ else #[])
    tw t R J d B T n (fun v => if h : v< n then base ⟨v,h⟩ else false)
    (fun v => if h : v< n then correction ⟨v,h⟩ else false)
    (by intro v hv; simpa only [dite_eq_left hv] using hvalid ⟨v,hv⟩)
    htw htval hd ht hden hrow hnum (by
      intro v hv i hi
      simpa only [dite_eq_left hv] using hsource ⟨v,hv⟩ i hi)
  have he : (fun v => decode (if h : v<n then source ⟨v,h⟩ else #[]))=
      (fun v => if h : v<n then decode (source ⟨v,h⟩) else #[]) := by
    funext v
    split_ifs <;> simp [decode]
  rw [he] at h
  exact h

/-- A single ORIGINAL-parameter polynomial width covers all shift and port sums. -/
def portWidth (b R : ℕ) : ℕ := 3*b+(2*b+2)*(R+1)+3

/-- The physical template always has space for literal zeros and ones. -/
theorem portWidth_pos (b R : ℕ) : 0< portWidth b R := by unfold portWidth; omega

/-- All numerical fits used by physical acquisition follow from original dyadic
source/node/dimension bounds, not from an output or intermediate fit oracle. -/
theorem port_numeric_bounds (b R J d B T n : ℕ)
    (hd : d≤2^b) (hB : B≤2^b) (hT : T≤2^b) (hJ : J≤2^b) (hn : n≤2^b) :
    d<2^(portWidth b R) ∧
      hornerBound J B T (R+1)<2^(portWidth b R) ∧
      n*hornerBound J B T (R+1)<2^(portWidth b R) := by
  have hh := SemiprimeLocalExecutionBitBounds.hornerBound_le J B T b (R+1) hJ hB hT
  have hm := Nat.mul_le_mul hn hh
  have hpow : (2^b)*(2^(b+(2*b+2)*(R+1)))=2^(2*b+(2*b+2)*(R+1)) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hm
  refine ⟨hd.trans_lt (Nat.pow_lt_pow_right (by decide) ?_),
    hh.trans_lt (Nat.pow_lt_pow_right (by decide) ?_),
    hm.trans_lt (Nat.pow_lt_pow_right (by decide) ?_)⟩ <;> unfold portWidth <;> omega

/-- The complete finite physical corrected port is correct at the derived
public width. Only ORIGINAL source representations and integer-node bounds occur. -/
theorem acquireCorrectedFin_at_width {n : ℕ} (b R J d B T : ℕ)
    (source : Fin n → Array RationalWord) (tw : RationalWord) (t : ℤ)
    (base correction : Fin n → Bool)
    (hvalid : ∀ v,Valid (source v)) (htw : tw.Valid) (htval : tw.value=(t:ℚ))
    (hd : 0< d) (ht : t.natAbs≤ T)
    (hdb : d≤2^b) (hBb : B≤2^b) (hTb : T≤2^b) (hJb : J≤2^b) (hnb : n≤2^b)
    (hsource : ∀ v i,i≤ R → Representation (coefficient (decode (source v)) i) d B) :
    decode (acquireCorrectedFin (List.replicate (portWidth b R) false) source tw R J base correction).words=
      (SemiprimeLocalArrayFrontend.acquireCorrectedFin (fun v => decode (source v)) (t:ℚ)
        R J base correction).coefficients ∧
      Valid (acquireCorrectedFin (List.replicate (portWidth b R) false) source tw R J base correction).words := by
  have hh := port_numeric_bounds b R J d B T n hdb hBb hTb hJb hnb
  apply acquireCorrectedFin_correct _ source tw t R J d B T base correction hvalid htw htval hd ht
  · simpa only [List.length_replicate] using hh.1
  · simpa only [List.length_replicate] using hh.2.1
  · simpa only [List.length_replicate] using hh.2.2
  · exact hsource

end RiemannGaussian.SemiprimeCorrectedPortBits
