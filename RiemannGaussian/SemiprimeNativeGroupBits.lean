/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNativeLocalBits
import RiemannGaussian.SemiprimeNativeGroupExecution

/-! # Physical native group multiplication in the original factor order
The width uses total incidence only polynomially. Every Boolean interpolation
still runs at its own original local arity. Source-word acquisition and the
final rational boundary are explicitly separate from physical group arithmetic.
-/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace RiemannGaussian.SemiprimeNativeGroupBits
open scoped BigOperators
open SemiprimeRationalBits SemiprimeJetBits SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeLocalExecutionHeight SemiprimeLocalBits SemiprimeLocalBitsBounds
open SemiprimeLocalArrayFrontend SemiprimeHermiteArrayHeight

/-- Derived factor/product coefficient exponent, using original parameter bits. -/
def factorExponent (b R s : ℕ) : ℕ :=
  b+(2*SemiprimeNativeLocalBits.portExponent b R+4)*(s+1)+3

/-- A common polynomial width for all physical local calls and product suffixes. -/
def groupWidth (b R F s : ℕ) : ℕ :=
  SemiprimeNativeLocalBits.publicWidth b R s+factorExponent b R s*(2*F+2)+1

/-- Literal physical truncated-one report. -/
def oneBits (J : ℕ) : JetReport := ⟨oneArray J,3*J+1⟩

/-- The same tail-first factor product as the original native group. Each
callback and suffix report is cached once and retained before multiplication. -/
def productList {A : Type} (template : List Bool) (J : ℕ) : List A → (A → JetReport) → JetReport
  | [],_ => oneBits J
  | e::tail,f =>
      let left := f e
      let right := productList template J tail f
      let out := multiplyBits template left.words right.words J
      ⟨out.words,left.clock+right.clock+out.clock+J+3⟩

/-- Selected finite base-bit allocation and factor-control allowance. -/
def groupControl (n F J W : ℕ) : ℕ := 20*(n+F+1)*(J+1)*(W+1)+10*n+10*F+10

/-- Actual word-backed group, with the original factor order and gated table
ownership. Total incidence affects width only, never a Boolean exponential. -/
def run {n F r : ℕ} {h : Fin r → ℕ} (b : ℕ) (arity : Fin F → ℕ) (J R : ℕ)
    (tw : RationalWord) (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (grouping : Fin n ≃ ((g : Fin r) × Fin (h g))) (assigned : Fin F → Fin r)
    (correction : Fin n → Bool) (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (g : Fin r) (a : (g : Fin r) → Fin (h g) → Bool) : JetReport :=
  let W := groupWidth b R F (∑ e,arity e)
  let template := List.replicate W false
  let bits := Array.ofFn (SemiprimeNativeGroupExecution.baseBits grouping a)
  let getBit := fun v : Fin n => bits[v.val]'(by simp [bits])
  let result := productList template J (List.ofFn (fun e : Fin F => e)) (fun e =>
    if assigned e=g then SemiprimeNativeLocalBits.nativeLocal template (arity e) J R tw
      (source e) getBit correction (entries e) else oneBits J)
  ⟨result.words,result.clock+groupControl n F J W⟩

/-- Actual output-word normalization/copy allowance at the retained rational
counter boundary. This is a ledger boundary, not a claimed tape compiler. -/
def decodeWork (words : Array RationalWord) : ℕ :=
  (words.toList.map (fun w => 20000*(w.numerator.magnitude.length+w.denominator.length+1)^3+5)).sum+
    2*words.size+1

/-- Embed one actual physical report in the original scalar traversal while
retaining its complete clock and actual output-copy allowance. -/
def toScalarRun (report : JetReport) : SemiprimeFibreArrayExecution.Run :=
  ⟨⟨decode report.words,0,0⟩,report.clock+decodeWork report.words⟩

/-- The scalar boundary keeps exactly the actual decoded word array. -/
theorem toScalarRun_coefficients (report : JetReport) :
    (toScalarRun report).jet.coefficients=decode report.words := rfl

/-- No physical group work is erased by the scalar traversal boundary. -/
theorem toScalarRun_work (report : JetReport) :
    (toScalarRun report).work=report.clock+decodeWork report.words := by
  simp only [toScalarRun,SemiprimeFibreArrayExecution.Run.work,Nat.zero_add]

/-- Every suffix has exactly the retained precision. -/
theorem productList_size {A : Type} (template : List Bool) (J : ℕ) (xs : List A) (f : A → JetReport) :
    (productList template J xs f).words.size=J := by
  cases xs <;> simp only [productList,oneBits,oneArray_size,multiplyBits_size]

/-- The actual group result has the requested precision. -/
theorem run_size {n F r : ℕ} {h : Fin r → ℕ} (b : ℕ) (arity : Fin F → ℕ) (J R : ℕ)
    (tw : RationalWord) (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (grouping : Fin n ≃ ((g : Fin r) × Fin (h g))) (assigned : Fin F → Fin r)
    (correction : Fin n → Bool) (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (g : Fin r) (a : (g : Fin r) → Fin (h g) → Bool) :
    (run b arity J R tw source grouping assigned correction entries g a).words.size=J := by
  simp only [run,productList_size]

/-- Physical one words decode exactly to the original one-jet array. -/
theorem oneBits_decode (J : ℕ) : decode (oneBits J).words=(SemiprimeArrayOps.oneJet J).coefficients := by
  apply SemiprimeCorrectedPortBits.array_eq_of_coeff J
  · simp only [oneBits,decode_size,oneArray_size]
  · simp only [SemiprimeArrayOps.oneJet,Array.size_ofFn]
  · exact oneArray_coefficient J

/-- The original same-order product also has exactly its requested precision. -/
theorem scalarProduct_size {A : Type} (J : ℕ) (xs : List A)
    (f : A → SemiprimeFibreArrayExecution.Run) :
    (SemiprimeFibreArrayExecution.productList J xs f).jet.coefficients.size=J := by
  cases xs <;> simp only [SemiprimeFibreArrayExecution.productList,
    SemiprimeFibreArrayExecution.oneRun,SemiprimeFibreArrayExecution.mulRun,
    SemiprimeArrayOps.oneJet,SemiprimeJetArray.multiply_size,Array.size_ofFn]

/-- A public dyadic base bound controls every required product power. -/
theorem power_lt_width (N k L e W : ℕ) (hN : N ≤ 2^k)
    (he : e ≤ 2*L+2) (hW : k*(2*L+2)<W) : N^e<2^W := by
  have hp := Nat.pow_le_pow_left hN e
  rw [← pow_mul] at hp
  exact hp.trans_lt (Nat.pow_lt_pow_right (by decide)
    ((Nat.mul_le_mul_left k he).trans_lt hW))

/-- Same-order physical product correctness and all suffix fits follow from
common original callback representations and a derived dyadic base. -/
theorem productList_correct {A : Type} (template : List Bool) (J D B N k : ℕ)
    (xs : List A) (f : A → JetReport) (legacy : A → SemiprimeFibreArrayExecution.Run)
    (hD : 0<D) (hDN : D ≤ N) (hBN : B ≤ N) (hJN : J ≤ N) (hNk : N ≤ 2^k)
    (hwidth : k*(2*xs.length+2)<template.length)
    (hf : ∀ e∈xs, decode (f e).words=(legacy e).jet.coefficients ∧
      Valid (f e).words ∧ ArrayBound (decode (f e).words) J D B) :
    decode (productList template J xs f).words=
      (SemiprimeFibreArrayExecution.productList J xs legacy).jet.coefficients ∧
    Valid (productList template J xs f).words ∧
    ArrayBound (decode (productList template J xs f).words) J (D^xs.length) (N^(2*xs.length)) := by
  induction xs with
  | nil =>
    refine ⟨oneBits_decode J,oneArray_valid J,?_⟩
    simpa only [List.length_nil,pow_zero,mul_zero,productList,oneBits] using
      SemiprimeLocalBitsCorrectness.one_bound J 1 (by decide)
  | cons e tail ih =>
    have ht : k*(2*tail.length+2)<template.length := by
      simp only [List.length_cons,Nat.mul_succ] at hwidth ⊢
      omega
    have hs := ih ht (fun x hx => hf x (by simp only [List.mem_cons]; exact Or.inr hx))
    have he := hf e (by simp only [List.mem_cons,true_or])
    have hden : D*D^tail.length<2^template.length := by
      rw [← pow_succ']
      exact (Nat.pow_le_pow_left hDN _).trans_lt
        (power_lt_width N k (tail.length+1) (tail.length+1) template.length hNk (by omega)
          (by simpa only [List.length_cons] using hwidth))
    have hnum0 : J*B*N^(2*tail.length) ≤ N^(2*(tail.length+1)) := by
      have hm := Nat.mul_le_mul_right (N^(2*tail.length)) (Nat.mul_le_mul hJN hBN)
      calc
        _ ≤ N*N*N^(2*tail.length) := hm
        _ = _ := by rw [← pow_two,← pow_add]; congr 1; omega
    have hnum := hnum0.trans_lt (power_lt_width N k (tail.length+1)
      (2*(tail.length+1)) template.length hNk (by omega)
      (by simpa only [List.length_cons] using hwidth))
    have hm := multiplyBits_correct template (f e).words (productList template J tail f).words
      J D (D^tail.length) B (N^(2*tail.length)) he.2.1 hs.2.1 hD (pow_pos hD _)
      hden hnum he.2.2 hs.2.2
    have heq : decode (multiplyBits template (f e).words (productList template J tail f).words J).words=
        (SemiprimeJetArray.multiply (decode (f e).words)
          (decode (productList template J tail f).words) J).coefficients := by
      apply SemiprimeCorrectedPortBits.array_eq_of_coeff J
      · simp only [decode_size,multiplyBits_size]
      · exact SemiprimeJetArray.multiply_size _ _ _
      · exact hm.1
    refine ⟨?_,hm.2,?_⟩
    · change decode (multiplyBits template (f e).words (productList template J tail f).words J).words=_
      rw [heq,he.1,hs.1]
      rfl
    · intro i hi
      change Representation (coefficient (decode
        (multiplyBits template (f e).words (productList template J tail f).words J).words) i)
          (D^(e::tail).length) (N^(2*(e::tail).length))
      rw [heq]
      have hr := multiply_representation (decode (f e).words)
        (decode (productList template J tail f).words) D (D^tail.length)
        B (N^(2*tail.length)) J he.2.2 hs.2.2 i hi
      have hb := representation_mono hr hnum0
      simpa only [List.length_cons,pow_succ'] using hb

/-- An original factor arity is at most total incidence. -/
theorem arity_le_total {F : ℕ} (arity : Fin F → ℕ) (e : Fin F) : arity e ≤ ∑ x,arity x :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)

/-- The original local numerator base and a common denominator give a single
public dyadic base for all factor and product-suffix representations. -/
theorem factor_base_dyadic (b R J d B T n s : ℕ)
    (hdb : d ≤ 2^b) (hBb : B ≤ 2^b) (hTb : T ≤ 2^b) (hJb : J ≤ 2^b) (hnb : n ≤ 2^b) :
    (J+1)*(d^s+(localBase J d (n*hornerBound J B T (R+1))+d+1)^s+1) ≤
      2^(factorExponent b R s) := by
  let p := SemiprimeNativeLocalBits.portExponent b R
  have hbp : b ≤ p := by dsimp [p,SemiprimeNativeLocalBits.portExponent]; omega
  have hdp := hdb.trans (Nat.pow_le_pow_right (by decide : 0<2) hbp)
  have hJp := hJb.trans (Nat.pow_le_pow_right (by decide : 0<2) hbp)
  have hP := SemiprimeNativeLocalBits.port_numerator_le b R J B T n hJb hBb hTb hnb
  have hL := SemiprimeLocalExecutionBitBounds.localBase_le J d
    (n*hornerBound J B T (R+1)) p hJp hdp hP
  have hq : p ≤ 2*p+2 := by omega
  have hdq := hdp.trans (Nat.pow_le_pow_right (by decide : 0<2) hq)
  have hone : 1 ≤ 2^(2*p+2) := Nat.one_le_pow _ _ (by decide)
  have hbase : localBase J d (n*hornerBound J B T (R+1))+d+1 ≤ 2^(2*p+4) := by
    rw [show 2*p+4=(2*p+2)+2 by omega,pow_add]
    norm_num
    omega
  have hdlarge := hdp.trans (Nat.pow_le_pow_right (by decide : 0<2) (show p ≤ 2*p+4 by omega))
  have hD := Nat.pow_le_pow_left hdlarge s
  have hB := Nat.pow_le_pow_left hbase s
  rw [← pow_mul] at hD hB
  have hone' : 1 ≤ 2^((2*p+4)*s) := Nat.one_le_pow _ _ (by decide)
  have hsum : d^s+(localBase J d (n*hornerBound J B T (R+1))+d+1)^s+1 ≤
      2^((2*p+4)*s+2) := by
    rw [pow_add]
    norm_num
    omega
  have hJ : J+1 ≤ 2^(b+1) := by rw [pow_succ]; have := Nat.one_le_pow b 2 (by decide); omega
  have hm := Nat.mul_le_mul hJ hsum
  rw [← pow_add] at hm
  apply hm.trans
  apply Nat.pow_le_pow_right (by decide)
  dsimp [factorExponent,p]
  nlinarith

/-- Full physical group refinement with no runtime d/B inputs and no
intermediate Fits advice. The common width uses total incidence polynomially. -/
theorem run_spec {n F r : ℕ} {h : Fin r → ℕ} (b : ℕ) (arity : Fin F → ℕ) (J R d B T : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (tw : RationalWord) (t : ℤ) (grouping : Fin n ≃ ((g : Fin r) × Fin (h g)))
    (assigned : Fin F → Fin r) (correction : Fin n → Bool)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (g : Fin r) (a : (g : Fin r) → Fin (h g) → Bool)
    (hvalid : ∀ e i v,Valid (source e i v)) (htw : tw.Valid) (htval : tw.value=(t:ℚ))
    (hd : 0<d) (ht : t.natAbs ≤ T)
    (hdb : d ≤ 2^b) (hBb : B ≤ 2^b) (hTb : T ≤ 2^b) (hJb : J ≤ 2^b) (hnb : n ≤ 2^b)
    (hsource : ∀ e i v k,k ≤ R → Representation (coefficient (decode (source e i v)) k) d B)
    (hentries : ∀ e eta,(entries e eta).bits.value.natAbs ≤ 1) :
    decode (run b arity J R tw source grouping assigned correction entries g a).words=
      (SemiprimeNativeGroupExecution.nativeGroup arity J R (t:ℚ)
        (fun e i v => decode (source e i v)) grouping assigned correction
        (fun e => table (entries e)) g a).jet.coefficients ∧
    Valid (run b arity J R tw source grouping assigned correction entries g a).words := by
  let s := ∑ e,arity e
  let W := groupWidth b R F s
  let template := List.replicate W false
  let bits := Array.ofFn (SemiprimeNativeGroupExecution.baseBits grouping a)
  let getBit := fun v : Fin n => bits[v.val]'(by simp [bits])
  let callback := fun e => if assigned e=g then
    SemiprimeNativeLocalBits.nativeLocal template (arity e) J R tw
      (source e) getBit correction (entries e) else oneBits J
  let legacy := fun e => if assigned e=g then
    SemiprimeNativeGroupExecution.localRun (arity e) J R (t:ℚ)
      (fun i v => decode (source e i v)) getBit correction (table (entries e))
    else SemiprimeFibreArrayExecution.oneRun J
  let base := localBase J d (n*hornerBound J B T (R+1))+d+1
  let D := d^s
  let B0 := base^s
  let N := (J+1)*(D+B0+1)
  let k := factorExponent b R s
  have hdBase : d ≤ base := by dsimp [base]; omega
  have hlocalBase : localBase J d (n*hornerBound J B T (R+1)) ≤ base := by dsimp [base]; omega
  have hD : 0<D := pow_pos hd _
  have hB0 : D ≤ B0 := Nat.pow_le_pow_left hdBase s
  have hDN : D ≤ N := by
    have hm := Nat.mul_le_mul_right (D+B0+1) (show 1 ≤ J+1 by omega)
    simp only [one_mul] at hm
    dsimp [N]
    omega
  have hBN : B0 ≤ N := by
    have hm := Nat.mul_le_mul_right (D+B0+1) (show 1 ≤ J+1 by omega)
    simp only [one_mul] at hm
    dsimp [N]
    omega
  have hJN : J ≤ N := by
    have hm := Nat.mul_le_mul_left (J+1) (show 1 ≤ D+B0+1 by omega)
    simp only [mul_one] at hm
    dsimp [N]
    omega
  have hNk : N ≤ 2^k := factor_base_dyadic b R J d B T n s hdb hBb hTb hJb hnb
  have hf (e : Fin F) (_ : e∈List.ofFn (fun e : Fin F => e)) :
      decode (callback e).words=(legacy e).jet.coefficients ∧
        Valid (callback e).words ∧ ArrayBound (decode (callback e).words) J D B0 := by
    by_cases he : assigned e=g
    · have hw : SemiprimeNativeLocalBits.publicWidth b R (arity e) ≤ template.length := by
        have hm := SemiprimeNativeLocalBits.publicWidth_mono_arity b R (arity_le_total arity e)
        dsimp only [template,W]
        rw [List.length_replicate]
        unfold groupWidth
        change SemiprimeNativeLocalBits.publicWidth b R (arity e) ≤
          SemiprimeNativeLocalBits.publicWidth b R s at hm
        omega
      have hl := SemiprimeNativeLocalBits.nativeLocal_correct template b (arity e) R J d B T
        (source e) tw t getBit correction (entries e) hw (hvalid e) htw htval hd ht
        hdb hBb hTb hJb hnb (hsource e) (hentries e)
      refine ⟨?_,?_,?_⟩
      · simpa only [callback,legacy,ite_eq_left he,SemiprimeNativeGroupExecution.localRun] using hl.1
      · simpa only [callback,ite_eq_left he] using hl.2.1
      · intro i hi
        have hp := representation_mono (hl.2.2 i hi)
          (Nat.pow_le_pow_left hlocalBase (arity e))
        have hext := representation_power_extend d base (arity e) s hd hdBase (arity_le_total arity e) hp
        simpa only [callback,ite_eq_left he,D,B0] using hext
    · refine ⟨?_,?_,?_⟩
      · simpa only [callback,legacy,ite_eq_right he,SemiprimeFibreArrayExecution.oneRun] using oneBits_decode J
      · simpa only [callback,ite_eq_right he,oneBits] using oneArray_valid J
      · have hb := arrayBound_mono (SemiprimeLocalBitsCorrectness.one_bound J D hD) hB0
        simpa only [callback,ite_eq_right he,oneBits] using hb
  have hwidth : k*(2*(List.ofFn (fun e : Fin F => e)).length+2)<template.length := by
    dsimp only [template,W,groupWidth,k]
    simp only [List.length_ofFn,List.length_replicate]
    omega
  have hp := productList_correct template J D B0 N k (List.ofFn (fun e : Fin F => e))
    callback legacy hD hDN hBN hJN hNk hwidth hf
  refine ⟨?_,?_⟩
  · simpa only [run,SemiprimeNativeGroupExecution.nativeGroup,template,W,s,bits,getBit,callback,legacy] using hp.1
  · simpa only [run,template,W,s,bits,getBit,callback] using hp.2.1

/-- Exact decoded native-group array for the parent counter adapter. -/
theorem run_correct {n F r : ℕ} {h : Fin r → ℕ} (b : ℕ) (arity : Fin F → ℕ) (J R d B T : ℕ)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (tw : RationalWord) (t : ℤ) (grouping : Fin n ≃ ((g : Fin r) × Fin (h g)))
    (assigned : Fin F → Fin r) (correction : Fin n → Bool)
    (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (g : Fin r) (a : (g : Fin r) → Fin (h g) → Bool)
    (hvalid : ∀ e i v,Valid (source e i v)) (htw : tw.Valid) (htval : tw.value=(t:ℚ))
    (hd : 0<d) (ht : t.natAbs ≤ T)
    (hdb : d ≤ 2^b) (hBb : B ≤ 2^b) (hTb : T ≤ 2^b) (hJb : J ≤ 2^b) (hnb : n ≤ 2^b)
    (hsource : ∀ e i v k,k ≤ R → Representation (coefficient (decode (source e i v)) k) d B)
    (hentries : ∀ e eta,(entries e eta).bits.value.natAbs ≤ 1) :
    decode (run b arity J R tw source grouping assigned correction entries g a).words=
      (SemiprimeNativeGroupExecution.nativeGroup arity J R (t:ℚ)
        (fun e i v => decode (source e i v)) grouping assigned correction
        (fun e => table (entries e)) g a).jet.coefficients :=
  (run_spec b arity J R d B T source tw t grouping assigned correction entries g a
    hvalid htw htval hd ht hdb hBb hTb hJb hnb hsource hentries).1

end RiemannGaussian.SemiprimeNativeGroupBits
