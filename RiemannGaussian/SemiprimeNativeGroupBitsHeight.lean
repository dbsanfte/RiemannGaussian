/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNativeGroupBits

/-! # Actual physical native group common-denominator height
The construction proof retains the product representation discarded by the
older value/validity corollary. No intermediate or output height is supplied.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeNativeGroupBitsHeight
open scoped BigOperators
open SemiprimeNativeGroupBits SemiprimeRationalBits SemiprimeJetBits
open SemiprimeLocalBits SemiprimeLocalArrayFrontend SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeLocalExecutionHeight SemiprimeLocalBitsCorrectness SemiprimeHermiteArrayHeight

/-- One denominator shared by every actual group coefficient. -/
def denominator (d s F : ℕ) : ℕ := (d^s)^F

/-- Uniform product-factor numerator base acquired from original source bounds. -/
def numeratorBase (n J R d B T s : ℕ) : ℕ :=
  (J+1)*(d^s+(localBase J d (n*hornerBound J B T (R+1))+d+1)^s+1)

/-- One bound shared by every actual group coefficient numerator. -/
def numerator (n J R d B T s F : ℕ) : ℕ := (numeratorBase n J R d B T s)^(2*F)

/-- Explicit fixed polynomial exponent covering both integer magnitudes. -/
def exponent (b R F s : ℕ) : ℕ := b*s*F+factorExponent b R s*(2*F)+1

/-- Positive original source denominators remain positive under the actual factor product. -/
theorem denominator_pos (d s F : ℕ) (hd : 0<d) : 0<denominator d s F :=
  pow_pos (pow_pos hd s) F

/-- The common denominator has a public dyadic bound from original input bits. -/
theorem denominator_dyadic (b R d s F : ℕ) (hd : d≤2^b) :
    denominator d s F≤2^(exponent b R F s) := by
  have h := Nat.pow_le_pow_left (Nat.pow_le_pow_left hd s) F
  calc
    denominator d s F ≤ ((2^b)^s)^F := h
    _ = 2^(b*s*F) := by rw [← pow_mul,← pow_mul]; congr 1; ring
    _ ≤ 2^(exponent b R F s) := Nat.pow_le_pow_right (by decide) (by unfold exponent; omega)

/-- The common numerator bound has a public dyadic bound from original input bits. -/
theorem numerator_dyadic (b R J d B T n s F : ℕ)
    (hdb : d≤2^b) (hBb : B≤2^b) (hTb : T≤2^b) (hJb : J≤2^b) (hnb : n≤2^b) :
    numerator n J R d B T s F≤2^(exponent b R F s) := by
  have hn := factor_base_dyadic b R J d B T n s hdb hBb hTb hJb hnb
  have h := Nat.pow_le_pow_left hn (2*F)
  rw [← pow_mul] at h
  exact h.trans (Nat.pow_le_pow_right (by decide) (by unfold exponent; omega))

/-- Actual group output height, reconstructed from the original product proof. -/
theorem run_height {n F r : ℕ} {h : Fin r → ℕ} (b : ℕ) (arity : Fin F → ℕ) (J R d B T : ℕ)
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
    ArrayBound (decode (run b arity J R tw source grouping assigned correction entries g a).words) J
      (denominator d (∑ e,arity e) F) (numerator n J R d B T (∑ e,arity e) F) := by
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
  simpa only [run,template,W,s,bits,getBit,callback,legacy,List.length_ofFn,
    denominator,numerator,numeratorBase,D,N,B0,base] using hp.2.2

end RiemannGaussian.SemiprimeNativeGroupBitsHeight
