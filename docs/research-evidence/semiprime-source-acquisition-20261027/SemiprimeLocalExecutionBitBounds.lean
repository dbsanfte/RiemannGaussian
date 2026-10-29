/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLocalExecutionHeight
import RiemannGaussian.SemiprimeRationalBits

/-!
# Polynomial bit budgets for the local interpreter's actual states

The inequalities convert the literal numerator/denominator representations to
normalized rational fits. They do not assert a primitive interpreter has already
been assembled, and do not assume that desired intermediate outputs fit.
-/
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace RiemannGaussian.SemiprimeLocalExecutionBitBounds
open SemiprimeLocalExecutionHeight SemiprimeLocalArrayFrontend
open SemiprimeJetArray SemiprimeJetArrayHeight SemiprimeRationalBits

/-- A scalar represented with dyadically bounded numerator and denominator fits
one additional bit beyond their larger exponent. -/
theorem representation_fits {q : ℚ} {d B a b : ℕ} (hd : 0<d)
    (h : Representation q d B) (hdB : d ≤ 2^a) (hBB : B ≤ 2^b) :
    Fits q (a+b+1) := by
  apply fits_of_representation hd h
  · exact hBB.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  · exact hdB.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

/-- The multiplier in the source Horner bound has only O(b) bits. -/
theorem horner_base_le (J T b : ℕ) (hJ : J ≤ 2^b) (hT : T ≤ 2^b) :
    1+J*(T+1) ≤ 2^(2*b+2) := by
  have hp : 1 ≤ 2^b := Nat.one_le_pow _ _ (by decide)
  have hm := Nat.mul_le_mul hJ (Nat.add_le_add_right hT 1)
  have he : 2^(2*b+2) = 4*(2^b)^2 := by
    rw [show 2*b+2=b+b+2 by omega, pow_add, pow_add]
    norm_num
    ring
  rw [he]
  nlinarith

/-- Every Horner suffix numerator has a bit budget linear in its source length. -/
theorem hornerBound_le (J B T b len : ℕ)
    (hJ : J ≤ 2^b) (hB : B ≤ 2^b) (hT : T ≤ 2^b) :
    hornerBound J B T len ≤ 2^(b+(2*b+2)*len) := by
  have hm := Nat.mul_le_mul hB (Nat.pow_le_pow_left (horner_base_le J T b hJ hT) len)
  simpa only [hornerBound, ← pow_mul, ← pow_add] using hm

/-- The completed local interpolation base has at most 2b+2 bits. -/
theorem localBase_le (J d B b : ℕ) (hJ : J ≤ 2^b) (hd : d ≤ 2^b) (hB : B ≤ 2^b) :
    localBase J d B ≤ 2^(2*b+2) := by
  have hm := Nat.mul_le_mul hJ (Nat.add_le_add hd hB)
  have he : 2^(2*b+2) = 4*(2^b)^2 := by
    rw [show 2*b+2=b+b+2 by omega, pow_add, pow_add]
    norm_num
    ring
  rw [he]
  unfold localBase
  nlinarith

/-- The actual Horner suffix fits a polynomial-width primitive-rational buffer. -/
theorem shiftFrom_fits (a : Array ℚ) (t : ℤ) (J d B T b start len : ℕ)
    (hd : 0<d) (hdB : d ≤ 2^b) (hJ : J ≤ 2^b) (hB : B ≤ 2^b) (hT : T ≤ 2^b)
    (ht : t.natAbs ≤ T)
    (ha : ∀ i, start ≤ i → i < start+len → Representation (coefficient a i) d B)
    (i : ℕ) (hi : i < J) :
    Fits (coefficient (shiftFrom a (t : ℚ) J start len).coefficients i)
      (2*b+(2*b+2)*len+1) := by
  have h := representation_fits hd (shiftFrom_bound a t J d B T start len ht ha i hi)
    hdB (hornerBound_le J B T b len hJ hB hT)
  convert h using 1
  congr 1
  ring

/-- Every actual corrected-input prefix fits, without assuming a Taylor-output height. -/
theorem acquireCorrected_fits (source : ℕ → Array ℚ) (t : ℤ)
    (R J d B T b n : ℕ) (base correction : ℕ → Bool)
    (hd : 0<d) (hdB : d ≤ 2^b) (hJ : J ≤ 2^b) (hB : B ≤ 2^b)
    (hT : T ≤ 2^b) (hn : n ≤ 2^b) (ht : t.natAbs ≤ T)
    (hs : ∀ v < n, ∀ i ≤ R, Representation (coefficient (source v) i) d B)
    (i : ℕ) (hi : i < J) :
    Fits (coefficient (acquireCorrected source (t : ℚ) R J base correction n).coefficients i)
      (3*b+(2*b+2)*(R+1)+1) := by
  have hnum : n*hornerBound J B T (R+1) ≤ 2^(2*b+(2*b+2)*(R+1)) := by
    have hm := Nat.mul_le_mul hn (hornerBound_le J B T b (R+1) hJ hB hT)
    convert hm using 1
    ring
  convert representation_fits hd
    (acquireCorrected_bound source t R J d B T n base correction ht hs i hi) hdB hnum using 1
  congr 1
  ring

/-- Every recursive branch output has a bit budget linear in the branch arity. -/
theorem localEvaluate_fits (J w d B b : ℕ) (hd : 0<d)
    (hJ : J ≤ 2^b) (hdB : d ≤ 2^b) (hB : B ≤ 2^b)
    (T : (Fin w → Bool) → EntryReport) (inputs : Fin w → Array ℚ)
    (hT : ∀ eta, (T eta).value.natAbs ≤ 1) (hinputs : ∀ v, ArrayBound (inputs v) J d B)
    (i : ℕ) (hi : i < J) :
    Fits (coefficient (localEvaluate J w T inputs).coefficients i) ((3*b+2)*w+1) := by
  have hden : d^w ≤ 2^(b*w) := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left hdB w
  have hnum : localBase J d B^w ≤ 2^((2*b+2)*w) := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left (localBase_le J d B b hJ hdB hB) w
  convert representation_fits (pow_pos hd _) (localEvaluate_representation J w d B hd T inputs hT hinputs i hi)
    hden hnum using 1
  congr 1
  ring

/-- Every partial Horner multiplication fits the next-suffix width budget. -/
theorem shiftFrom_prefix_fits (a : Array ℚ) (t : ℤ) (J d B T b start len k p : ℕ)
    (hd : 0<d) (hdB : d ≤ 2^b) (hJ : J ≤ 2^b) (hB : B ≤ 2^b) (hT : T ≤ 2^b)
    (ht : t.natAbs ≤ T)
    (ha : ∀ i, start ≤ i → i < start+len → Representation (coefficient a i) d B)
    (hk : k < J) (hp : p ≤ k) :
    Fits (dotPrefix (shiftFrom a (t : ℚ) J start len).coefficients
      #[(t : ℚ),1] (k-1) p).value (2*b+(2*b+2)*(len+1)+1) := by
  have hrep := shiftFrom_product_prefix a t J d B T start len k p ht ha hk hp
  have hn : p*hornerBound J B T len*(T+1) ≤ hornerBound J B T (len+1) := by
    unfold hornerBound
    rw [pow_succ]
    have hmul := Nat.mul_le_mul_right (B*(1+J*(T+1))^len*(T+1)) (show p ≤ J by omega)
    have he : B*((1+J*(T+1))^len*(1+J*(T+1))) =
        J*(B*(1+J*(T+1))^len*(T+1))+B*(1+J*(T+1))^len := by ring
    rw [he]
    calc
      _ = p*(B*(1+J*(T+1))^len*(T+1)) := by ring
      _ ≤ J*(B*(1+J*(T+1))^len*(T+1)) := hmul
      _ ≤ _ := Nat.le_add_right _ _
  have hr := representation_mono hrep hn
  have hf := representation_fits hd hr hdB (hornerBound_le J B T b (len+1) hJ hB hT)
  convert hf using 1
  congr 1
  ring

/-- Product-denominator and numerator budgets for every local nonleaf buffer. -/
theorem local_level_bounds (J d B b w : ℕ)
    (hJ : J ≤ 2^b) (hd : d ≤ 2^b) (hB : B ≤ 2^b) :
    d*d^w ≤ 2^(b*(w+1)) ∧
      J*(d+B)*localBase J d B^w ≤ 2^((2*b+2)*(w+1)) := by
  constructor
  · have hm := Nat.pow_le_pow_left hd (w+1)
    calc
      d*d^w = d^(w+1) := (pow_succ' _ _).symm
      _ ≤ (2^b)^(w+1) := hm
      _ = _ := by rw [← pow_mul]
  · have hb := localBase_le J d B b hJ hd hB
    have hp := Nat.pow_le_pow_left hb (w+1)
    have hfac : J*(d+B) ≤ localBase J d B := by
      unfold localBase
      nlinarith [Nat.zero_le (J*(d+B))]
    have hm := Nat.mul_le_mul_right (localBase J d B^w) hfac
    calc
      _ ≤ localBase J d B * localBase J d B^w := hm
      _ = localBase J d B^(w+1) := (pow_succ' _ _).symm
      _ ≤ _ := by simpa only [← pow_mul] using hp

/-- Every false and true convolution accumulator in the actual local trace fits.
The width is linear in branch arity and in the port coefficient bit budget. -/
theorem localStep_prefix_fits (J w d B b : ℕ) (hd : 0<d)
    (hJ : J ≤ 2^b) (hdB : d ≤ 2^b) (hB : B ≤ 2^b)
    (T : (Fin (w+1) → Bool) → EntryReport) (inputs : Fin (w+1) → Array ℚ)
    (hsafe : LocalStepSafe J w d B T inputs) (k p : ℕ) (hk : k < J) (hp : p ≤ k) :
    Fits (dotPrefix (SemiprimeArrayOps.addJet (SemiprimeArrayOps.oneJet J).coefficients
      (SemiprimeArrayOps.scaleJet (inputs 0) (-1) J).coefficients J).coefficients
      (localEvaluate J w (fun eta => T (Fin.cons false eta)) (fun v => inputs v.succ)).coefficients
      (k-1) p).value ((3*b+2)*(w+1)+1) ∧
    Fits (dotPrefix (inputs 0)
      (localEvaluate J w (fun eta => T (Fin.cons true eta)) (fun v => inputs v.succ)).coefficients
      (k-1) p).value ((3*b+2)*(w+1)+1) := by
  have hlev := local_level_bounds J d B b w hJ hdB hB
  have hleft := representation_mono (hsafe.leftPrefix k hk p hp)
    (Nat.mul_le_mul_right (localBase J d B^w) (Nat.mul_le_mul_right (d+B) (show p ≤ J by omega)))
  have hright := representation_mono (hsafe.rightPrefix k hk p hp)
    (show p*B*localBase J d B^w ≤ J*(d+B)*localBase J d B^w by gcongr <;> omega)
  have hl := representation_fits (Nat.mul_pos hd (pow_pos hd _)) hleft hlev.1 hlev.2
  have hr := representation_fits (Nat.mul_pos hd (pow_pos hd _)) hright hlev.1 hlev.2
  constructor
  · convert hl using 1
    congr 1
    ring
  · convert hr using 1
    congr 1
    ring

/-- Both completed multiplication buffers at every local node fit the same width. -/
theorem localStep_buffers_fits (J w d B b : ℕ) (hd : 0<d)
    (hJ : J ≤ 2^b) (hdB : d ≤ 2^b) (hB : B ≤ 2^b)
    (T : (Fin (w+1) → Bool) → EntryReport) (inputs : Fin (w+1) → Array ℚ)
    (hsafe : LocalStepSafe J w d B T inputs) (k : ℕ) (hk : k < J) :
    Fits (coefficient (multiply
      (SemiprimeArrayOps.addJet (SemiprimeArrayOps.oneJet J).coefficients
        (SemiprimeArrayOps.scaleJet (inputs 0) (-1) J).coefficients J).coefficients
      (localEvaluate J w (fun eta => T (Fin.cons false eta)) (fun v => inputs v.succ)).coefficients J).coefficients k)
      ((3*b+2)*(w+1)+1) ∧
    Fits (coefficient (multiply (inputs 0)
      (localEvaluate J w (fun eta => T (Fin.cons true eta)) (fun v => inputs v.succ)).coefficients J).coefficients k)
      ((3*b+2)*(w+1)+1) := by
  have hlev := local_level_bounds J d B b w hJ hdB hB
  have hleft := hsafe.left k hk
  have hright := representation_mono (hsafe.right k hk)
    (show J*B*localBase J d B^w ≤ J*(d+B)*localBase J d B^w by gcongr; omega)
  have hl := representation_fits (Nat.mul_pos hd (pow_pos hd _)) hleft hlev.1 hlev.2
  have hr := representation_fits (Nat.mul_pos hd (pow_pos hd _)) hright hlev.1 hlev.2
  constructor
  · convert hl using 1
    congr 1
    ring
  · convert hr using 1
    congr 1
    ring

/-- Scalar products before accumulation fit the same local-node width. -/
theorem localStep_terms_fits (J w d B b : ℕ) (hd : 0<d)
    (hJ : J ≤ 2^b) (hdB : d ≤ 2^b) (hB : B ≤ 2^b)
    (T : (Fin (w+1) → Bool) → EntryReport) (inputs : Fin (w+1) → Array ℚ)
    (hsafe : LocalStepSafe J w d B T inputs) (k i : ℕ) (hk : k < J) (hi : i ≤ k) :
    Fits (coefficient (SemiprimeArrayOps.addJet (SemiprimeArrayOps.oneJet J).coefficients
      (SemiprimeArrayOps.scaleJet (inputs 0) (-1) J).coefficients J).coefficients i *
      coefficient (localEvaluate J w (fun eta => T (Fin.cons false eta))
        (fun v => inputs v.succ)).coefficients (k-i)) ((3*b+2)*(w+1)+1) ∧
    Fits (coefficient (inputs 0) i * coefficient (localEvaluate J w
      (fun eta => T (Fin.cons true eta)) (fun v => inputs v.succ)).coefficients (k-i))
      ((3*b+2)*(w+1)+1) := by
  have hlev := local_level_bounds J d B b w hJ hdB hB
  have hleft := representation_mono (hsafe.leftTerm k hk i hi)
    (show (d+B)*localBase J d B^w ≤ J*(d+B)*localBase J d B^w by
      have h := Nat.mul_le_mul_right ((d+B)*localBase J d B^w) (show 1 ≤ J by omega)
      simpa only [one_mul, Nat.mul_assoc] using h)
  have hright := representation_mono (hsafe.rightTerm k hk i hi)
    (show B*localBase J d B^w ≤ J*(d+B)*localBase J d B^w by
      calc
        _ ≤ (d+B)*localBase J d B^w := Nat.mul_le_mul_right _ (by omega)
        _ ≤ _ := by
          have h := Nat.mul_le_mul_right ((d+B)*localBase J d B^w) (show 1 ≤ J by omega)
          simpa only [one_mul, Nat.mul_assoc] using h)
  have hl := representation_fits (Nat.mul_pos hd (pow_pos hd _)) hleft hlev.1 hlev.2
  have hr := representation_fits (Nat.mul_pos hd (pow_pos hd _)) hright hlev.1 hlev.2
  constructor
  · convert hl using 1
    congr 1
    ring
  · convert hr using 1
    congr 1
    ring

/-- One explicit polynomial bit budget for the executed coefficient-to-local-value call. -/
theorem nativeLocal_fits {n : ℕ} (w J R d B T b : ℕ) (hd : 0<d)
    (hdB : d ≤ 2^b) (hJ : J ≤ 2^b) (hB : B ≤ 2^b) (hT : T ≤ 2^b) (hn : n ≤ 2^b)
    (t : ℤ) (ht : t.natAbs ≤ T) (source : Fin w → Fin n → Array ℚ)
    (base correction : Fin n → Bool) (entries : (Fin w → Bool) → EntryReport)
    (hentries : ∀ eta, (entries eta).value.natAbs ≤ 1)
    (hs : ∀ v u i, i ≤ R → Representation (coefficient (source v u) i) d B)
    (i : ℕ) (hi : i < J) :
    Fits (coefficient (nativeLocal w J R (t : ℚ) source base correction entries).coefficients i)
      ((3*(2*b+(2*b+2)*(R+1))+2)*w+1) := by
  let p := 2*b+(2*b+2)*(R+1)
  have hbp : b ≤ p := by dsimp [p]; omega
  have hpow : 2^b ≤ 2^p := Nat.pow_le_pow_right (by decide) hbp
  have hnum : n*hornerBound J B T (R+1) ≤ 2^p := by
    have hm := Nat.mul_le_mul hn (hornerBound_le J B T b (R+1) hJ hB hT)
    convert hm using 1
    dsimp [p]
    ring
  let inputs := Array.ofFn (fun v : Fin w => acquireCorrectedFin (source v)
    (t : ℚ) R J base correction)
  let ports := fun v : Fin w => (inputs[v.val]'(by simp [inputs])).coefficients
  have hports (v : Fin w) : ArrayBound (ports v) J d (n*hornerBound J B T (R+1)) := by
    simpa only [ports, inputs, Array.getElem_ofFn] using
      acquireCorrectedFin_bound (source v) t R J d B T base correction ht (hs v)
  exact localEvaluate_fits J w d _ p hd (hJ.trans hpow) (hdB.trans hpow) hnum
    entries ports hentries hports i hi

end RiemannGaussian.SemiprimeLocalExecutionBitBounds
