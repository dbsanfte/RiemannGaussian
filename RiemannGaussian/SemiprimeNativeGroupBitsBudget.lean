/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeNativeGroupBits

/-! # Complete physical native-group arithmetic ledger
All actual local callbacks and product suffixes are retained. Total incidence
appears in the polynomial width; only original local arity appears exponentially.
Source acquisition and the scalar/address boundary remain separately scoped.
-/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeNativeGroupBitsBudget
open scoped BigOperators
open SemiprimeNativeGroupBits SemiprimeRationalBits SemiprimeJetBits SemiprimeLocalBits

/-- Every acquired physical product suffix fits the actual template. -/
theorem productList_bounded {A : Type} (template : List Bool) (J : ℕ)
    (xs : List A) (f : A → JetReport) (ht : 0< template.length) :
    Bounded (productList template J xs f).words template.length := by
  cases xs with
  | nil => exact oneArray_bounded J _ ht
  | cons e tail => exact multiplyBits_bounded template ht _ _ J

/-- Actual convolution instructions on two J-word product buffers. -/
def multiplyBudget (W J : ℕ) : ℕ :=
  J*(J*(40000*(W+1)^3+4)+4+J*((J+1)*(2*W+3)+(J+1)*(2*W+3)))+(2*J+1)

/-- Tail-first physical multiplication pays every callback once and every
suffix multiplication/copy/control step. -/
theorem productList_clock {A : Type} (template : List Bool) (J B : ℕ)
    (xs : List A) (f : A → JetReport) (ht : 0< template.length)
    (hf : ∀ e∈xs,(f e).clock≤ B)
    (hw : ∀ e∈xs,Bounded (f e).words template.length)
    (hs : ∀ e∈xs,(f e).words.size≤ J) :
    (productList template J xs f).clock≤
      xs.length*(B+multiplyBudget template.length J+J+3)+(3*J+1) := by
  induction xs with
  | nil => simp [productList,oneBits]
  | cons e tail ih =>
    have he := hf e (by simp)
    have hwe := hw e (by simp)
    have hse := hs e (by simp)
    have ho := ih (fun x hx => hf x (by simp [hx]))
      (fun x hx => hw x (by simp [hx])) (fun x hx => hs x (by simp [hx]))
    have hm := multiplyBits_cost template ht (f e).words (productList template J tail f).words J
      hwe (productList_bounded template J tail f ht)
    have hm' : (multiplyBits template (f e).words (productList template J tail f).words J).clock≤
        multiplyBudget template.length J := by
      apply hm.trans
      unfold multiplyBudget accessCost
      simp only [productList_size]
      gcongr
    change (f e).clock+_+_+J+3≤_
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- Increasing the LOCAL arity coarsens only its original 2^w traversal. -/
theorem localBudget_mono_arity (n R J W A E : ℕ) {u w : ℕ} (huw : u≤ w) :
    SemiprimeNativeLocalBits.localBudget n u R J W A E≤
      SemiprimeNativeLocalBits.localBudget n w R J W A E := by
  have hp := Nat.pow_le_pow_right (by decide : 0<2) huw
  unfold SemiprimeNativeLocalBits.localBudget SemiprimeNativeLocalBits.cacheControl
  gcongr

/-- Fixed polynomial group/control envelope apart from the original LOCAL 2^w.
The total incidence s is used only in the derived physical width. -/
def groupBudget (n F R J b s w A E : ℕ) : ℕ :=
  let W := groupWidth b R F s
  F*(SemiprimeNativeLocalBits.localBudget n w R J W A E+(3*J+1)+multiplyBudget W J+J+3)+
    (3*J+1)+groupControl n F J W

/-- Actual group outputs are physically width bounded without output advice. -/
theorem run_bounded {n F r : ℕ} {h : Fin r → ℕ} (b : ℕ) (arity : Fin F → ℕ) (J R : ℕ)
    (tw : RationalWord) (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (grouping : Fin n ≃ ((g : Fin r) × Fin (h g))) (assigned : Fin F → Fin r)
    (correction : Fin n → Bool) (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (g : Fin r) (a : (g : Fin r) → Fin (h g) → Bool) :
    Bounded (run b arity J R tw source grouping assigned correction entries g a).words
      (groupWidth b R F (∑ e,arity e)) := by
  let W := groupWidth b R F (∑ e,arity e)
  let template := List.replicate W false
  let bits := Array.ofFn (SemiprimeNativeGroupExecution.baseBits grouping a)
  let getBit := fun v : Fin n => bits[v.val]'(by simp [bits])
  let callback := fun e => if assigned e=g then SemiprimeNativeLocalBits.nativeLocal template (arity e) J R tw
    (source e) getBit correction (entries e) else oneBits J
  have ht : 0<template.length := by
    simp only [template,List.length_replicate]
    dsimp only [W,groupWidth]
    omega
  change Bounded (productList template J (List.ofFn (fun e : Fin F => e)) callback).words W
  simpa only [template,List.length_replicate] using
    productList_bounded template J (List.ofFn (fun e : Fin F => e)) callback ht

/-- Every invoked physical corrected-port/local/factor callback and suffix
multiplication is retained in the ACTUAL group report. -/
theorem run_clock {n F r : ℕ} {h : Fin r → ℕ} (b : ℕ) (arity : Fin F → ℕ)
    (J R w A E : ℕ) (tw : RationalWord)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (grouping : Fin n ≃ ((g : Fin r) × Fin (h g))) (assigned : Fin F → Fin r)
    (correction : Fin n → Bool) (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (g : Fin r) (a : (g : Fin r) → Fin (h g) → Bool)
    (harity : ∀ e,arity e≤ w)
    (htw : Width tw (groupWidth b R F (∑ e,arity e)))
    (hsource : ∀ e i v,Bounded (source e i v) (groupWidth b R F (∑ e,arity e)))
    (hsize : ∀ e i v,(source e i v).size≤ A)
    (hentry : ∀ e eta,(entries e eta).clock≤ E)
    (hentryWidth : ∀ e eta,(entries e eta).bits.magnitude.length≤ groupWidth b R F (∑ e,arity e)) :
    (run b arity J R tw source grouping assigned correction entries g a).clock≤
      groupBudget n F R J b (∑ e,arity e) w A E := by
  let s := ∑ e,arity e
  let W := groupWidth b R F s
  let template := List.replicate W false
  let bits := Array.ofFn (SemiprimeNativeGroupExecution.baseBits grouping a)
  let getBit := fun v : Fin n => bits[v.val]'(by simp [bits])
  let callback := fun e => if assigned e=g then SemiprimeNativeLocalBits.nativeLocal template (arity e) J R tw
    (source e) getBit correction (entries e) else oneBits J
  have ht : 0< template.length := by
    simp only [template,List.length_replicate]
    dsimp only [W,groupWidth]
    omega
  have hc (e : Fin F) : (callback e).clock≤ SemiprimeNativeLocalBits.localBudget n w R J W A E+(3*J+1) := by
    by_cases he : assigned e=g
    · have hl := SemiprimeNativeLocalBits.nativeLocal_clock template (arity e) J R A E tw
        (source e) getBit correction (entries e) ht
        (by simpa only [template,List.length_replicate] using htw)
        (by simpa only [template,List.length_replicate] using hsource e) (hsize e) (hentry e)
        (by simpa only [template,List.length_replicate] using hentryWidth e)
      simp only [template,List.length_replicate] at hl
      have hm := hl.trans (localBudget_mono_arity n R J W A E (harity e))
      simpa only [callback,ite_eq_left he] using hm.trans (Nat.le_add_right _ (3*J+1))
    · simp only [callback,ite_eq_right he,oneBits]
      omega
  have hw (e : Fin F) : Bounded (callback e).words template.length := by
    by_cases he : assigned e=g
    · simpa only [callback,ite_eq_left he] using
        SemiprimeNativeLocalBits.nativeLocal_bounded template (arity e) J R tw
          (source e) getBit correction (entries e)
    · simpa only [callback,ite_eq_right he,oneBits] using oneArray_bounded J _ ht
  have hs (e : Fin F) : (callback e).words.size≤ J := by
    by_cases he : assigned e=g
    · simp only [callback,ite_eq_left he,SemiprimeNativeLocalBits.nativeLocal_size,le_refl]
    · simp only [callback,ite_eq_right he,oneBits,oneArray_size,le_refl]
  have hp := productList_clock template J (SemiprimeNativeLocalBits.localBudget n w R J W A E+(3*J+1))
    (List.ofFn (fun e : Fin F => e)) callback ht (fun e _ => hc e) (fun e _ => hw e) (fun e _ => hs e)
  simp only [List.length_ofFn,template,List.length_replicate] at hp
  unfold run groupBudget
  dsimp only
  exact Nat.add_le_add_right hp _

/-- The scalar-boundary allowance itself is controlled by actual physical word
lengths; this does not identify that boundary with a primitive tape compiler. -/
theorem decodeWork_bound (words : Array RationalWord) (W : ℕ) (hw : Bounded words W) :
    decodeWork words≤ words.size*(20000*(2*W+1)^3+5)+2*words.size+1 := by
  have hword (word : RationalWord) (hmem : word∈words.toList) :
      20000*(word.numerator.magnitude.length+word.denominator.length+1)^3+5≤20000*(2*W+1)^3+5 := by
    obtain ⟨i,hi,he⟩ := Array.mem_iff_getElem.mp (show word∈words by simpa using hmem)
    have hh := hw i hi
    rw [he] at hh
    have hs : word.numerator.magnitude.length+word.denominator.length+1≤2*W+1 := by
      rcases hh with ⟨h₁,h₂⟩
      omega
    gcongr
  have hsum (xs : List RationalWord) (hsub : ∀ x∈xs,x∈words.toList) :
      (xs.map (fun word => 20000*(word.numerator.magnitude.length+word.denominator.length+1)^3+5)).sum≤
        xs.length*(20000*(2*W+1)^3+5) := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx := hword x (hsub x (by simp))
      have ht := ih (fun y hy => hsub y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith only [hx,ht]
  have hs := hsum words.toList (fun _ hx => hx)
  simp only [Array.length_toList] at hs
  unfold decodeWork
  omega

/-- Complete group plus retained rational-boundary envelope. -/
def scalarGroupBudget (n F R J b s w A E : ℕ) : ℕ :=
  groupBudget n F R J b s w A E+J*(20000*(2*groupWidth b R F s+1)^3+5)+2*J+1

/-- Moving the ACTUAL group result into the scalar traversal keeps its physical
clock and the full declared normalization/copy allowance. -/
theorem toScalarRun_clock {n F r : ℕ} {h : Fin r → ℕ} (b : ℕ) (arity : Fin F → ℕ)
    (J R w A E : ℕ) (tw : RationalWord)
    (source : (e : Fin F) → Fin (arity e) → Fin n → Array RationalWord)
    (grouping : Fin n ≃ ((g : Fin r) × Fin (h g))) (assigned : Fin F → Fin r)
    (correction : Fin n → Bool) (entries : (e : Fin F) → (Fin (arity e) → Bool) → EntryWord)
    (g : Fin r) (a : (g : Fin r) → Fin (h g) → Bool)
    (harity : ∀ e,arity e≤ w)
    (htw : Width tw (groupWidth b R F (∑ e,arity e)))
    (hsource : ∀ e i v,Bounded (source e i v) (groupWidth b R F (∑ e,arity e)))
    (hsize : ∀ e i v,(source e i v).size≤ A)
    (hentry : ∀ e eta,(entries e eta).clock≤ E)
    (hentryWidth : ∀ e eta,(entries e eta).bits.magnitude.length≤ groupWidth b R F (∑ e,arity e)) :
    (toScalarRun (run b arity J R tw source grouping assigned correction entries g a)).work≤
      scalarGroupBudget n F R J b (∑ e,arity e) w A E := by
  have hr := run_clock b arity J R w A E tw source grouping assigned correction entries g a
    harity htw hsource hsize hentry hentryWidth
  have hd := decodeWork_bound _ _ (run_bounded b arity J R tw source grouping assigned correction entries g a)
  rw [run_size] at hd
  rw [toScalarRun_work]
  unfold scalarGroupBudget
  omega

end RiemannGaussian.SemiprimeNativeGroupBitsBudget
