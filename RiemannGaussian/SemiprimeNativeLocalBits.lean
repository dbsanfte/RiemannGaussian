/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeCorrectedPortBitsBounds
import RiemannGaussian.SemiprimeLocalBitsBounds

/-! # Physical corrected ports joined to the actual local Boolean tree
The runtime acquires each corrected port once, caches its report, and calls the
physical local evaluator. Source-word acquisition remains an explicit boundary.
All arithmetic fits are derived from original common source representations.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace RiemannGaussian.SemiprimeNativeLocalBits
open scoped BigOperators
open SemiprimeRationalBits SemiprimeJetBits SemiprimeJetArray SemiprimeJetArrayHeight
open SemiprimeLocalExecutionHeight SemiprimeLocalBits SemiprimeLocalBitsBounds
open SemiprimeLocalArrayFrontend

/-- Derived binary exponent for every acquired corrected-port coefficient. -/
def portExponent (b R : ℕ) : ℕ := 2*b+(2*b+2)*(R+1)

/-- One polynomial original-parameter width accommodates physical acquisition
and the entire multilinear tree. It is not supplied intermediate fit advice. -/
def publicWidth (b R w : ℕ) : ℕ :=
  SemiprimeCorrectedPortBits.portWidth b R+bufferWidth (portExponent b R) w+b+1

/-- The constructed physical width is positive for every original parameter. -/
theorem publicWidth_pos (b R w : ℕ) : 0<publicWidth b R w := by
  unfold publicWidth
  omega

/-- Larger actual arity only enlarges the polynomial width, not the runtime
arity of any local Boolean traversal. -/
theorem publicWidth_mono_arity (b R : ℕ) : Monotone (publicWidth b R) := by
  intro w W h
  unfold publicWidth bufferWidth
  gcongr

/-- Finite report-cache allocation, outer port access and local control allowance.
Literal address/tape compilation is separate from this selected control ledger. -/
def cacheControl (w J W : ℕ) : ℕ := 20*(w+1)*(J+1)*(W+1)*(2^w+1)+10*w+10

/-- Physical local execution: one cached acquired report per original port,
followed by the actual two-branch Boolean multilinear word evaluator. -/
def nativeLocal {n : ℕ} (template : List Bool) (w J R : ℕ) (tw : RationalWord)
    (source : Fin w → Fin n → Array RationalWord) (base correction : Fin n → Bool)
    (T : (Fin w → Bool) → EntryWord) : JetReport :=
  let inputs := Array.ofFn (fun v : Fin w => SemiprimeCorrectedPortBits.acquireCorrectedFin
    template (source v) tw R J base correction)
  let out := localEvaluateBits template J w T
    (fun v => (inputs[v.val]'(by simp [inputs])).words)
  ⟨out.words,(∑ v : Fin w, (inputs[v.val]'(by simp [inputs])).clock)+out.clock+
    cacheControl w J template.length⟩

/-- The public variant constructs its width template from original parameter bits. -/
def run {n : ℕ} (b w J R : ℕ) (tw : RationalWord)
    (source : Fin w → Fin n → Array RationalWord) (base correction : Fin n → Bool)
    (T : (Fin w → Bool) → EntryWord) : JetReport :=
  nativeLocal (List.replicate (publicWidth b R w) false) w J R tw source base correction T

/-- Exact acquired words always have the requested local output length. -/
theorem nativeLocal_size {n : ℕ} (template : List Bool) (w J R : ℕ) (tw : RationalWord)
    (source : Fin w → Fin n → Array RationalWord) (base correction : Fin n → Bool)
    (T : (Fin w → Bool) → EntryWord) :
    (nativeLocal template w J R tw source base correction T).words.size=J := by
  simp only [nativeLocal,localEvaluateBits_size]

/-- The original rational local tree also retains exactly its requested length. -/
theorem localEvaluate_size (J w : ℕ)
    (T : (Fin w → Bool) → SemiprimeLocalArrayFrontend.EntryReport)
    (inputs : Fin w → Array ℚ) :
    (SemiprimeLocalArrayFrontend.localEvaluate J w T inputs).coefficients.size=J := by
  cases w <;> simp only [SemiprimeLocalArrayFrontend.localEvaluate,
    SemiprimeArrayOps.scaleJet,SemiprimeArrayOps.addJet,Array.size_ofFn]

/-- Original dyadic source/node bounds control the full corrected-port numerator. -/
theorem port_numerator_le (b R J B T n : ℕ)
    (hJ : J ≤ 2^b) (hB : B ≤ 2^b) (hT : T ≤ 2^b) (hn : n ≤ 2^b) :
    n*hornerBound J B T (R+1) ≤ 2^(portExponent b R) := by
  have hh := SemiprimeLocalExecutionBitBounds.hornerBound_le J B T b (R+1) hJ hB hT
  have hm := Nat.mul_le_mul hn hh
  convert hm using 1
  rw [← pow_add]
  unfold portExponent
  congr 1
  omega

/-- Derived public-width correctness of the ACTUAL physical local call, with
exact decoded arrays and a shared denominator bound for subsequent group folds. -/
theorem nativeLocal_correct {n : ℕ} (template : List Bool) (b w R J d B T : ℕ)
    (source : Fin w → Fin n → Array RationalWord) (tw : RationalWord) (t : ℤ)
    (base correction : Fin n → Bool) (entries : (Fin w → Bool) → EntryWord)
    (hwidth : publicWidth b R w ≤ template.length)
    (hvalid : ∀ v u, Valid (source v u)) (htw : tw.Valid) (htval : tw.value=(t:ℚ))
    (hd : 0<d) (ht : t.natAbs ≤ T)
    (hdb : d ≤ 2^b) (hBb : B ≤ 2^b) (hTb : T ≤ 2^b) (hJb : J ≤ 2^b) (hnb : n ≤ 2^b)
    (hsource : ∀ v u i, i ≤ R → Representation (coefficient (decode (source v u)) i) d B)
    (hentries : ∀ eta, (entries eta).bits.value.natAbs ≤ 1) :
    decode (nativeLocal template w J R tw source base correction entries).words=
      (SemiprimeLocalArrayFrontend.nativeLocal w J R (t:ℚ)
        (fun v u => decode (source v u)) base correction (table entries)).coefficients ∧
    Valid (nativeLocal template w J R tw source base correction entries).words ∧
    ArrayBound (decode (nativeLocal template w J R tw source base correction entries).words)
      J (d^w) ((localBase J d (n*hornerBound J B T (R+1)))^w) := by
  let inputs := fun v : Fin w => SemiprimeCorrectedPortBits.acquireCorrectedFin
    template (source v) tw R J base correction
  have hp (v : Fin w) : decode (inputs v).words=
      (SemiprimeLocalArrayFrontend.acquireCorrectedFin (fun u => decode (source v u)) (t:ℚ)
        R J base correction).coefficients ∧ Valid (inputs v).words := by
    have hn := SemiprimeCorrectedPortBits.port_numeric_bounds b R J d B T n hdb hBb hTb hJb hnb
    have hw : SemiprimeCorrectedPortBits.portWidth b R ≤ template.length := by
      unfold publicWidth at hwidth
      omega
    have he := Nat.pow_le_pow_right (by decide : 0<2) hw
    exact SemiprimeCorrectedPortBits.acquireCorrectedFin_correct template (source v) tw t R J d B T
      base correction (hvalid v) htw htval hd ht (hn.1.trans_le he) (hn.2.1.trans_le he)
      (hn.2.2.trans_le he) (hsource v)
  have hinput (v : Fin w) : ArrayBound (decode (inputs v).words) J d
      (n*hornerBound J B T (R+1)) := by
    rw [(hp v).1]
    exact SemiprimeLocalExecutionHeight.acquireCorrectedFin_bound
      (fun u => decode (source v u)) t R J d B T base correction ht (hsource v)
  have hbp : b ≤ portExponent b R := by unfold portExponent; omega
  have hpow := Nat.pow_le_pow_right (by decide : 0<2) hbp
  have hlocal := local_correct_at_public_width template J d (n*hornerBound J B T (R+1))
    (portExponent b R) w (by unfold publicWidth at hwidth; omega) hd
    (hJb.trans hpow) (hdb.trans hpow) (port_numerator_le b R J B T n hJb hBb hTb hnb)
    entries (fun v => (inputs v).words) hentries hinput (fun v => (hp v).2)
  have heq : decode (localEvaluateBits template J w entries (fun v => (inputs v).words)).words=
      (SemiprimeLocalArrayFrontend.localEvaluate J w (table entries)
        (fun v => decode (inputs v).words)).coefficients := by
    apply SemiprimeCorrectedPortBits.array_eq_of_coeff J
    · simp only [decode_size,localEvaluateBits_size]
    · exact localEvaluate_size J w _ _
    · exact hlocal.1
  have hin : (fun v => decode (inputs v).words)=
      (fun v => (SemiprimeLocalArrayFrontend.acquireCorrectedFin
        (fun u => decode (source v u)) (t:ℚ) R J base correction).coefficients) :=
    funext (fun v => (hp v).1)
  refine ⟨?_,?_,?_⟩
  · simpa only [nativeLocal,SemiprimeLocalArrayFrontend.nativeLocal,Array.getElem_ofFn,hin] using heq
  · simpa only [nativeLocal,Array.getElem_ofFn,inputs] using hlocal.2.1
  · simpa only [nativeLocal,Array.getElem_ofFn,inputs] using hlocal.2.2

/-- Structural fitting bounds every retained physical local output word. -/
theorem nativeLocal_bounded {n : ℕ} (template : List Bool) (w J R : ℕ) (tw : RationalWord)
    (source : Fin w → Fin n → Array RationalWord) (base correction : Fin n → Bool)
    (T : (Fin w → Bool) → EntryWord) :
    Bounded (nativeLocal template w J R tw source base correction T).words template.length := by
  exact localEvaluateBits_bounded template J w T _

/-- Exact retained clock of the physical port-acquisition/cache/tree composition. -/
theorem nativeLocal_clock_eq {n : ℕ} (template : List Bool) (w J R : ℕ) (tw : RationalWord)
    (source : Fin w → Fin n → Array RationalWord) (base correction : Fin n → Bool)
    (entries : (Fin w → Bool) → EntryWord) :
    (nativeLocal template w J R tw source base correction entries).clock=
      (∑ v : Fin w, (SemiprimeCorrectedPortBits.acquireCorrectedFin
        template (source v) tw R J base correction).clock)+
      (localEvaluateBits template J w entries (fun v =>
        (SemiprimeCorrectedPortBits.acquireCorrectedFin
          template (source v) tw R J base correction).words)).clock+
      cacheControl w J template.length := by
  simp only [nativeLocal,Array.getElem_ofFn]

/-- Explicit native-local physical arithmetic/control budget. The only
exponential is the actual local arity, never total network incidence. -/
def localBudget (n w R J W A E : ℕ) : ℕ :=
  w*SemiprimeCorrectedPortBitsBounds.portBudget W A R J n+
    2^w*(E+(w+1)*nodeBudget J W)+cacheControl w J W

/-- All corrected-port reports and every actual original table call are paid.
Input widths and sizes concern the original encoded cache, not computed Fits. -/
theorem nativeLocal_clock {n : ℕ} (template : List Bool) (w J R A E : ℕ) (tw : RationalWord)
    (source : Fin w → Fin n → Array RationalWord) (base correction : Fin n → Bool)
    (entries : (Fin w → Bool) → EntryWord) (ht : 0<template.length)
    (htw : Width tw template.length)
    (ha : ∀ v u,Bounded (source v u) template.length)
    (hsize : ∀ v u,(source v u).size ≤ A)
    (hentries : ∀ eta,(entries eta).clock ≤ E)
    (hentryWidth : ∀ eta,(entries eta).bits.magnitude.length ≤ template.length) :
    (nativeLocal template w J R tw source base correction entries).clock ≤
      localBudget n w R J template.length A E := by
  have hp := Finset.sum_le_sum (s:=Finset.univ) (fun (v : Fin w) _ =>
    SemiprimeCorrectedPortBitsBounds.acquireCorrectedFin_clock template (source v) tw R J A
      base correction ht htw (ha v) (hsize v))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hp
  have hl := local_clock template J w E ht entries
    (fun v => (SemiprimeCorrectedPortBits.acquireCorrectedFin
      template (source v) tw R J base correction).words) hentries hentryWidth
    (fun v => SemiprimeCorrectedPortBitsBounds.acquireCorrectedFin_bounded
      template (source v) tw R J base correction ht)
    (fun _ => (SemiprimeCorrectedPortBitsBounds.acquireCorrectedFin_size _ _ _ _ _ _ _).le)
  rw [nativeLocal_clock_eq]
  exact Nat.add_le_add_right (Nat.add_le_add hp hl) _

/-- The initialized public local executor is exactly the old rational frontend. -/
theorem run_correct {n : ℕ} (b w R J d B T : ℕ)
    (source : Fin w → Fin n → Array RationalWord) (tw : RationalWord) (t : ℤ)
    (base correction : Fin n → Bool) (entries : (Fin w → Bool) → EntryWord)
    (hvalid : ∀ v u, Valid (source v u)) (htw : tw.Valid) (htval : tw.value=(t:ℚ))
    (hd : 0<d) (ht : t.natAbs ≤ T)
    (hdb : d ≤ 2^b) (hBb : B ≤ 2^b) (hTb : T ≤ 2^b) (hJb : J ≤ 2^b) (hnb : n ≤ 2^b)
    (hsource : ∀ v u i, i ≤ R → Representation (coefficient (decode (source v u)) i) d B)
    (hentries : ∀ eta, (entries eta).bits.value.natAbs ≤ 1) :
    decode (run b w J R tw source base correction entries).words=
      (SemiprimeLocalArrayFrontend.nativeLocal w J R (t:ℚ)
        (fun v u => decode (source v u)) base correction (table entries)).coefficients ∧
    Valid (run b w J R tw source base correction entries).words ∧
    ArrayBound (decode (run b w J R tw source base correction entries).words)
      J (d^w) ((localBase J d (n*hornerBound J B T (R+1)))^w) := by
  exact nativeLocal_correct _ b w R J d B T source tw t base correction entries
    (by simp only [List.length_replicate]; exact le_rfl) hvalid htw htval hd ht hdb hBb hTb hJb hnb hsource hentries

end RiemannGaussian.SemiprimeNativeLocalBits
