/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeLocalBits

/-! # Constructor-derived correctness of the physical local interpreter -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace RiemannGaussian.SemiprimeLocalBitsCorrectness
open scoped BigOperators
open SemiprimeLocalBits SemiprimeJetBits SemiprimeRationalBits SemiprimeJetArray
open SemiprimeJetArrayHeight SemiprimeLocalArrayFrontend SemiprimeLocalExecutionHeight SemiprimeHermiteArrayHeight

/-- Retained equality transfers a proved common representation. -/
theorem bound_transfer (J d B : ℕ) {a b : Array ℚ}
    (h : EqualBelow J a b) (hb : ArrayBound b J d B) : ArrayBound a J d B := by
  intro i hi
  rw [h i hi]
  exact hb i hi

/-- Literal one coefficients admit every positive common denominator. -/
theorem one_bound (J d : ℕ) (hd : 0<d) : ArrayBound (decode (oneArray J)) J d d := by
  apply bound_transfer J d d (oneArray_coefficient J)
  exact oneJet_representation J d hd

/-- Port negation and one-minus-port budgets occur explicitly in the cap. -/
theorem cap_small (J d B w : ℕ) :
    d<cap J d B w ∧ B<cap J d B w ∧ d+B<cap J d B w ∧ 1<cap J d B w := by
  unfold cap
  omega

/-- Actual child-product denominator is bounded independently of cancellation. -/
theorem cap_den (J d B w : ℕ) : d*d^w<cap J d B (w+1) := by
  have h := Nat.pow_le_pow_left (Nat.le_succ d) (w+1)
  rw [pow_succ'] at h
  simp only [Nat.succ_eq_add_one] at h
  unfold cap
  omega

/-- Both convolution outputs together fit the derived coefficient cap. -/
theorem cap_num (J d B w : ℕ) :
    2*(J*(d+B)*localBase J d B^w)<cap J d B (w+1) := by
  have he : 2*(J*(d+B)*localBase J d B^w)=localBase J d B^(w+1) := by
    rw [pow_succ]
    unfold localBase
    ring
  rw [he]
  have h := Nat.pow_le_pow_left (Nat.le_succ (localBase J d B)) (w+1)
  simp only [Nat.succ_eq_add_one] at h
  unfold cap
  omega

/-- The executed evaluator refines the frozen rational arrays and derives its
output representation from initial ports and the actual bounded integer table.
No desired branch-output Fits proposition is an input. -/
theorem local_correct (template : List Bool) (J d B : ℕ) (hd : 0<d) :
    ∀ (w : ℕ) (T : (Fin w → Bool) → EntryWord) (inputs : Fin w → Array RationalWord),
    cap J d B w < 2^template.length →
    (∀ eta, (T eta).bits.value.natAbs≤1) →
    (∀ v, ArrayBound (decode (inputs v)) J d B) →
    (∀ v, Valid (inputs v)) →
    EqualBelow J (decode (localEvaluateBits template J w T inputs).words)
      (localEvaluate J w (table T) (fun v => decode (inputs v))).coefficients ∧
    Valid (localEvaluateBits template J w T inputs).words ∧
    ArrayBound (decode (localEvaluateBits template J w T inputs).words)
      J (d^w) (localBase J d B^w) := by
  intro w
  induction w with
  | zero =>
    intro T inputs hcap hT hinputs hvalid
    let e := T Fin.elim0
    have he : Representation e.rational.value 1 1 := by
      rw [entry_value]
      exact representation_mono (representation_integer e.bits.value) (hT Fin.elim0)
    have hc := scaleBits_correct template (oneArray J) e.rational J 1 1 1 1
      (oneArray_valid J) (entry_valid e) (by decide) (by decide)
      (by have h := (cap_small J d B 0).2.2.2; simpa using h.trans hcap)
      (by have h := (cap_small J d B 0).2.2.2; simpa using h.trans hcap)
      (one_bound J 1 (by decide)) he
    have heq : EqualBelow J (decode (localEvaluateBits template J 0 T inputs).words)
        (localEvaluate J 0 (table T) (fun v => decode (inputs v))).coefficients := by
      intro i hi
      have h := hc.1 i hi
      rw [SemiprimeArrayOps.scaleJet_coefficient _ _ J i hi] at h
      change _ = coefficient (SemiprimeArrayOps.scaleJet (SemiprimeArrayOps.oneJet J).coefficients
        ((T Fin.elim0).bits.value : ℚ) J).coefficients i
      rw [SemiprimeArrayOps.scaleJet_coefficient _ _ J i hi]
      simpa only [e,localEvaluateBits,entry_value,oneArray_coefficient J i hi] using h
    refine ⟨heq,hc.2,?_⟩
    exact bound_transfer J _ _ heq (localEvaluate_representation J 0 d B hd (table T)
      (fun v => decode (inputs v)) hT hinputs)
  | succ w ih =>
    intro T inputs hcap hT hinputs hvalid
    let l := localEvaluateBits template J w (fun eta => T (Fin.cons false eta)) (fun i => inputs i.succ)
    let h := localEvaluateBits template J w (fun eta => T (Fin.cons true eta)) (fun i => inputs i.succ)
    have hchild := (cap_mono J d B (Nat.le_succ w)).trans_lt hcap
    have hl := ih _ _ hchild (fun eta => hT (Fin.cons false eta))
      (fun i => hinputs i.succ) (fun i => hvalid i.succ)
    have hh := ih _ _ hchild (fun eta => hT (Fin.cons true eta))
      (fun i => hinputs i.succ) (fun i => hvalid i.succ)
    have hdsmall := (cap_small J d B (w+1)).1.trans hcap
    have hbsmall := (cap_small J d B (w+1)).2.1.trans hcap
    have hnsmall := (cap_small J d B (w+1)).2.2.1.trans hcap
    have hdprod := (cap_den J d B w).trans hcap
    have hnum := (cap_num J d B w).trans hcap
    let neg := scaleBits template (inputs 0) negOneWord J
    have hneg := scaleBits_correct template (inputs 0) negOneWord J d 1 B 1
      (hvalid 0) negOneWord_valid hd (by decide) (by simpa using hdsmall) (by simpa using hbsmall)
      (hinputs 0) (by simpa using (representation_neg (representation_one 1 (by decide))))
    have eneg : EqualBelow J (decode neg.words)
        (SemiprimeArrayOps.scaleJet (decode (inputs 0)) (-1) J).coefficients := by
      simpa only [neg,EqualBelow,negOneWord_value] using hneg.1
    have rn : ArrayBound (decode neg.words) J d B := by
      intro i hi
      rw [eneg i hi,SemiprimeArrayOps.scaleJet_coefficient _ _ J i hi,neg_one_mul]
      exact representation_neg (hinputs 0 i hi)
    let no := addBits template (oneArray J) neg.words J
    have hno := addBits_correct template (oneArray J) neg.words J d d B
      (oneArray_valid J) hneg.2 hd hdsmall hnsmall (one_bound J d hd) rn
    have eno := fun i hi => (hno.1 i hi).trans
      (add_congr J (oneArray_coefficient J) eneg i hi)
    have rno : ArrayBound (decode no.words) J d (d+B) :=
      bound_transfer J _ _ hno.1 (SemiprimeArrayOps.addJet_representation _ _ J d d B (one_bound J d hd) rn)
    let left := multiplyBits template no.words l.words J
    have hleft := multiplyBits_correct template no.words l.words J d (d^w) (d+B) (localBase J d B^w)
      hno.2 hl.2.1 hd (pow_pos hd _) hdprod (by omega) rno hl.2.2
    have eleft := fun i hi => (hleft.1 i hi).trans (multiply_congr J eno hl.1 i hi)
    have rleft : ArrayBound (decode left.words) J (d*d^w) (J*(d+B)*localBase J d B^w) :=
      bound_transfer J _ _ hleft.1 (multiply_representation _ _ _ _ _ _ J rno hl.2.2)
    let right := multiplyBits template (inputs 0) h.words J
    have hrnum : J*B*localBase J d B^w ≤ J*(d+B)*localBase J d B^w := by gcongr; omega
    have hright := multiplyBits_correct template (inputs 0) h.words J d (d^w) B (localBase J d B^w)
      (hvalid 0) hh.2.1 hd (pow_pos hd _) hdprod (by omega) (hinputs 0) hh.2.2
    have eright := fun i hi => (hright.1 i hi).trans (multiply_congr J (fun _ _ => rfl) hh.1 i hi)
    have rright : ArrayBound (decode right.words) J (d*d^w) (J*B*localBase J d B^w) :=
      bound_transfer J _ _ hright.1 (multiply_representation _ _ _ _ _ _ J (hinputs 0) hh.2.2)
    let out := addBits template left.words right.words J
    have hout := addBits_correct template left.words right.words J (d*d^w)
      (J*(d+B)*localBase J d B^w) (J*B*localBase J d B^w)
      hleft.2 hright.2 (Nat.mul_pos hd (pow_pos hd _)) hdprod (by omega) rleft rright
    have heq : EqualBelow J (decode (localEvaluateBits template J (w+1) T inputs).words)
        (localEvaluate J (w+1) (table T) (fun v => decode (inputs v))).coefficients := by
      intro i hi
      exact (hout.1 i hi).trans (add_congr J eleft eright i hi)
    refine ⟨heq,hout.2,?_⟩
    exact bound_transfer J _ _ heq (localEvaluate_representation J (w+1) d B hd (table T)
      (fun v => decode (inputs v)) hT hinputs)
end RiemannGaussian.SemiprimeLocalBitsCorrectness
