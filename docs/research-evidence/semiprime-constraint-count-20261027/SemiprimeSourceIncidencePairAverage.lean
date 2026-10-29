/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHeadCountFormula

/-! # Conditional whole-word equality averages without completion enumeration -/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceIncidencePairAverage
open OAI.Algorithms.SubexponentialSAT
open ConditionalExpectation LocalExpectation MulticolorTypes
open SemiprimeSourceHeadCountFormula

/-- Conditional equality probability: a loop is certain; a genuinely free
nonloop costs one uniform word; anchored endpoints are actually compared. -/
def pairPotential {W : Type*} [DecidableEq W] (L : ℕ) (remaining : List ℕ)
    (ω : ℕ → W) (a c : ℕ) : ℚ :=
  if a=c then 1 else if a∈remaining ∨ c∈remaining then 1/(L:ℚ)
  else if ω a=ω c then 1 else 0

/-- Averaging a fixed scalar multiple is exact on the supplied finite list. -/
theorem mean_mul_right {W : Type*} (alphabet : List W) (f : W → ℚ) (v : ℚ) :
    mean alphabet (fun w => f w*v)=mean alphabet f*v := by
  have hs : (alphabet.map (fun w => f w*v)).sum=(alphabet.map f).sum*v := by
    induction alphabet with
    | nil => simp
    | cons a as ih => simp only [List.map_cons,List.sum_cons,ih];ring
  simp only [mean,hs];ring

/-- Symmetric scalar extraction, including the empty-list convention. -/
theorem mean_mul_left {W : Type*} (alphabet : List W) (f : W → ℚ) (v : ℚ) :
    mean alphabet (fun w => v*f w)=v*mean alphabet f := by
  simpa only [mul_comm v] using mean_mul_right alphabet f v

/-- The actual complete canonical menu assigns probability exactly 1/L to
one specified whole word; no random or field-order assumption is used. -/
theorem mean_delta (r Q : ℕ) (w : Word r Q) :
    mean (alphabet r Q) (fun z => if z=w then 1 else 0)=1/(r^Q:ℕ) := by
  classical
  have hs : ((alphabet r Q).map (fun z => if z=w then (1:ℚ) else 0)).sum=1 := by
    have hu : (alphabet r Q).toFinset=Finset.univ := by
      ext z
      simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
      exact (SemiprimeFiniteEnumerations.words r Q).complete z
    have hn : (alphabet r Q).Nodup := (SemiprimeFiniteEnumerations.words r Q).nodup
    rw [← List.sum_toFinset _ hn,hu]
    simp
  simp only [mean,hs,alphabet_length]

/-- Updating a key outside an edge cannot change its conditional potential. -/
theorem pair_update_other {W : Type*} [DecidableEq W] (L : ℕ) (remaining : List ℕ)
    (ω : ℕ → W) (a c i : ℕ) (w : W) (hia : i≠a) (hic : i≠c) :
    pairPotential L remaining (Function.update ω i w) a c=
      pairPotential L remaining ω a c := by
  simp only [pairPotential,Function.update_of_ne (Ne.symm hia),
    Function.update_of_ne (Ne.symm hic)]

/-- One exact elimination step, valid for every current anchored environment. -/
theorem pair_mean_step (r Q : ℕ) (hr : 0<r) (remaining : List ℕ)
    (ω : ℕ → Word r Q) (a c i : ℕ) (hi : i∉remaining) :
    mean (alphabet r Q) (fun w => pairPotential (r^Q) remaining
      (Function.update ω i w) a c)=pairPotential (r^Q) (i::remaining) ω a c := by
  classical
  have hne : alphabet r Q≠[] := by
    have hl : 0<(alphabet r Q).length := by rw [alphabet_length];exact pow_pos hr Q
    exact List.ne_nil_of_length_pos hl
  by_cases hac : a=c
  · subst c
    simpa only [pairPotential,ite_eq_left_iff,ite_true] using mean_const (alphabet r Q) hne (1:ℚ)
  by_cases hia : i=a
  · subst i
    by_cases hc : c∈remaining
    · simp only [pairPotential,hac,ite_false,List.mem_cons_self,true_or,ite_true,hc,or_true]
      exact mean_const _ hne _
    · simp only [pairPotential,hac,ite_false,hi,hc,false_or,List.mem_cons_self,true_or,
        ite_true,Function.update_same,Function.update_of_ne (Ne.symm hac)]
      exact mean_delta r Q (ω c)
  by_cases hic : i=c
  · subst i
    by_cases ha : a∈remaining
    · simp only [pairPotential,hac,ite_false,List.mem_cons_self,or_true,ite_true,ha,true_or]
      exact mean_const _ hne _
    · simp only [pairPotential,hac,ite_false,hi,ha,false_or,List.mem_cons_self,or_true,
        ite_true,Function.update_same,Function.update_of_ne hac]
      simpa only [eq_comm] using mean_delta r Q (ω a)
  · simp_rw [pair_update_other (r^Q) remaining ω a c i _ hia hic]
    rw [mean_const _ hne]
    simp only [pairPotential,List.mem_cons,Ne.symm hia,Ne.symm hic,false_or]

/-- At an empty remaining list the potential is the literal equality test. -/
theorem pair_nil {W : Type*} [DecidableEq W] (L : ℕ) (ω : ℕ → W) (a c : ℕ) :
    pairPotential L [] ω a c=(if ω a=ω c then 1 else 0) := by
  by_cases h : a=c
  · subst c;simp [pairPotential]
  · simp [pairPotential,h]

/-- Exact conditional average of one whole-word equality for every prefix. -/
theorem pair_average (r Q : ℕ) (hr : 0<r) (remaining : List ℕ)
    (hn : remaining.Nodup) (ω : ℕ → Word r Q) (a c : ℕ) :
    wordExpectation (alphabet r Q) (fun v => if v a=v c then 1 else 0)
      remaining ω=pairPotential (r^Q) remaining ω a c := by
  induction remaining generalizing ω with
  | nil => simp only [wordExpectation,pair_nil]
  | cons i rest ih =>
    simp only [wordExpectation]
    have hmap : (fun w => wordExpectation (alphabet r Q)
        (fun v => if v a=v c then 1 else 0) rest (Function.update ω i w))=
        (fun w => pairPotential (r^Q) rest (Function.update ω i w) a c) := by
      funext w
      exact ih hn.of_cons _
    rw [hmap]
    exact pair_mean_step r Q hr rest ω a c i (List.nodup_cons.mp hn).1

/-- Disjoint equality pairs remain independent after an arbitrary ordered
prefix, including all aliases within either pair. -/
theorem separated_average (r Q : ℕ) (hr : 0<r) (remaining : List ℕ)
    (hn : remaining.Nodup) (ω : ℕ → Word r Q) (a b c d : ℕ)
    (hab : a≠b) (had : a≠d) (hcb : c≠b) (hcd : c≠d) :
    wordExpectation (alphabet r Q)
      (fun v => (if v a=v c then 1 else 0)*(if v b=v d then 1 else 0))
      remaining ω=pairPotential (r^Q) remaining ω a c*
        pairPotential (r^Q) remaining ω b d := by
  induction remaining generalizing ω with
  | nil => simp only [wordExpectation,pair_nil]
  | cons i rest ih =>
    simp only [wordExpectation]
    have hmap : (fun w => wordExpectation (alphabet r Q)
        (fun v => (if v a=v c then 1 else 0)*(if v b=v d then 1 else 0))
        rest (Function.update ω i w))=
      (fun w => pairPotential (r^Q) rest (Function.update ω i w) a c*
        pairPotential (r^Q) rest (Function.update ω i w) b d) := by
      funext w
      exact ih hn.of_cons _
    rw [hmap]
    by_cases hia : i=a ∨ i=c
    · have hib : i≠b := by rcases hia with h|h <;> subst i <;> assumption
      have hid : i≠d := by rcases hia with h|h <;> subst i <;> assumption
      simp_rw [pair_update_other (r^Q) rest ω b d i _ hib hid]
      rw [mean_mul_right,pair_mean_step r Q hr rest ω a c i (List.nodup_cons.mp hn).1]
      congr 1
      simp only [pairPotential,List.mem_cons,Ne.symm hib,Ne.symm hid,false_or]
    · have hia' : i≠a := fun h => hia (Or.inl h)
      have hic : i≠c := fun h => hia (Or.inr h)
      simp_rw [pair_update_other (r^Q) rest ω a c i _ hia' hic]
      rw [mean_mul_left,pair_mean_step r Q hr rest ω b d i (List.nodup_cons.mp hn).1]
      congr 1
      simp only [pairPotential,List.mem_cons,Ne.symm hia',Ne.symm hic,false_or]

end RiemannGaussian.SemiprimeSourceIncidencePairAverage
