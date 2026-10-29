/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.SemiprimeSourceHeadFibres
import RiemannGaussian.SemiprimeSourceScoreCountsPadding
import RiemannGaussian.SemiprimeFiniteEnumerations

/-! # Exact original padded head counts for every environment and prefix
The final theorem simplifies the original ordered recursive evaluator, not an
assumed uniform oracle. Arbitrary typed defaults/fixed words/overrides are allowed.
-/
set_option autoImplicit false
namespace RiemannGaussian.SemiprimeSourceHeadCountFormula
open scoped BigOperators
open RiemannGaussian
open OAI.Algorithms.SubexponentialSAT.MulticolorTypes
open SemiprimeMaterializedWords SemiprimeMaterializedScoreEnvironment
open SemiprimeSourceScoreCounts

/-- The actual canonical complete source-word menu, with its published order. -/
def alphabet (r Q : ℕ) := (SemiprimeFiniteEnumerations.words r Q).values

theorem alphabet_length (r Q : ℕ) : (alphabet r Q).length=r^Q := by
  exact SemiprimeFiniteEnumerations.words_length r Q

theorem alphabet_sum (r Q : ℕ) (f : Word r Q → ℕ) :
    ((alphabet r Q).map f).sum=∑w,f w := by
  classical
  have hu : (alphabet r Q).toFinset=Finset.univ := by
    ext w
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact (SemiprimeFiniteEnumerations.words r Q).complete w
  have hn : (alphabet r Q).Nodup := (SemiprimeFiniteEnumerations.words r Q).nodup
  rw [← List.sum_toFinset f hn,hu]

theorem fibre_sum (r Q : ℕ) (q : Fin Q) (c : Fin r) :
    ((alphabet r Q).map (fun w => if w q=c then 1 else 0)).sum=r^(Q-1) := by
  classical
  rw [alphabet_sum]
  rw [Finset.sum_boole]
  rw [← Fintype.card_subtype]
  exact SemiprimeSourceHeadFibres.fibre_card r Q q c

theorem sum_constant (r Q c : ℕ) :
    ((alphabet r Q).map (fun _ => c)).sum=r^Q*c := by
  simp [alphabet_length, List.sum_replicate, List.map_const']

theorem sum_mul {r Q : ℕ} (xs : List (Word r Q)) (f : Word r Q→ℕ) (c : ℕ) :
    (xs.map (fun w => f w*c)).sum=(xs.map f).sum*c := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,add_mul]


theorem empty_head (r Q : ℕ) (q : Fin Q) (a b : ℕ) (env : Environment r Q) :
    (count (alphabet r Q) (.head q a b) [] env).value=
      if denote env a q=denote env b q then 1 else 0 := by
  simp only [count,hit,decide_eq_true_eq]
  rfl

theorem singleton_left (r Q : ℕ) (q : Fin Q) (a b : ℕ) (hab : a≠b)
    (env : Environment r Q) :
    (count (alphabet r Q) (.head q a b) [a] env).value=r^(Q-1) := by
  rw [count,sumCount_value]
  simp only [empty_head]
  change ((alphabet r Q).map (fun w =>
    if denote (extend env a w) a q=denote (extend env a w) b q then 1 else 0)).sum=_
  simp only [denote_extend,Function.update_same,Function.update_noteq (Ne.symm hab)]
  exact fibre_sum r Q q (denote env b q)

theorem singleton_right (r Q : ℕ) (q : Fin Q) (a b : ℕ) (hab : a≠b)
    (env : Environment r Q) :
    (count (alphabet r Q) (.head q a b) [b] env).value=r^(Q-1) := by
  rw [count,sumCount_value]
  simp only [empty_head]
  change ((alphabet r Q).map (fun w =>
    if denote (extend env b w) a q=denote (extend env b w) b q then 1 else 0)).sum=_
  simp only [denote_extend,Function.update_same,Function.update_noteq hab]
  simpa only [eq_comm] using fibre_sum r Q q (denote env a q)

theorem pair_left (r Q : ℕ) (q : Fin Q) (a b : ℕ) (hab : a≠b)
    (env : Environment r Q) :
    (count (alphabet r Q) (.head q a b) [a,b] env).value=r^Q*r^(Q-1) := by
  rw [count,sumCount_value]
  change ((alphabet r Q).map (fun w =>
    (count (alphabet r Q) (.head q a b) [b] (extend env a w)).value)).sum=_
  simp_rw [singleton_right r Q q a b hab]
  exact sum_constant r Q (r^(Q-1))

theorem pair_right (r Q : ℕ) (q : Fin Q) (a b : ℕ) (hab : a≠b)
    (env : Environment r Q) :
    (count (alphabet r Q) (.head q a b) [b,a] env).value=r^Q*r^(Q-1) := by
  rw [count,sumCount_value]
  change ((alphabet r Q).map (fun w =>
    (count (alphabet r Q) (.head q a b) [a] (extend env b w)).value)).sum=_
  simp_rw [singleton_left r Q q a b hab]
  exact sum_constant r Q (r^(Q-1))

theorem self_count (r Q : ℕ) (q : Fin Q) (a : ℕ)
    (xs : List ℕ) (env : Environment r Q) :
    (count (alphabet r Q) (.head q a a) xs env).value=(r^Q)^xs.length := by
  induction xs generalizing env with
  | nil => simp [empty_head]
  | cons i xs ih =>
    rw [count,sumCount_value]
    change ((alphabet r Q).map (fun w =>
      (count (alphabet r Q) (.head q a a) xs (extend env i w)).value)).sum=_
    simp_rw [ih]
    rw [sum_constant]
    simp [pow_succ,Nat.mul_comm]


theorem one_shape (b : ℕ) (xs : List ℕ) (hn : xs.Nodup)
    (hm : ∀ x∈xs,x=b) : xs=[] ∨ xs=[b] := by
  cases xs with
  | nil => exact Or.inl rfl
  | cons x xs =>
    have hx:=hm x List.mem_cons_self
    subst x
    have hnil : xs=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro y hy
      have he:=hm y (List.mem_cons_of_mem _ hy)
      subst y
      exact (List.nodup_cons.mp hn).1 hy
    subst xs
    exact Or.inr rfl

theorem two_shapes (a b : ℕ) (xs : List ℕ) (hn : xs.Nodup)
    (hm : ∀ x∈xs,x=a ∨ x=b) :
    xs=[] ∨ xs=[a] ∨ xs=[b] ∨ xs=[a,b] ∨ xs=[b,a] := by
  cases xs with
  | nil => exact Or.inl rfl
  | cons x xs =>
    have hx:=hm x List.mem_cons_self
    rcases hx with rfl|rfl
    · have ht : ∀ y∈xs,y=b := by
        intro y hy
        rcases hm y (List.mem_cons_of_mem _ hy) with he|he
        · subst y; exact False.elim ((List.nodup_cons.mp hn).1 hy)
        · exact he
      rcases one_shape b xs (List.nodup_cons.mp hn).2 ht with rfl|rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · have ht : ∀ y∈xs,y=a := by
        intro y hy
        rcases hm y (List.mem_cons_of_mem _ hy) with he|he
        · exact he
        · subst y; exact False.elim ((List.nodup_cons.mp hn).1 hy)
      rcases one_shape a xs (List.nodup_cons.mp hn).2 ht with rfl|rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- The original paid active-support scan, observed at its returned list. -/
def activeHead {Q : ℕ} (q : Fin Q) (a b : ℕ) (remaining : List ℕ) :=
  (activeRun (support (.head q a b)) remaining).value

theorem activeHead_mem {Q : ℕ} (q : Fin Q) (a b x : ℕ) (xs : List ℕ) :
    x∈activeHead q a b xs ↔ x∈xs ∧ (x=a ∨ x=b) := by
  simp [activeHead,activeRun_value,OAI.Algorithms.SubexponentialSAT.LocalExpectation.active,support]

theorem activeHead_nodup {Q : ℕ} (q : Fin Q) (a b : ℕ) (xs : List ℕ) (hn : xs.Nodup) :
    (activeHead q a b xs).Nodup := by
  unfold activeHead
  rw [activeRun_value]
  exact hn.filter _


theorem supported_padded (r Q : ℕ) (q : Fin Q) (a b : ℕ)
    (xs : List ℕ) (env : Environment r Q) (hn : xs.Nodup)
    (hm : ∀ x∈xs,x=a ∨ x=b) (hlen : xs.length≤4) :
    (count (alphabet r Q) (.head q a b) xs env).value*(r^Q)^(4-xs.length)=
      if a=b then (r^Q)^4 else if a∈xs ∨ b∈xs then r^(4*Q-1)
      else if denote env a q=denote env b q then (r^Q)^4 else 0 := by
  by_cases hab : a=b
  · subst b
    rw [self_count,←pow_add,Nat.add_sub_of_le hlen]
    simp
  · simp only [hab,ite_false]
    rcases two_shapes a b xs hn hm with h|h|h|h|h
    · subst xs
      simp [empty_head]
    · subst xs
      simp
      rw [singleton_left r Q q a b hab, ←pow_mul, ←pow_add]
      congr 1
      have := q.isLt
      omega
    · subst xs
      simp
      rw [singleton_right r Q q a b hab, ←pow_mul, ←pow_add]
      congr 1
      have := q.isLt
      omega
    · subst xs
      simp
      rw [pair_left r Q q a b hab, ←pow_add, ←pow_mul, ←pow_add]
      congr 1
      have := q.isLt
      omega
    · subst xs
      simp
      rw [pair_right r Q q a b hab, ←pow_add, ←pow_mul, ←pow_add]
      congr 1
      have := q.isLt
      omega

theorem head_padded_original (r Q : ℕ) (q : Fin Q) (a b : ℕ)
    (remaining : List ℕ) (env : Environment r Q) (hn : remaining.Nodup) :
    (SemiprimeSourceScoreCountsPadding.paddedLocal (SemiprimeFiniteEnumerations.words r Q).values
      (.head q a b) remaining env).value=
      if a=b then (r^Q)^4 else if a∈remaining ∨ b∈remaining then r^(4*Q-1)
      else if denote env a q=denote env b q then (r^Q)^4 else 0 := by
  have hlen:=SemiprimeSourceScoreCountsPadding.active_length (.head q a b) remaining hn
  have h:=supported_padded r Q q a b (activeHead q a b remaining) env
    (activeHead_nodup q a b remaining hn)
    (fun x hx => (activeHead_mem q a b x remaining).mp hx |>.2) hlen
  have ha : a∈activeHead q a b remaining ↔ a∈remaining := by simp [activeHead_mem]
  have hb : b∈activeHead q a b remaining ↔ b∈remaining := by simp [activeHead_mem]
  simp only [ha,hb] at h
  simpa only [SemiprimeSourceScoreCountsPadding.paddedLocal,
    (SemiprimeSourceScoreCountsPadding.power_spec _ _).1,alphabet,activeHead,
    SemiprimeFiniteEnumerations.words_length] using h

end RiemannGaussian.SemiprimeSourceHeadCountFormula
