/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMarkedCompletion

/-!
# The ordered Euler product equals the completed marked arithmetic packet

The reindexing keeps actual distinct primes, canonical least-prime order,
every middle subset, and the correlated finite factorial rectangle.
-/

namespace RiemannGaussian.ZetaRieszOrderedEulerCompletion
noncomputable section
open scoped BigOperators Classical
open ZetaRieszMarkedEuler ZetaRieszMarkedCompletion

/-- Least-prime, distinct marked-prime and middle-subset coordinates. -/
abbrev OrderedIndex := Σ _r : ℕ, Σ _p : ℕ, Finset ℕ
/-- Squarefree-label and marked-incidence coordinates. -/
abbrev MarkedIndex := Σ _n : ℕ, ℕ

/-- All admissible ordered pairs with nonempty middle subsets. The
empty subset has identically zero factorial rectangle. -/
def orderedIndices (A : Finset ℕ) : Finset OrderedIndex :=
  A.sigma (fun r => (A.filter (fun p => r < p)).sigma
    (fun p => ((middlePrimes A p r).powerset).filter Finset.Nonempty))

/-- Every nonleast marked incidence of the complete arithmetic universe. -/
def markedIndices (A : Finset ℕ) : Finset MarkedIndex :=
  (completeBand A).sigma (fun n => n.primeFactors.erase n.minFac)

/-- The actual prime support of an ordered incidence. -/
def support (a : OrderedIndex) : Finset ℕ := insert a.1 (insert a.2.1 a.2.2)
/-- The squarefree arithmetic label reconstructed from its prime support. -/
def label (a : OrderedIndex) : ℕ := ∏ q ∈ support a, q
/-- Reindex an ordered subset as its label and marked prime. -/
def toMarked (a : OrderedIndex) : MarkedIndex := ⟨label a,a.2.1⟩
/-- Recover the least prime and middle subset from a marked label. -/
def toOrdered (a : MarkedIndex) : OrderedIndex :=
  ⟨a.1.minFac,a.2,(a.1.primeFactors.erase a.2).erase a.1.minFac⟩

theorem ordered_data {A : Finset ℕ} {a : OrderedIndex} (ha : a ∈ orderedIndices A) :
    a.1 ∈ A ∧ a.2.1 ∈ A ∧ a.1 < a.2.1 ∧
      a.2.2 ⊆ middlePrimes A a.2.1 a.1 ∧ a.2.2.Nonempty := by
  rcases Finset.mem_sigma.mp ha with ⟨hr,hpU⟩
  rcases Finset.mem_sigma.mp hpU with ⟨hp,hU⟩
  exact ⟨hr,(Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2,
    Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1,(Finset.mem_filter.mp hU).2⟩

theorem support_data {A : Finset ℕ} {a : OrderedIndex} (ha : a ∈ orderedIndices A) :
    a.1 ∉ a.2.2 ∧ a.2.1 ∉ a.2.2 ∧ support a ⊆ A ∧
      3 ≤ (support a).card ∧ ∀ q ∈ support a, a.1 ≤ q := by
  obtain ⟨hr,hp,hrp,hU,hUn⟩ := ordered_data ha
  have hrU : a.1 ∉ a.2.2 := by
    intro hh
    exact (Finset.mem_filter.mp (hU hh)).2.1.false
  have hpU : a.2.1 ∉ a.2.2 := by
    intro hh
    exact (Finset.mem_filter.mp (hU hh)).2.2 rfl
  refine ⟨hrU,hpU,?_,?_,?_⟩
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hr
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact (Finset.mem_filter.mp (hU hq)).1
  · have hrnot : a.1 ∉ insert a.2.1 a.2.2 := by simp [hrp.ne,hrU]
    rw [support,Finset.card_insert_of_notMem hrnot,Finset.card_insert_of_notMem hpU]
    have hh := Finset.card_pos.mpr hUn
    omega
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · rfl
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hrp.le
    · exact (Finset.mem_filter.mp (hU hq)).2.1.le

theorem label_data {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) {a : OrderedIndex}
    (ha : a ∈ orderedIndices A) :
    Squarefree (label a) ∧ (label a).primeFactors = support a ∧
      1 < label a ∧ (label a).minFac = a.1 := by
  obtain ⟨_hrU,_hpU,hsub,hcard,hlo⟩ := support_data ha
  have hp (q : ℕ) (hq : q ∈ support a) : q.Prime := hA q (hsub hq)
  have hs := squarefree_prime_product (support a) hp
  have hf : (label a).primeFactors = support a := Nat.primeFactors_prod hp
  have h1 : 1 < label a := by
    have hz : label a ≠ 0 := hs.ne_zero
    have hn : label a ≠ 1 := by
      intro he
      rw [he,Nat.primeFactors_one] at hf
      have hcr := congrArg Finset.card hf
      simp only [Finset.card_empty] at hcr
      omega
    omega
  refine ⟨hs,hf,h1,?_⟩
  have hr : a.1 ∈ (label a).primeFactors := by rw [hf]; simp [support]
  have hrp := Nat.prime_of_mem_primeFactors hr
  apply le_antisymm (Nat.minFac_le_of_dvd hrp.two_le (Nat.dvd_of_mem_primeFactors hr))
  apply hlo
  rw [← hf]
  exact (Nat.minFac_prime h1.ne').mem_primeFactors (Nat.minFac_dvd _) hs.ne_zero

theorem toMarked_mem {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) {a : OrderedIndex}
    (ha : a ∈ orderedIndices A) : toMarked a ∈ markedIndices A := by
  obtain ⟨hs,hf,_h1,hm⟩ := label_data hA ha
  obtain ⟨_hrU,_hpU,hsub,hcard,_hlo⟩ := support_data ha
  have hd := ordered_data ha
  refine Finset.mem_sigma.mpr ⟨?_,?_⟩
  · apply (mem_completeBand A hA (label a)).mpr
    rw [hf]
    exact ⟨hs,hcard,hsub⟩
  · change a.2.1 ∈ (label a).primeFactors.erase (label a).minFac
    rw [hf,hm]
    simp [support,hd.2.2.1.ne']

theorem toOrdered_toMarked {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) {a : OrderedIndex}
    (ha : a ∈ orderedIndices A) : toOrdered (toMarked a) = a := by
  obtain ⟨_hs,hf,_h1,hm⟩ := label_data hA ha
  obtain ⟨hrU,hpU,_hsub,_hcard,_hlo⟩ := support_data ha
  have hrp := (ordered_data ha).2.2.1
  rcases a with ⟨r,p,U⟩
  dsimp at hrp hrU hpU
  simp only [toOrdered,toMarked,Sigma.mk.injEq,heq_eq_eq]
  simp only [hm,hf,support]
  simp only [true_and]
  ext q
  simp only [Finset.mem_erase,Finset.mem_insert]
  constructor
  · rintro ⟨hqr,hqp,rfl | rfl | hq⟩
    · exact False.elim (hqr rfl)
    · exact False.elim (hqp rfl)
    · exact hq
  · intro hq
    exact ⟨ne_of_mem_of_not_mem hq hrU,ne_of_mem_of_not_mem hq hpU,Or.inr (Or.inr hq)⟩

theorem marked_data {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) {a : MarkedIndex}
    (ha : a ∈ markedIndices A) :
    Squarefree a.1 ∧ 1 < a.1 ∧ 3 ≤ a.1.primeFactors.card ∧
      a.1.primeFactors ⊆ A ∧ a.2 ∈ a.1.primeFactors ∧ a.2 ≠ a.1.minFac := by
  obtain ⟨hn,hp⟩ := Finset.mem_sigma.mp ha
  obtain ⟨hs,hc,hA'⟩ := (mem_completeBand A hA a.1).mp hn
  obtain ⟨hne,hp⟩ := Finset.mem_erase.mp hp
  have h1 : 1 < a.1 := by
    have hz := hs.ne_zero
    have hh : a.1 ≠ 1 := by intro he; rw [he,Nat.primeFactors_one,Finset.card_empty] at hc; omega
    omega
  exact ⟨hs,h1,hc,hA',hp,hne⟩

theorem toOrdered_mem {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) {a : MarkedIndex}
    (ha : a ∈ markedIndices A) : toOrdered a ∈ orderedIndices A := by
  obtain ⟨hs,h1,hc,hsub,hp,hne⟩ := marked_data hA ha
  have hr : a.1.minFac ∈ a.1.primeFactors :=
    (Nat.minFac_prime h1.ne').mem_primeFactors (Nat.minFac_dvd _) hs.ne_zero
  have hrl : a.1.minFac < a.2 := lt_of_le_of_ne
    (Nat.minFac_le_of_dvd (Nat.prime_of_mem_primeFactors hp).two_le (Nat.dvd_of_mem_primeFactors hp)) hne.symm
  refine Finset.mem_sigma.mpr ⟨hsub hr,Finset.mem_sigma.mpr ⟨?_,?_⟩⟩
  · exact Finset.mem_filter.mpr ⟨hsub hp,hrl⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_,?_⟩
    · intro q hq
      obtain ⟨hqr,hqp⟩ := Finset.mem_erase.mp hq
      obtain ⟨hqp',hq⟩ := Finset.mem_erase.mp hqp
      refine Finset.mem_filter.mpr ?_
      exact ⟨hsub hq,lt_of_le_of_ne (Nat.minFac_le_of_dvd
        (Nat.prime_of_mem_primeFactors hq).two_le (Nat.dvd_of_mem_primeFactors hq)) hqr.symm,hqp'⟩
    · apply Finset.card_pos.mp
      change 0 < ((a.1.primeFactors.erase a.2).erase a.1.minFac).card
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne.symm,hr⟩),
        Finset.card_erase_of_mem hp]
      omega

theorem toMarked_toOrdered {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) {a : MarkedIndex}
    (ha : a ∈ markedIndices A) : toMarked (toOrdered a) = a := by
  obtain ⟨hs,h1,_hc,_hsub,hp,hne⟩ := marked_data hA ha
  have hr : a.1.minFac ∈ a.1.primeFactors :=
    (Nat.minFac_prime h1.ne').mem_primeFactors (Nat.minFac_dvd _) hs.ne_zero
  have hr' : a.1.minFac ∈ a.1.primeFactors.erase a.2 := Finset.mem_erase.mpr ⟨hne.symm,hr⟩
  have he : support (toOrdered a) = a.1.primeFactors := by
    simp only [support,toOrdered]
    rw [Finset.insert_comm,Finset.insert_erase hr',Finset.insert_erase hp]
  simp only [toMarked,he,label]
  rw [Nat.prod_primeFactors_of_squarefree hs]
  cases a
  rfl

theorem orderedSymbol_eq_index_sum (A : Finset ℕ) (N : ℕ) (s : ℂ) (xi : ℝ) :
    orderedSymbol A N s xi = ∑ a ∈ orderedIndices A,
      rectangle N a.2.1 a.1 s xi (∏ q ∈ a.2.2, leg s xi q) := by
  rw [orderedSymbol_subsets,orderedIndices,Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro p _hp
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro U hU hnot
  have he : U = ∅ := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hU,Finset.nonempty_iff_ne_empty.mpr hne⟩)
  simp only [he,Finset.prod_empty]
  exact rectangle_one N p r s xi

/-- Complete middle subsets are in bijection with genuine squarefree
labels and their marked prime incidences. No multiplicity factor is lost. -/
theorem orderedSymbol_eq_labels (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) (s : ℂ) (xi : ℝ) :
    orderedSymbol A N s xi = ∑ n ∈ completeBand A, labelSymbol N n s xi := by
  rw [orderedSymbol_eq_index_sum]
  have h : (∑ a ∈ orderedIndices A,
      rectangle N a.2.1 a.1 s xi (∏ q ∈ a.2.2, leg s xi q)) =
      ∑ b ∈ markedIndices A, rectangle N b.2 b.1.minFac s xi
        (∏ q ∈ (b.1.primeFactors.erase b.2).erase b.1.minFac, leg s xi q) := by
    apply Finset.sum_bij' (fun a _ => toMarked a) (fun b _ => toOrdered b)
      (fun _ ha => toMarked_mem hA ha) (fun _ hb => toOrdered_mem hA hb)
      (fun _ ha => toOrdered_toMarked hA ha) (fun _ hb => toMarked_toOrdered hA hb)
    intro a ha
    have hm := (label_data hA ha).2.2.2
    have he := congrArg (fun b : OrderedIndex => b.2.2) (toOrdered_toMarked hA ha)
    change ((label a).primeFactors.erase a.2.1).erase (label a).minFac = a.2.2 at he
    change rectangle N a.2.1 a.1 s xi _ =
      rectangle N a.2.1 (label a).minFac s xi _
    dsimp only [toMarked]
    rw [he,hm]
  rw [h,markedIndices,Finset.sum_sigma]
  rfl

theorem orderedPair_eq_labels (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) (s : ℂ) (L xi : ℝ) :
    orderedPair A N s L xi = ∑ n ∈ completeBand A, labelPair N n s L xi := by
  rw [orderedPair,orderedSymbol_eq_labels A hA,orderedSymbol_eq_labels A hA,
    Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  rfl

/-- The paired Euler response is genuinely integrable, including at
frequency zero. Its two signs are kept together. -/
theorem integrable_orderedPair (A : Finset ℕ) (hA : ∀ p ∈ A, p.Prime)
    (N : ℕ) (s : ℂ) (L : ℝ) :
    MeasureTheory.IntegrableOn
      (fun xi : ℝ => orderedPair A N s L xi/(xi : ℂ)^2) (Set.Ioi 0) := by
  simp_rw [orderedPair_eq_labels A hA,Finset.sum_div]
  apply MeasureTheory.integrable_finsetSum
  intro n hn
  obtain ⟨hs,hc,_hsub⟩ := (mem_completeBand A hA n).mp hn
  have h1 : 1 < n := by
    have hz := hs.ne_zero
    have hh : n ≠ 1 := by rintro rfl; norm_num at hc
    omega
  exact integrable_labelPair hs h1 N s L

/-- The completed ordered Euler product, evaluated at the ORIGINAL
moving physical cutoff and factorial rectangle. -/
def completion (u y : ℝ) (N : ℕ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(2*(Real.pi : ℂ)*(SquarefreeVaughanLogSource.length u N : ℂ))*
    ∫ xi : ℝ in Set.Ioi 0,
      orderedPair (ZetaRieszAnnulusJoint.intermediatePrimes u N) N
        (3/2+Complex.I*y) (SquarefreeVaughanLogSource.length u N) xi/(xi : ℂ)^2

/-- Exact arithmetic identification, before asymptotics: all ordered
middle subsets, factorial orders and Fourier signs are included. -/
theorem completePacket_eq_completion (u y : ℝ) (N : ℕ) :
    completePacket u y N = completion u y N := by
  have hA (p : ℕ) (hp : p ∈ ZetaRieszAnnulusJoint.intermediatePrimes u N) : p.Prime :=
    ((ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hp).1
  have hi (n : ℕ) (hn : n ∈ completeBand (ZetaRieszAnnulusJoint.intermediatePrimes u N)) :
      MeasureTheory.IntegrableOn (fun xi : ℝ => labelPair N n (3/2+Complex.I*y)
        (SquarefreeVaughanLogSource.length u N) xi/(xi : ℂ)^2) (Set.Ioi 0) := by
    obtain ⟨hs,h1,_hc,_hsub⟩ := completeBand_data hn
    exact integrable_labelPair hs h1 N _ _
  unfold completion
  simp_rw [orderedPair_eq_labels _ hA,Finset.sum_div]
  rw [MeasureTheory.integral_finsetSum _ hi,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hs,h1,hc,_hsub⟩ := completeBand_data hn
  have hnp : ¬n.Prime := by
    intro hp
    rw [hp.primeFactors,Finset.card_singleton] at hc
    omega
  exact marked_atom_eq_integral hs h1 hnp N _ (SquarefreeVaughanLogSource.length_pos u N)

/-- Terminal transfer: the existing signed boundary packet differs from
the ordered least-prime Euler completion by source-scale o(1). This is
independent of zero hypotheses and is not a bound on the common main term. -/
theorem tendsto_completion_sub_current {u : ℝ} (hu : 1/2 < u)
    (hU : u ≤ ZetaRieszWideOwnerAudit.radiusCeiling) (y : ℝ) :
    Filter.Tendsto (fun j => (u : ℂ)^(ZetaRieszPrimeCountFrequency.dyadicMomentOrder j+1)*
      (completion u y (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j)-
        (ZetaRieszLeastOrderOverflow.lowerThresholdPacket u y
          (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j)-
          ZetaRieszLeastOrderOverflow.shortOverflowPacket u y
            (ZetaRieszPrimeCountFrequency.dyadicMomentOrder j) (ZetaRieszPrimeCountFrequency.dyadicPrimeCount j))))
      Filter.atTop (nhds 0) := by
  simpa only [completePacket_eq_completion] using tendsto_complete_sub_current hu hU y

end
end RiemannGaussian.ZetaRieszOrderedEulerCompletion
