/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszOwnerCompletionAudit

/-!
# Why the joint floor must use the actual prime phases

Every original central label has a prime outside the entire head support.
Fixing every head-prime sign to one and averaging all other prime signs
annihilates the WHOLE central sum, at all counts simultaneously. The SAME
head stays fixed. Consequently some completely multiplicative sign choice
has joint real value at most minus the height-zero head.

This is an audit of estimates valid for arbitrary prime phases. Such signs
are NOT asserted to equal `exp (-I*y*log p)` at one fixed height. There is
no new bound on the actual fixed-height carrier or cofinal floor.
-/

set_option autoImplicit false
noncomputable section
open Real
open scoped BigOperators Classical
namespace RiemannGaussian.ZetaRieszJointPhaseConstraint
open ZetaRieszPrimeCountFrequency ZetaRieszPrimeEndpoint
open ZetaRieszBalancedOwnerFloor ZetaRieszBalancedRadialPayment
open ZetaRieszSmallTagNativeFloor (owners)
open ZetaRieszHeadSharedCancellation (headCofactors headCofactor_log)

/-- A multiplicative sign on a squarefree prime support, not an actual
fixed-height logarithmic character. -/
def signCharacter (V P : Finset ℕ) : ℝ :=
  ∏ p∈P, if p∈V then (-1 : ℝ) else 1

private theorem signCharacter_comm (V P : Finset ℕ) :
    signCharacter V P=∏ p∈V, if p∈P then (-1 : ℝ) else 1 := by
  simp only [signCharacter,Finset.prod_ite,Finset.prod_const_one,mul_one]
  congr 1
  ext p
  simp only [Finset.mem_filter,and_comm]

/-- One free prime suffices for EXACT cancellation of the average. The
other signs, including all shared prime incidences, are not independent
copies on different labels. -/
theorem sum_signCharacter_zero {F P : Finset ℕ} (h : (F∩P).Nonempty) :
    ∑ V∈F.powerset,signCharacter V P=0 := by
  simp_rw [signCharacter_comm]
  rw [← Finset.prod_one_add]
  obtain ⟨p,hp⟩ := h
  obtain ⟨hpF,hpP⟩ := Finset.mem_inter.mp hp
  exact Finset.prod_eq_zero hpF (by simp only [if_pos hpP]; norm_num)

/-- ALL signed amplitudes are joined before averaging. No count price,
norm, absolute moment or density replacement is introduced. -/
theorem sum_weighted_characters_zero (B F : Finset ℕ) (a : ℕ→ℝ)
    (hfree : ∀ n∈B,(F∩n.primeFactors).Nonempty) :
    ∑ V∈F.powerset,∑ n∈B,a n*signCharacter V n.primeFactors=0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro n hn
  rw [← Finset.mul_sum,sum_signCharacter_zero (hfree n hn),mul_zero]

theorem exists_nonpositive_signed_sum (B F : Finset ℕ) (a : ℕ→ℝ)
    (hfree : ∀ n∈B,(F∩n.primeFactors).Nonempty) :
    ∃ V∈F.powerset,(∑ n∈B,a n*signCharacter V n.primeFactors)≤0 := by
  by_contra h
  push Not at h
  have hz := sum_weighted_characters_zero B F a hfree
  have hp : 0<∑ V∈F.powerset,∑ n∈B,a n*signCharacter V n.primeFactors :=
    Finset.sum_pos (fun V hV => h V hV)
      (Finset.powerset_nonempty F)
  rw [hz] at hp
  exact (lt_irrefl (0 : ℝ)) hp

/-- A floor justified for ALL multiplicative sign choices must pay at
least the entire fixed head. The statement does not apply to a theorem
that exploits the correlations of one actual logarithmic character. -/
theorem arbitrary_sign_allowance_ge_head (B F : Finset ℕ) (a : ℕ→ℝ)
    (H b : ℝ) (hfree : ∀ n∈B,(F∩n.primeFactors).Nonempty)
    (hfloor : ∀ V∈F.powerset,
      -b≤(∑ n∈B,a n*signCharacter V n.primeFactors)-H) : H≤b := by
  obtain ⟨V,hV,hneg⟩ := exists_nonpositive_signed_sum B F a hfree
  have hf := hfloor V hV
  linarith only [hf,hneg]

private theorem central_not_head_owner {u : ℝ} {j n p : ℕ}
    (hn : n∈centralLabels u j) (hp : p∈n.primeFactors) :
    p∉owners u (dyadicMomentOrder j) := by
  intro howner
  have hhi := (mem_restLabels.mp (mem_centralLabels.mp hn).1).2
  have hlo := (ZetaRieszSmallTagNativeFloor.owners_data howner).2.2.1
  have hmax : p≤largestPrime n := by
    rw [largestPrime,dif_pos (show n.primeFactors.Nonempty from ⟨p,hp⟩)]
    exact Finset.le_max' _ _ hp
  have hlog := log_le_log
    (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos : (0 : ℝ)<p)
    (by exact_mod_cast hmax : (p : ℝ)≤largestPrime n)
  linarith only [hhi,hlo,hlog]

/-- The exact radial/count geometry leaves a free prime on EVERY native
central label. Three head cofactor primes would already have total log
greater than `21N/10`, outside the central window. -/
theorem central_has_prime_outside_head {u : ℝ} {j n : ℕ}
    (hn : n∈centralLabels u j) :
    ∃ p∈n.primeFactors,
      p∉owners u (dyadicMomentOrder j)∪headCofactors u (dyadicMomentOrder j) := by
  have hnative := (Finset.mem_sdiff.mp (mem_centralLabels.mp hn).1).1
  have hs : Squarefree n := (Finset.mem_filter.mp hnative).2
  have hc : 3≤n.primeFactors.card :=
    ZetaRieszJointPrimeEnergy.core_count (Finset.mem_filter.mp hnative).1
  have hN : (0 : ℝ)<dyadicMomentOrder j := by
    unfold dyadicMomentOrder dyadicPrimeCount
    positivity
  by_contra h
  push Not at h
  have hlog p (hp : p∈n.primeFactors) :
      (7/10 : ℝ)*dyadicMomentOrder j≤log p := by
    have hmem := h p hp
    rcases Finset.mem_union.mp hmem with ho | hq
    · exact False.elim (central_not_head_owner hn hp ho)
    · exact (headCofactor_log hq).le
  have hsum := Finset.sum_le_sum hlog
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  rw [← CoprimeEulerPhase.squarefree_log_eq_prime_sum hs] at hsum
  have hcR : (3 : ℝ)≤n.primeFactors.card := by exact_mod_cast hc
  have ht := (mem_centralLabels.mp hn).2.2
  nlinarith only [hN,hsum,hcR,ht]

/-- Only prime signs outside the SAME full head are varied. -/
def freePrimes (u : ℝ) (j : ℕ) : Finset ℕ :=
  (centralLabels u j).biUnion Nat.primeFactors\
    (owners u (dyadicMomentOrder j)∪headCofactors u (dyadicMomentOrder j))

theorem central_free_intersection {u : ℝ} {j n : ℕ} (hn : n∈centralLabels u j) :
    ((freePrimes u j)∩n.primeFactors).Nonempty := by
  obtain ⟨p,hp,hnot⟩ := central_has_prime_outside_head hn
  exact ⟨p,Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr
    ⟨Finset.mem_biUnion.mpr ⟨n,hn,hp⟩,hnot⟩,hp⟩⟩

/-- The signs on BOTH actual head legs remain one. Neither the head
support nor its allocation or sieve weight changes under this audit. -/
theorem head_pair_sign_one {u : ℝ} {j p q : ℕ} {V : Finset ℕ}
    (hV : V⊆freePrimes u j) (hp : p∈owners u (dyadicMomentOrder j))
    (hq : q∈ZetaRieszPrimeHeadTransport.pairInterval (dyadicMomentOrder j) p)
    (hqp : q.Prime) : signCharacter V {p,q}=1 := by
  have hpV : p∉V := by
    intro h
    exact (Finset.mem_sdiff.mp (hV h)).2 (Finset.mem_union_left _ hp)
  have hqH : q∈headCofactors u (dyadicMomentOrder j) :=
    Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_filter.mpr ⟨hq,hqp⟩⟩
  have hqV : q∉V := by
    intro h
    exact (Finset.mem_sdiff.mp (hV h)).2 (Finset.mem_union_right _ hqH)
  unfold signCharacter
  exact Finset.prod_eq_one (fun r hr => by
    rcases Finset.mem_insert.mp hr with hr | hr
    · subst r; rw [if_neg hpV]
    · have hrq := Finset.mem_singleton.mp hr
      subst r; rw [if_neg hqV])

/-- Keep the height-zero amplitudes of the actual original central main.
Some sign assignment has joint value no larger than MINUS the SAME head.
This is not an assignment of logarithmic phases at a fixed ordinate. -/
theorem exists_joint_le_neg_head (u : ℝ) (j : ℕ) :
    ∃ V∈(freePrimes u j).powerset,
      (∑ n∈centralLabels u j,
        (((u : ℂ)^(dyadicMomentOrder j+1)*
          SquarefreeVaughanLogSource.coefficient
            (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*
          zetaPrimeLogKernel (dyadicMomentOrder j) (3/2 : ℂ) n).re)*
            signCharacter V n.primeFactors)-
        ZetaRieszRoughPrimePairCancellation.nativeHead u 0 (dyadicMomentOrder j)≤
          -ZetaRieszRoughPrimePairCancellation.nativeHead u 0 (dyadicMomentOrder j) := by
  obtain ⟨V,hV,hneg⟩ := exists_nonpositive_signed_sum
    (centralLabels u j) (freePrimes u j)
    (fun n => ((u : ℂ)^(dyadicMomentOrder j+1)*
      SquarefreeVaughanLogSource.coefficient
        (SquarefreeVaughanLogSource.length u (dyadicMomentOrder j)) n*
      zetaPrimeLogKernel (dyadicMomentOrder j) (3/2 : ℂ) n).re)
    (fun n hn => central_free_intersection hn)
  exact ⟨V,hV,by linarith only [hneg]⟩

end RiemannGaussian.ZetaRieszJointPhaseConstraint
