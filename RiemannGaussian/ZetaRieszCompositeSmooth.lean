/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszBeyondPhysical

/-!
# Complete actual composite-smooth arithmetic classes

Unique prime insertion identifies the complete pair response with actual
integer labels. Every squarefree composite cofactor supported through N^2
is paid for 1/2<u<exp(-1/2), with every inserted prime above N^2, every
original order and every subband mask retained. No separate cofactor or
physical-prime cutoff is imposed on this complete class.
-/

namespace RiemannGaussian.ZetaRieszCompositeSmooth
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSmoothPrimeProduct
open ZetaRieszBeyondPhysical

/-- Every squarefree composite cofactor in the quadratic prime head,
with no size restriction. -/
def compositeCofactorHead (N : ℕ) : Finset ℕ :=
  (ZetaRieszSmoothPrimePrefix.cofactorHead (N ^ 2)).filter (fun a => a ≠ 1 ∧ ¬ a.Prime)

/-- The actual prime family through the original product ceiling,
strictly above the full cofactor head. -/
def allLargePrimes (N : ℕ) : Finset ℕ :=
  (Nat.primesLE (2 ^ (32 * N))).filter (fun p => N ^ 2 < p)

/-- The complete actual integer class with one large prime and a
composite smooth cofactor, intersected with any original-band mask. -/
def compositeSmoothBand (keep : ℕ → Prop) (N : ℕ) : Finset ℕ :=
  ZetaRieszSmoothPrimePrefix.productBand keep (compositeCofactorHead N) (allLargePrimes N) N

/-- Exact membership in the complete one-large-prime composite class;
there is no physical-prime cutoff or maximum-cofactor-size restriction. -/
theorem mem_compositeSmoothBand_iff (keep : ℕ → Prop) (N n : ℕ) :
    n ∈ compositeSmoothBand keep N ↔ (n ∈ zetaPrimeLogBand N ∧ keep n) ∧ ∃ a p : ℕ,
      Squarefree a ∧ a ≠ 1 ∧ ¬ a.Prime ∧ (∀ r ∈ a.primeFactors, r ≤ N ^ 2) ∧
      p.Prime ∧ N ^ 2 < p ∧ n = p * a := by
  constructor
  · intro hn
    obtain ⟨hi, hb⟩ := Finset.mem_filter.mp hn
    obtain ⟨⟨a, p⟩, hap, he⟩ := Finset.mem_image.mp hi
    obtain ⟨ha, hp⟩ := Finset.mem_product.mp hap
    obtain ⟨ha, ha1, haprime⟩ := Finset.mem_filter.mp ha
    obtain ⟨has, hsmall⟩ := (ZetaRieszSmoothPrimePrefix.mem_cofactorHead_iff _ a).mp ha
    obtain ⟨hp, hbig⟩ := Finset.mem_filter.mp hp
    exact ⟨hb, a, p, has, ha1, haprime, hsmall, (Nat.mem_primesLE.mp hp).2, hbig, he.symm⟩
  · rintro ⟨hb, a, p, ha, ha1, haprime, hsmall, hp, hbig, he⟩
    have ha0 : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
    have hpa : p ≤ p * a := by nlinarith [hp.pos]
    have hpB : p ≤ 2 ^ (32 * N) := by
      apply hpa.trans
      rw [← he]
      exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hb.1).1).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(a, p), Finset.mem_product.mpr ⟨?_, ?_⟩, he.symm⟩, hb⟩
    · exact Finset.mem_filter.mpr
        ⟨(ZetaRieszSmoothPrimePrefix.mem_cofactorHead_iff _ a).mpr ⟨ha, hsmall⟩, ha1, haprime⟩
    · exact Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpB, hp⟩, hbig⟩

/-- The complete actual composite-smooth class decays at every order
throughout the proved prefix interval, including every larger inserted prime. -/
theorem tendsto_actual_compositeSmoothBand (keep : ℕ → ℕ → Prop) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ compositeSmoothBand (keep N) N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (nhds 0) := by
  have hA N a (ha : a ∈ compositeCofactorHead N) : Squarefree a ∧ a ≠ 1 ∧ ¬ a.Prime :=
    ⟨ZetaRieszSmoothPrimePrefix.cofactorHead_squarefree _ _ (Finset.mem_filter.mp ha).1,
      (Finset.mem_filter.mp ha).2⟩
  have hS N a (ha : a ∈ compositeCofactorHead N) : a.primeFactors ⊆ Nat.primesLE (N ^ 2) :=
    ZetaRieszSmoothPrimePrefix.cofactorHead_primeFactors _ _ (Finset.mem_filter.mp ha).1
  have hQ N p (hp : p ∈ allLargePrimes N) : p.Prime ∧ N ^ 2 < p :=
    ⟨(Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2, (Finset.mem_filter.mp hp).2⟩
  have he N : (∑ n ∈ compositeSmoothBand (keep N) N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      pairResponse (keep N) (compositeCofactorHead N) (allLargePrimes N) P N y
        (SquarefreeVaughanLogSource.length u N) := by
    apply ZetaRieszSmoothPrimePrefix.productBand_sum_eq_pairResponse _ _ _ P N (N ^ 2) y _
      (fun a ha => (hA N a ha).1)
    · intro a ha p hp
      exact (Nat.mem_primesLE.mp (hS N a ha hp)).1
    · exact hQ N
  simp_rw [he]
  exact tendsto_all_composite_pairResponse keep compositeCofactorHead allLargePrimes
    (fun N => Nat.primesLE (N ^ 2)) P y hA hS
    (fun N p hp => ⟨(Nat.mem_primesLE.mp hp).2, (Nat.mem_primesLE.mp hp).1⟩) hQ hu hcontact

end
end RiemannGaussian.ZetaRieszCompositeSmooth
