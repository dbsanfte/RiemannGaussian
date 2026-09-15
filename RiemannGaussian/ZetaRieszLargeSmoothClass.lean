/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmoothRoughProduct
import RiemannGaussian.ZetaRieszSmoothPrimePrefix

/-!
# Actual classes with a large complete smooth factor

Disjoint prime supports uniquely recover both integer factors. Every
squarefree integer has the required complete smooth/rough factorization.
The original class whose N^2-smooth factor reaches the physical cutoff
has independent decay for 0<u and 2*u^2<1, with every subband mask and
any number of rough primes retained.
-/

namespace RiemannGaussian.ZetaRieszLargeSmoothClass
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSmoothRoughProduct

/-- Disjoint prime supports uniquely recover the complete smooth
and rough factors, so an arbitrary squarefree rough kernel counts each
actual integer exactly once in the original signed pair response. -/
theorem productBand_sum_eq_pairResponse_squarefree (keep : ℕ → Prop) (A Q : Finset ℕ)
    (P : Polynomial ℂ) (N h : ℕ) (y L : ℝ)
    (hA : ∀ a ∈ A, Squarefree a) (hQ : ∀ b ∈ Q, Squarefree b)
    (hsmall : ∀ a ∈ A, ∀ p ∈ a.primeFactors, p ≤ h)
    (hrough : ∀ b ∈ Q, ∀ p ∈ b.primeFactors, h < p) :
    (∑ n ∈ ZetaRieszSmoothPrimePrefix.productBand keep A Q N,
      SquarefreeVaughanLogSource.coefficient L n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      ZetaRieszSmoothPrimeProduct.pairResponse keep A Q P N y L := by
  have hsub (a b c d : ℕ) (ha : a ∈ A) (hc : c ∈ A) (hd : d ∈ Q)
      (he : b * a = d * c) : a.primeFactors ⊆ c.primeFactors := by
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ d * c := by
      rw [← he]
      exact dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hp) b
    rcases hprime.dvd_mul.mp hpd with hpd | hpc
    · have hpm := Nat.mem_primeFactors.mpr ⟨hprime, hpd, (hQ d hd).ne_zero⟩
      exact False.elim ((hrough d hd p hpm).not_ge (hsmall a ha p hp))
    · exact Nat.mem_primeFactors.mpr ⟨hprime, hpc, (hA c hc).ne_zero⟩
  have hinj : Set.InjOn (fun ab : ℕ × ℕ => ab.2 * ab.1) (A ×ˢ Q : Finset (ℕ × ℕ)) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd he
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
    change b * a = d * c at he
    have hp := Finset.Subset.antisymm (hsub a b c d ha hc hd he) (hsub c d a b hc ha hb he.symm)
    have hac : a = c := by
      rw [← Nat.prod_primeFactors_of_squarefree (hA a ha),
        ← Nat.prod_primeFactors_of_squarefree (hA c hc), hp]
    subst c
    have hbd : b = d := mul_right_cancel₀ (hA a ha).ne_zero he
    exact Prod.ext rfl hbd
  unfold ZetaRieszSmoothPrimePrefix.productBand
  rw [Finset.sum_filter, Finset.sum_image hinj, Finset.sum_product]
  rfl

/-- All actual squarefree rough factors through the original product
ceiling, with every prime factor above the quadratic smooth head. -/
def roughFactors (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (2 ^ (32 * N))).filter
    (fun b => Squarefree b ∧ ∀ p ∈ b.primeFactors, N ^ 2 < p)

/-- Every smooth factor at or beyond the original physical cutoff,
with its complete squarefree prime support and no additional size cap. -/
def largeSmoothHead (u : ℝ) (N : ℕ) : Finset ℕ :=
  (ZetaRieszSmoothPrimePrefix.cofactorHead (N ^ 2)).filter
    (fun a => (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ a)

/-- The actual original-band class whose smooth factor reaches the
physical cutoff, allowing any number of primes in the rough factor. -/
def largeSmoothFactorBand (keep : ℕ → Prop) (u : ℝ) (N : ℕ) : Finset ℕ :=
  ZetaRieszSmoothPrimePrefix.productBand keep (largeSmoothHead u N) (roughFactors N) N

/-- Every actual large-smooth-factor class decays independently when
2*u^2<1, with no restriction on the number of remaining rough primes. -/
theorem tendsto_actual_largeSmoothFactorBand (keep : ℕ → ℕ → Prop) (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu2 : 2 * u ^ 2 < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ largeSmoothFactorBand (keep N) u N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (nhds 0) := by
  have hA N a (ha : a ∈ largeSmoothHead u N) : Squarefree a :=
    ZetaRieszSmoothPrimePrefix.cofactorHead_squarefree _ _ (Finset.mem_filter.mp ha).1
  have hS N a (ha : a ∈ largeSmoothHead u N) : a.primeFactors ⊆ Nat.primesLE (N ^ 2) :=
    ZetaRieszSmoothPrimePrefix.cofactorHead_primeFactors _ _ (Finset.mem_filter.mp ha).1
  have hQ N b (hb : b ∈ roughFactors N) : Squarefree b := (Finset.mem_filter.mp hb).2.1
  have he N : (∑ n ∈ largeSmoothFactorBand (keep N) u N,
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      ZetaRieszSmoothPrimeProduct.pairResponse (keep N) (largeSmoothHead u N) (roughFactors N) P N y
        (SquarefreeVaughanLogSource.length u N) := by
    apply productBand_sum_eq_pairResponse_squarefree _ _ _ P N (N ^ 2) y _ (hA N) (hQ N)
    · intro a ha p hp
      exact (Nat.mem_primesLE.mp (hS N a ha hp)).1
    · intro b hb p hp
      exact (Finset.mem_filter.mp hb).2.2 p hp
  simp_rw [he]
  exact tendsto_large_smooth_pairResponse keep (largeSmoothHead u) roughFactors
    (fun N => Nat.primesLE (N ^ 2)) P y hA hS
    (fun N p hp => ⟨(Nat.mem_primesLE.mp hp).2, (Nat.mem_primesLE.mp hp).1⟩)
    hQ hu hu2 (fun N a ha => (Finset.mem_filter.mp ha).2)

/-- Exact membership in the complete large-smooth-factor class;
every prime in the second factor is above the head, with no count restriction. -/
theorem mem_largeSmoothFactorBand_iff (keep : ℕ → Prop) (u : ℝ) (N n : ℕ) :
    n ∈ largeSmoothFactorBand keep u N ↔ (n ∈ zetaPrimeLogBand N ∧ keep n) ∧ ∃ a b : ℕ,
      Squarefree a ∧ (∀ p ∈ a.primeFactors, p ≤ N ^ 2) ∧
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ a ∧
      Squarefree b ∧ (∀ p ∈ b.primeFactors, N ^ 2 < p) ∧ n = b * a := by
  constructor
  · intro hn
    obtain ⟨hi, hband⟩ := Finset.mem_filter.mp hn
    obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.mp hi
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨ha, hlarge⟩ := Finset.mem_filter.mp ha
    obtain ⟨has, hsmall⟩ := (ZetaRieszSmoothPrimePrefix.mem_cofactorHead_iff _ a).mp ha
    obtain ⟨_hbB, hbs, hrough⟩ := Finset.mem_filter.mp hb
    exact ⟨hband, a, b, has, hsmall, hlarge, hbs, hrough, he.symm⟩
  · rintro ⟨hband, a, b, ha, hsmall, hlarge, hb, hrough, he⟩
    have ha0 : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
    have hb0 : 0 < b := Nat.pos_of_ne_zero hb.ne_zero
    have hba : b ≤ b * a := by nlinarith
    have hbB : b ≤ 2 ^ (32 * N) := by
      apply hba.trans
      rw [← he]
      exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hband.1).1).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨?_, ?_⟩, he.symm⟩, hband⟩
    · exact Finset.mem_filter.mpr
        ⟨(ZetaRieszSmoothPrimePrefix.mem_cofactorHead_iff _ a).mpr ⟨ha, hsmall⟩, hlarge⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb0, hbB⟩, hb, hrough⟩

/-- Every squarefree integer has its full smooth/rough factorization
at the quadratic head; no factorization-existence premise is left downstream. -/
theorem exists_smooth_rough_factorization {n : ℕ} (hn : Squarefree n) (N : ℕ) :
    ∃ a b : ℕ, Squarefree a ∧ (∀ p ∈ a.primeFactors, p ≤ N ^ 2) ∧
      Squarefree b ∧ (∀ p ∈ b.primeFactors, N ^ 2 < p) ∧ n = b * a := by
  let a := Nat.gcd n (primorial (N ^ 2))
  have had : a ∣ n := Nat.gcd_dvd_left _ _
  have hah : a ∣ primorial (N ^ 2) := Nat.gcd_dvd_right _ _
  obtain ⟨b, he⟩ := had
  have hmul : Squarefree (a * b) := by rwa [← he]
  have ha : Squarefree a := hmul.of_mul_left
  have hb : Squarefree b := hmul.of_mul_right
  have hsmall (p : ℕ) (hp : p ∈ a.primeFactors) : p ≤ N ^ 2 := by
    have hm := Nat.primeFactors_mono hah (primorial_ne_zero _) hp
    rw [primeFactors_primorial] at hm
    exact (Nat.mem_primesLE.mp hm).1
  have hrough (p : ℕ) (hp : p ∈ b.primeFactors) : N ^ 2 < p := by
    apply lt_of_not_ge
    intro hle
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hphead : p ∣ primorial (N ^ 2) := by
      apply Nat.dvd_of_mem_primeFactors
      rw [primeFactors_primorial]
      exact Nat.mem_primesLE.mpr ⟨hle, hprime⟩
    have hpb : p ∣ b := Nat.dvd_of_mem_primeFactors hp
    have hpn : p ∣ n := by rw [he]; exact dvd_mul_of_dvd_right hpb a
    have hpa : p ∣ a := Nat.dvd_gcd hpn hphead
    have hg : p ∣ Nat.gcd a b := Nat.dvd_gcd hpa hpb
    rw [(Nat.coprime_of_squarefree_mul hmul).gcd_eq_one] at hg
    exact hprime.ne_one (Nat.dvd_one.mp hg)
  exact ⟨a, b, ha, hsmall, hb, hrough, he.trans (Nat.mul_comm a b)⟩

end
end RiemannGaussian.ZetaRieszLargeSmoothClass
