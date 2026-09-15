/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmoothHead

/-!
# Independent smooth-class deletion from the actual Riesz band

The exact signed partition removes every N^2-smooth squarefree term with
independently vanishing normalized error. The remaining class has a prime
above N^2 and retains the exact hypothetical-zero source. The final RH
implication assumes the still-open independent floor for the full remainder.
-/

namespace RiemannGaussian.ZetaRieszSmoothDeletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSmoothHead

/-- The actual squarefree band labels built entirely from head primes. -/
def smoothBand (N b : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter (fun n => Squarefree n ∧ ∀ p ∈ n.primeFactors, p ≤ b)

/-- The complementary actual squarefree labels have at least one prime
above the head; multiplicities are excluded by literal squarefree support. -/
def roughBand (N b : ℕ) : Finset ℕ :=
  (zetaPrimeLogBand N).filter (fun n => Squarefree n ∧ ∃ p ∈ n.primeFactors, b < p)

/-- The original signed coefficient and full complex filter on the head class. -/
def smoothResponse (P : Polynomial ℂ) (N b : ℕ) (y L : ℝ) : ℂ :=
  ∑ n ∈ smoothBand N b, SquarefreeVaughanLogSource.coefficient L n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The original signed coefficient and full complex filter on the
remaining class; no completion or sign change is made. -/
def roughResponse (P : Polynomial ℂ) (N b : ℕ) (y L : ℝ) : ℂ :=
  ∑ n ∈ roughBand N b, SquarefreeVaughanLogSource.coefficient L n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- Every retained rough label has an actual prime above the head. -/
theorem roughBand_has_large_prime {N b n : ℕ} (hn : n ∈ roughBand N b) :
    ∃ p, p.Prime ∧ p ∣ n ∧ b < p := by
  obtain ⟨p, hp, hb⟩ := (Finset.mem_filter.mp hn).2.2
  exact ⟨p, Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp, hb⟩

/-- An exact partition of the literal arithmetic band. Both signed sums
retain their original phases, lengths, factorial offsets and band endpoints. -/
theorem actual_band_eq_smooth_add_rough (P : Polynomial ℂ) (N b : ℕ) (y L : ℝ) :
    zetaArithmeticBand (SquarefreeVaughanLogSource.coefficient L) P N y =
      smoothResponse P N b y L + roughResponse P N b y L := by
  simp only [zetaArithmeticBand, smoothResponse, roughResponse, smoothBand, roughBand,
    Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hs : Squarefree n
  · by_cases hp : ∀ p ∈ n.primeFactors, p ≤ b
    · have hnlarge : ¬ ∃ p ∈ n.primeFactors, b < p := by
        rintro ⟨p, hpn, hpb⟩
        exact (hp p hpn).not_gt hpb
      rw [if_pos ⟨hs, hp⟩, if_neg (fun h => hnlarge h.2), add_zero]
    · have hlarge : ∃ p ∈ n.primeFactors, b < p := by
        by_contra hh
        apply hp
        intro p hpn
        exact le_of_not_gt (fun hpb => hh ⟨p, hpn, hpb⟩)
      rw [if_neg (fun h => hp h.2), if_pos ⟨hs, hlarge⟩, zero_add]
  · have hc : SquarefreeVaughanLogSource.coefficient L n = 0 := by
      simp [SquarefreeVaughanLogSource.coefficient, hs]
    simp only [hc, zero_mul, ite_self, zero_add]

/-- The entire actual smooth class through the square of the order
vanishes independently, for every positive physical-length schedule. -/
theorem tendsto_quadratic_smoothResponse (P : Polynomial ℂ) (y : ℝ)
    (L : ℕ → ℝ) (hL : ∀ N, 0 < L N) {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) * smoothResponse P N (N ^ 2) y (L N))
      atTop (nhds 0) := by
  apply tendsto_actual_quadratic_head_sum (fun N => smoothBand N (N ^ 2))
    (fun N => Nat.primesLE (N ^ 2)) _ _ _ _ P y L hL hu hu1
  · intro N n hn
    exact (Finset.mem_filter.mp hn).2.1
  · intro N
    exact Finset.filter_subset _ _
  · intro N n hn p hp
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_filter.mp hn).2.2 p hp,
      Nat.prime_of_mem_primeFactors hp⟩
  · intro N p hp
    exact ⟨(Nat.mem_primesLE.mp hp).2, (Nat.mem_primesLE.mp hp).1⟩

/-- The literal original normalized band differs negligibly from a
sum whose labels all have an actual prime above the square of the order.
This deletion uses no hypothetical-zero premise. -/
theorem tendsto_actual_band_sub_quadraticRoughResponse (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N)) P N y -
        roughResponse P N (N ^ 2) y (SquarefreeVaughanLogSource.length u N)))
      atTop (nhds 0) := by
  apply (tendsto_quadratic_smoothResponse P y (SquarefreeVaughanLogSource.length u)
    (SquarefreeVaughanLogSource.length_pos u) hu hu1).congr'
  filter_upwards [] with N
  rw [actual_band_eq_smooth_add_rough]
  ring

/-- The original hypothetical-zero filter and normalization on the
actual remaining class, with the physical length unchanged. -/
def normalizedRoughResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
    roughResponse (zetaRightHalfPoleJetFilter rho hrho) N (N ^ 2) rho.1.im
      (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)

/-- The exact negative multiplicity source survives after the
independent smooth-class deletion at every original factorial order. -/
theorem tendsto_normalizedRoughResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (normalizedRoughResponse rho hrho) atTop
      (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have hs := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  have he := tendsto_actual_band_sub_quadraticRoughResponse (zetaRightHalfPoleJetFilter rho hrho)
    rho.1.im hu hu1
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by push_cast; rfl
  simp only [hcast] at he
  have h := hs.sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold normalizedRoughResponse
  ring

/-- A strict cofinal real floor for the complete remaining rough
arithmetic sum contradicts the negative source. The floor is still a premise. -/
theorem false_of_roughResponse_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop, -c ≤ (normalizedRoughResponse rho hrho N).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_normalizedRoughResponse rho hrho)
  have hf := ge_of_tendsto_of_frequently hs hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- A full independent floor for each original rough arithmetic sum
would close Mathlib RH. This theorem does not establish its arithmetic premise. -/
theorem rh_of_roughResponse_cofinal_floors
    (hfloor : ∀ (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re),
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop, -c ≤ (normalizedRoughResponse rho hrho N).re) :
    RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨c, hc, hf⟩ := hfloor rho hrho
    exact false_of_roughResponse_cofinal_floor rho hrho hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

end
end RiemannGaussian.ZetaRieszSmoothDeletion
