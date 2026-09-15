/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszPhysicalProductBounds

/-!
# The actual physical annulus and the surviving signed source

On u<exp(-2/3) the whole carrier is restricted to X_N<n<X_N^2, preserving
every earlier support restriction, the physical floor and all factorial shifts.
The lower deletion is exact and the upper error independently vanishes.
Other scales keep their earlier residual. At exposed right-half zeros the
constant-filter annular response retains the entire negative multiplicity
source and its exact real cosine sum. Every surviving extreme-prime label
is an intermediate/extreme semiprime; other labels have all primes below X_N.
Their joint independent cofinal floor remains open in the conditional RH theorem.
-/

namespace RiemannGaussian.ZetaRieszPhysicalAnnulus
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszLowerDegreeBounds ZetaRieszLowerDegreeDeletion
open ZetaRieszPhysicalProductBounds

/-- On the square-tail interval retain exactly the physical annulus
inside every previous support cut. Other source scales are unchanged. -/
def annulusBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  if u < Real.exp (-(2 / 3 : ℝ)) then
    (degreeResidualBand u N).filter (fun n =>
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < n ∧
      n < ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2)
  else degreeResidualBand u N

/-- The original signed coefficient, physical length and factorial filter
on the actual annular support. -/
def annulusResponse (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) : ℂ :=
  ∑ n ∈ annulusBand u N, SquarefreeVaughanLogSource.coefficient L n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- All earlier arithmetic deletions and their ranges remain in force. -/
theorem annulusBand_subset (u : ℝ) (N : ℕ) : annulusBand u N ⊆ degreeResidualBand u N := by
  unfold annulusBand
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.Subset.refl _

/-- The surviving actual labels lie strictly between the physical cutoff
and its square on the new source interval. -/
theorem mem_annulusBand {u : ℝ} {N n : ℕ} (hu : u < Real.exp (-(2 / 3 : ℝ))) :
    n ∈ annulusBand u N ↔ n ∈ degreeResidualBand u N ∧
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < n ∧
      n < ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2 := by
  simp only [annulusBand, if_pos hu, Finset.mem_filter]

/-- Deleting the lower physical prefix is an exact equality, so the
annular response equals the upper-truncated original response. -/
theorem annulusResponse_eq_upper (P : Polynomial ℂ) (N : ℕ) (y : ℝ) {u : ℝ}
    (hu : u < Real.exp (-(2 / 3 : ℝ))) :
    annulusResponse P N y (SquarefreeVaughanLogSource.length u N) u =
      ∑ n ∈ (degreeResidualBand u N).filter (fun n =>
        n < ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2),
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n := by
  have h := sum_filter_physical_lower
    ((degreeResidualBand u N).filter (fun n =>
      n < ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2))
    (fun n => zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) u N
  simpa only [annulusResponse, annulusBand, if_pos hu, Finset.filter_filter, and_comm] using h

/-- The actual full annulus deletion has independently vanishing error
at source scale. No zero premise is used, and the fallback is unchanged. -/
theorem tendsto_degree_sub_annulus (P : Polynomial ℂ) (y : ℝ) {u : ℝ} (hu : 0 < u) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (degreeResidualResponse P N y (SquarefreeVaughanLogSource.length u N) u -
        annulusResponse P N y (SquarefreeVaughanLogSource.length u N) u)) atTop (𝓝 0) := by
  by_cases huh : u < Real.exp (-(2 / 3 : ℝ))
  · have h := tendsto_above_physical_square
      (fun N => (degreeResidualBand u N).filter (fun n =>
        ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2 ≤ n)) P y hu huh
      (fun _ _ hn => (Finset.mem_filter.mp hn).2)
    apply h.congr'
    filter_upwards [] with N
    rw [annulusResponse_eq_upper P N y huh]
    have he := Finset.sum_filter_add_sum_filter_not (degreeResidualBand u N)
      (fun n => n < ((ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ^ 2)
      (fun n => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    simp only [not_lt] at he
    unfold degreeResidualResponse
    rw [← he]
    ring
  · simpa only [annulusResponse, annulusBand, if_neg huh, degreeResidualResponse,
      sub_self, mul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

/-- The complete annular carrier keeps the original source normalization. -/
def normalizedAnnulus (rho : NontrivialZetaZero) (N : ℕ) : ℂ :=
  ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
    annulusResponse 1 N rho.1.im (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
      (3 / 2 - rho.1.re)

/-- The narrowed physical annulus retains the entire negative multiplicity
source, with no source margin lost. The independent signed floor is open. -/
theorem tendsto_normalizedAnnulus (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    Tendsto (normalizedAnnulus rho) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have h := (tendsto_normalizedDegreeResidual rho hrho hexposed).sub
    (tendsto_degree_sub_annulus 1 rho.1.im hu)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold normalizedAnnulus normalizedDegreeResidual
  ring

/-- Every surviving extreme-prime term in the actual annulus is an exact
intermediate/extreme semiprime. All other survivors have every prime below
the physical cutoff. These two classes still need their JOINT signed floor. -/
theorem annulus_support_dichotomy {u : ℝ} {N n : ℕ}
    (hu : u < Real.exp (-(2 / 3 : ℝ)))
    (hNX : N ^ 2 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hn : n ∈ annulusBand u N)
    (hc : SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n ≠ 0) :
    (∀ p ∈ n.primeFactors, p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2) ∨
    ∃ a p : ℕ, a.Prime ∧ p.Prime ∧ N ^ 2 < a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ∧
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 ≤ p ∧ n = p * a ∧
      SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n =
        ((-Real.log n * Real.log a / SquarefreeVaughanLogSource.length u N : ℝ) : ℂ) := by
  by_cases hsmall : ∀ p ∈ n.primeFactors,
      p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2
  · exact Or.inl hsmall
  · push Not at hsmall
    obtain ⟨p, hpn, hpX⟩ := hsmall
    have hp := Nat.prime_of_mem_primeFactors hpn
    obtain ⟨a, ha, haX, he, _, hcoeff⟩ := nonzero_extreme_below_square_is_semiprime
      hp (Nat.dvd_of_mem_primeFactors hpn) hpX ((mem_annulusBand hu).mp hn).2.2 hc
    have hsemi := ZetaRieszNarrowCarrier.residualBand_subset u N
      (ZetaRieszFourExtremeDeletion.fourResidualBand_subset u N
        (degreeResidualBand_subset u N (annulusBand_subset u N hn)))
    have hNa : N ^ 2 < a := by
      by_contra h
      exact ZetaRieszSemiprimeDeletion.surviving_not_small_semiprime hsemi
        ⟨a, p, ha, le_of_not_gt h, hp, hNX.trans_le hpX, he⟩
    exact Or.inr ⟨a, p, ha, hp, hNa, haX, hpX, he, hcoeff⟩

/-- The exact real source on the physical annulus keeps the coefficient
sign, original factorial envelope and full logarithmic product phase. -/
theorem re_normalizedAnnulus_eq_cosine_sum (rho : NontrivialZetaZero) (N : ℕ) :
    (normalizedAnnulus rho N).re =
      (3 / 2 - rho.1.re) ^ (N + 1) * ∑ n ∈ annulusBand (3 / 2 - rho.1.re) N,
        (SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n).re *
          (Real.exp (-(3 / 2 : ℝ) * Real.log n) * (Real.log n) ^ N / N.factorial) *
            Real.cos (rho.1.im * Real.log n) := by
  simp only [normalizedAnnulus, annulusResponse, ← Complex.ofReal_pow, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp only [Complex.re_sum, ZetaRieszCosineCarrier.re_coefficient_filter_one]

/-- A source-scale floor for the WHOLE annular residual gives the
contradiction. Its independent arithmetic premise remains open. -/
theorem false_of_annulus_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop, -c ≤ (normalizedAnnulus rho N).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_normalizedAnnulus rho hrho hexposed)
  have hf := ge_of_tendsto_of_frequently hs hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- The whole independent annular floors imply Mathlib RH. All source
transport, the physical upper bound, lower deletion and exposed-zero
selection are proved. The joint floors remain explicit open premises. -/
theorem rh_of_exposed_annulus_floors
    (hfloor : ∀ (rho : NontrivialZetaZero), 1 / 2 < rho.1.re →
      (∀ tau : NontrivialZetaZero, tau ≠ rho →
        3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) →
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop, -c ≤ (normalizedAnnulus rho N).re) :
    RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨sigma, hright, hexposed⟩ := ZetaExposedZero.exists_exposed_right_half_zero rho hrho
    have hsigma : 1 / 2 < sigma.1.re := hrho.trans_le hright
    obtain ⟨c, hc, hf⟩ := hfloor sigma hsigma hexposed
    exact false_of_annulus_cofinal_floor sigma hsigma hexposed hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

end
end RiemannGaussian.ZetaRieszPhysicalAnnulus
