/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSemiprimeSupport

/-!
# Semiprime deletion in the complete signed RH carrier

The actual semiprime intersection is removed from the full adaptive
carrier at exposed right-half zeros. The exact negative multiplicity
source, all earlier arithmetic cuts and the signed Euler bridge survive.
On the earlier complete-composite interval, every nonzero survivor now
has at least two distinct primes above N^2. Other source scales retain
their composite-cofactor fallback; the large-smooth-factor estimate keeps
its own interval. The joint independent cofinal floor remains open.
The terminal RH theorem proves only the conditional floor implication.
-/

namespace RiemannGaussian.ZetaRieszSemiprimeDeletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaExposedZero
open ZetaExposedPrimeMoments
open ZetaPrimeCofactorCompletion
open ZetaRieszCompletedCofactor
open ZetaRieszSemiprimePrefix
open ZetaRieszSemiprimePrefixDecay
open ZetaRieszSemiprimeCompletion
open ZetaRieszSemiprimeBand
open ZetaRieszSemiprimeSupport

/-- The full actual semiprime class still present in the adaptive carrier
vanishes at exposed right-half zeros. The overlap with earlier deletions
is paid independently by the physical prefix theorem. -/
theorem tendsto_semiprime_intersection (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (P : Polynomial ℂ) (A : ℕ → Finset ℕ)
    (hA : ∀ N a, a ∈ A N → a.Prime ∧ a ≤ N ^ 2) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      ∑ n ∈ adaptiveBand (3 / 2 - rho.1.re) N ∩ semiprimeBand (A N) N,
        SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * (rho.1.im : ℂ)) n) atTop (𝓝 0) := by
  let u : ℝ := 3 / 2 - rho.1.re
  have hu : 0 < u := by dsimp [u]; linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : u < 1 := by dsimp [u]; linarith
  have h := (tendsto_actual_semiprime_integer_band rho hrho hexposed P A hA).sub
    (tendsto_semiprime_outside_adaptive A P rho.1.im hu hu1 hA)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  have hid := Finset.sum_filter_add_sum_filter_not (semiprimeBand (A N) N)
    (fun n => n ∈ adaptiveBand u N)
    (fun n => SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * (rho.1.im : ℂ)) n)
  rw [Finset.filter_mem_eq_inter, Finset.inter_comm] at hid
  have hs := congrArg (fun z : ℂ => (u : ℂ) ^ (N + 1) * z) hid
  dsimp only [u] at hs ⊢
  linear_combination (norm := ring_nf) -hs

/-- The remaining original integer labels after removing every semiprime
with a prime factor in the quadratic head, preserving all earlier cuts. -/
def residualBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  adaptiveBand u N \ semiprimeBand (Nat.primesLE (N ^ 2)) N

/-- The entire remaining signed response retains the original coefficient,
physical length, phase and factorial filter. -/
def residualResponse (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) : ℂ :=
  ∑ n ∈ residualBand u N, SquarefreeVaughanLogSource.coefficient L n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The old carrier splits exactly into the newly paid semiprime
intersection and the new residual, with no duplicate labels. -/
theorem adaptiveResponse_eq_semiprime_split (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) :
    ZetaRieszLargeSmoothDeletion.adaptiveSmoothResponse P N y L u =
      (∑ n ∈ adaptiveBand u N ∩ semiprimeBand (Nat.primesLE (N ^ 2)) N,
        SquarefreeVaughanLogSource.coefficient L n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
      residualResponse P N y L u := by
  rw [← sum_adaptiveBand_eq_response]
  exact (Finset.sum_inter_add_sum_sdiff (adaptiveBand u N)
    (semiprimeBand (Nat.primesLE (N ^ 2)) N)
    (fun n => SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)).symm

/-- The whole original carrier differs from the new residual by a
vanishing normalized quantity at exposed zeros. All previous deletion
ranges and their all-scale fallback remain intact. -/
theorem tendsto_actual_band_sub_residual (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (P : Polynomial ℂ) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      (zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)) P N rho.1.im -
        residualResponse P N rho.1.im (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
          (3 / 2 - rho.1.re))) atTop (𝓝 0) := by
  have hu : 1 / 2 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have h := (ZetaRieszLargeSmoothDeletion.tendsto_actual_band_sub_adaptiveSmooth P rho.1.im hu hu1).add
    (tendsto_semiprime_intersection rho hrho hexposed P (fun N => Nat.primesLE (N ^ 2))
      (fun _N _a ha => ⟨(Nat.mem_primesLE.mp ha).2, (Nat.mem_primesLE.mp ha).1⟩))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [adaptiveResponse_eq_semiprime_split]
  ring

/-- The exact original source normalization on the new residual. -/
def normalizedResidual (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
    residualResponse (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
      (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) (3 / 2 - rho.1.re)

/-- The complete negative multiplicity source survives the actual
semiprime deletion at every exposed right-half zero. -/
theorem tendsto_normalizedResidual (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) :
    Tendsto (normalizedResidual rho hrho) atTop (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hs := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  have he := tendsto_actual_band_sub_residual rho hrho hexposed (zetaRightHalfPoleJetFilter rho hrho)
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by push_cast; rfl
  simp only [hcast] at he
  have h := hs.sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold normalizedResidual
  ring

/-- Every new survivor still satisfies the full earlier adaptive support. -/
theorem residualBand_subset (u : ℝ) (N : ℕ) : residualBand u N ⊆ adaptiveBand u N :=
  Finset.sdiff_subset

/-- Every original-band semiprime with one prime in the quadratic head
and one above it lies in the uniquely counted class just removed. -/
theorem mem_semiprimeBand_of_factorization {a p n N : ℕ} (ha : a.Prime)
    (haN : a ≤ N ^ 2) (hp : p.Prime) (hNp : N ^ 2 < p)
    (hb : n ∈ zetaPrimeLogBand N) (he : n = p * a) :
    n ∈ semiprimeBand (Nat.primesLE (N ^ 2)) N := by
  have hpB : p ≤ 2 ^ (32 * N) := by
    have hnB := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2
    have hpn : p ≤ n := by rw [he]; nlinarith [ha.pos]
    exact hpn.trans hnB
  simp only [semiprimeBand, ZetaRieszSmoothPrimePrefix.productBand, Finset.mem_filter, and_true]
  refine ⟨Finset.mem_image.mpr ⟨(a, p), ?_, he.symm⟩, hb⟩
  exact Finset.mem_product.mpr ⟨Nat.mem_primesLE.mpr ⟨haN, ha⟩,
    Finset.mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hpB, hp⟩, hNp⟩⟩

/-- No surviving label is a small-prime/large-prime semiprime. This is
an actual integer-support exclusion, not a coefficient convention. -/
theorem surviving_not_small_semiprime {u : ℝ} {N n : ℕ} (hn : n ∈ residualBand u N) :
    ¬ ∃ a p : ℕ, a.Prime ∧ a ≤ N ^ 2 ∧ p.Prime ∧ N ^ 2 < p ∧ n = p * a := by
  rintro ⟨a, p, ha, haN, hp, hNp, he⟩
  exact (Finset.mem_sdiff.mp hn).2 (mem_semiprimeBand_of_factorization ha haN hp hNp
    (adaptiveBand_subset u N (residualBand_subset u N hn)) he)

/-- On the earlier complete-composite interval, every nonzero survivor
now has at least two distinct primes above the quadratic head. The
physical head comparison is eventually automatic at every 0<u<1. -/
theorem surviving_two_large_primes {u L : ℝ} {N n : ℕ}
    (hcontact : u < Real.exp (-(1 / 2 : ℝ)))
    (hNX : N ^ 2 < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2)
    (hn : n ∈ residualBand u N) (hc : SquarefreeVaughanLogSource.coefficient L n ≠ 0) :
    ∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ p ∣ n ∧ r ∣ n ∧ N ^ 2 < p ∧ N ^ 2 < r := by
  have hm := residualBand_subset u N hn
  have hprev : n ∈ ZetaRieszLargeSmoothDeletion.previousBand u N := by
    by_cases h : 2 * u ^ 2 < 1
    · rw [adaptiveBand, if_pos h] at hm
      exact (Finset.mem_sdiff.mp hm).1
    · simpa only [adaptiveBand, if_neg h] using hm
  rw [ZetaRieszLargeSmoothDeletion.previousBand, if_pos hcontact] at hprev
  rcases ZetaRieszCompositeDeletion.surviving_support_dichotomy hprev hc with hs | hs
  · obtain ⟨a, p, ha, haN, hp, hXp, he⟩ := hs
    exact False.elim (surviving_not_small_semiprime hn ⟨a, p, ha, haN, hp, hNX.trans hXp, he⟩)
  · exact hs

/-- The large-smooth-factor restriction survives on precisely its old
interval. No extension of that independent estimate is asserted. -/
theorem surviving_small_smooth_factor {u L : ℝ} {N n : ℕ} (hu2 : 2 * u ^ 2 < 1)
    (hn : n ∈ residualBand u N) (hc : SquarefreeVaughanLogSource.coefficient L n ≠ 0) :
    ∃ a b : ℕ, Squarefree a ∧ (∀ p ∈ a.primeFactors, p ≤ N ^ 2) ∧
      Squarefree b ∧ (∀ p ∈ b.primeFactors, N ^ 2 < p) ∧ n = b * a ∧
      a < (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 := by
  have hm := residualBand_subset u N hn
  rw [adaptiveBand, if_pos hu2] at hm
  exact ZetaRieszLargeSmoothDeletion.surviving_support_with_small_smooth_factor hm hc

/-- A strict cofinal floor for the whole new residual contradicts its
negative multiplicity source. The independent arithmetic floor is still
an explicit premise; component decay alone does not establish it. -/
theorem false_of_residual_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop, -c ≤ (normalizedResidual rho hrho N).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_normalizedResidual rho hrho hexposed)
  have hf := ge_of_tendsto_of_frequently hs hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- Independent cofinal floors only at exposed zeros suffice for Mathlib
RH. The exposed zero is selected from any hypothetical right-half zero;
no global rightmost-zero assumption is introduced. The floors remain open. -/
theorem rh_of_exposed_residual_floors
    (hfloor : ∀ (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re),
      (∀ tau : NontrivialZetaZero, tau ≠ rho →
        3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖) →
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop, -c ≤ (normalizedResidual rho hrho N).re) :
    RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨sigma, hright, hexposed⟩ := ZetaExposedZero.exists_exposed_right_half_zero rho hrho
    have hsigma : 1 / 2 < sigma.1.re := hrho.trans_le hright
    obtain ⟨c, hc, hf⟩ := hfloor sigma hsigma hexposed
    exact false_of_residual_cofinal_floor sigma hsigma hexposed hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

/-- The full signed Euler-window residual remains connected to the new
arithmetic support by a vanishing error at exposed zeros. All coupled
leading, mixed and boundary information remains available upstream. -/
theorem tendsto_quadraticResidual_sub_residual (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3 / 2 - rho.1.re < ‖(3 / 2 + Complex.I * (rho.1.im : ℂ)) - tau.1‖)
    (P : Polynomial ℂ) :
    Tendsto (fun N : ℕ => ((3 / 2 - rho.1.re : ℝ) : ℂ) ^ (N + 1) *
      (ZetaRieszEulerWindowDeletion.windowResidualResponse P N (N ^ 2) rho.1.im
          (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) -
        residualResponse P N rho.1.im (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N)
          (3 / 2 - rho.1.re))) atTop (𝓝 0) := by
  have hu : 0 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have h := (tendsto_actual_band_sub_residual rho hrho hexposed P).sub
    (ZetaRieszEulerQuadraticHead.tendsto_actual_band_sub_quadraticResidual P rho.1.im hu hu1)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  ring

end
end RiemannGaussian.ZetaRieszSemiprimeDeletion
