/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszCompositeSmooth
import RiemannGaussian.ZetaRieszPhysicalPrefixDeletion

/-!
# Complete composite-smooth deletion inside the Riesz remainder

On 1/2<u<exp(-1/2), nonzero survivors are either small-prime/large-prime
semiprimes beyond the physical cutoff, or integers with at least two prime
factors above N^2. All earlier cofactor restrictions remain. An all-scale
fallback preserves the exact hypothetical-zero source and independent
bridge to the signed Euler residual. The full cofinal signed floor and RH
remain open; the final RH implication assumes that arithmetic floor.
-/

namespace RiemannGaussian.ZetaRieszCompositeDeletion
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszCompositeSmooth

/-- The newly paid complete composite class inside the existing
prefix residual, preserving every earlier support restriction. -/
def compositeDeletionBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  compositeSmoothBand (fun n => n ∈ ZetaRieszPhysicalPrefixDeletion.prefixResidualBand u N) N

/-- The composite deletion is a literal subset of the previous residual. -/
theorem compositeDeletionBand_subset (u : ℝ) (N : ℕ) :
    compositeDeletionBand u N ⊆ ZetaRieszPhysicalPrefixDeletion.prefixResidualBand u N := by
  intro n hn
  exact ((mem_compositeSmoothBand_iff _ N n).mp hn).1.2

/-- Original integer labels after the complete composite-smooth deletion. -/
def compositeResidualBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  ZetaRieszPhysicalPrefixDeletion.prefixResidualBand u N \ compositeDeletionBand u N

/-- The unchanged signed response on the more tightly supported residual. -/
def compositeResidualResponse (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) : ℂ :=
  ∑ n ∈ compositeResidualBand u N, SquarefreeVaughanLogSource.coefficient L n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- The complete signed composite deletion and remaining sum partition
the previous response exactly, with every original coefficient retained. -/
theorem prefixResponse_eq_composite_split (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) :
    ZetaRieszPhysicalPrefixDeletion.prefixResidualResponse P N y L u =
      (∑ n ∈ compositeDeletionBand u N, SquarefreeVaughanLogSource.coefficient L n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
      compositeResidualResponse P N y L u := by
  unfold ZetaRieszPhysicalPrefixDeletion.prefixResidualResponse compositeResidualResponse compositeResidualBand
  simpa only [add_comm] using (Finset.sum_sdiff
    (f := fun n => SquarefreeVaughanLogSource.coefficient L n *
      zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n)
    (compositeDeletionBand_subset u N)).symm

/-- The full composite-smooth class is independently paid inside the
previous residual, rather than through cancellation with excluded terms. -/
theorem tendsto_compositeDeletionBand (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ compositeDeletionBand u N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (nhds 0) :=
  tendsto_actual_compositeSmoothBand
    (fun N n => n ∈ ZetaRieszPhysicalPrefixDeletion.prefixResidualBand u N) P y hu hcontact

/-- The original band differs negligibly from the residual after all
one-large-prime composite-smooth terms are paid on the stated source interval. -/
theorem tendsto_actual_band_sub_compositeResidual (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hcontact : u < Real.exp (-(1 / 2 : ℝ))) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N)) P N y -
        compositeResidualResponse P N y (SquarefreeVaughanLogSource.length u N) u))
      atTop (nhds 0) := by
  have h := (ZetaRieszPhysicalPrefixDeletion.tendsto_actual_band_sub_prefixResidual P y hu hcontact).add
    (tendsto_compositeDeletionBand P y hu hcontact)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [prefixResponse_eq_composite_split]
  ring

/-- A surviving single-large-prime label can have only a unit or prime
smooth cofactor; all composite smooth cofactors have been independently paid. -/
theorem surviving_single_prime_cofactor_unit_or_prime {u : ℝ} {N n a p : ℕ}
    (hn : n ∈ compositeResidualBand u N) (ha : Squarefree a)
    (hsmall : ∀ r ∈ a.primeFactors, r ≤ N ^ 2) (hp : p.Prime) (hbig : N ^ 2 < p)
    (he : n = p * a) : a = 1 ∨ a.Prime := by
  obtain ⟨hold, hnot⟩ := Finset.mem_sdiff.mp hn
  by_contra h
  have ha1 : a ≠ 1 := fun h1 => h (Or.inl h1)
  have hap : ¬ a.Prime := fun hp => h (Or.inr hp)
  have hb : n ∈ zetaPrimeLogBand N :=
    ZetaRieszSmoothCofactor.optimizedReducedBand_subset u N
      (ZetaRieszSmoothCofactor.optimizedRoughBand_support
        (ZetaRieszPhysicalPrefixDeletion.prefixResidualBand_subset u N hold)).1
  apply hnot
  exact (mem_compositeSmoothBand_iff _ N n).mpr
    ⟨⟨hb, hold⟩, a, p, ha, ha1, hap, hsmall, hp, hbig, he⟩

/-- Every nonzero surviving single-large-prime contribution is a
semiprime whose large prime exceeds the original physical cutoff. -/
theorem surviving_single_prime_nonzero_is_semiprime {u L : ℝ} {N n a p : ℕ}
    (hn : n ∈ compositeResidualBand u N) (ha : Squarefree a)
    (hsmall : ∀ r ∈ a.primeFactors, r ≤ N ^ 2) (hp : p.Prime) (hbig : N ^ 2 < p)
    (he : n = p * a) (hc : SquarefreeVaughanLogSource.coefficient L n ≠ 0) :
    a.Prime ∧ (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p := by
  have hap : a.Prime := by
    rcases surviving_single_prime_cofactor_unit_or_prime hn ha hsmall hp hbig he with h1 | hp'
    · exfalso
      apply hc
      simp [he, h1, SquarefreeVaughanLogSource.coefficient, hp]
    · exact hp'
  exact ⟨hap, ZetaRieszPhysicalPrefixDeletion.surviving_single_prime_above_physical_cutoff
    (Finset.mem_sdiff.mp hn).1 ha hsmall hp hbig he⟩

/-- Use the complete composite residual on the proved interval, retaining
the previous joint residual at every other source scale. -/
def adaptiveCompositeResponse (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) : ℂ :=
  if u < Real.exp (-(1 / 2 : ℝ)) then compositeResidualResponse P N y L u
  else ZetaRieszSmoothCofactor.optimizedRoughResponse P N y L u

/-- The original normalized band has independently vanishing error
against the adaptive carrier at every right-half source scale. -/
theorem tendsto_actual_band_sub_adaptiveComposite (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N)) P N y -
        adaptiveCompositeResponse P N y (SquarefreeVaughanLogSource.length u N) u))
      atTop (nhds 0) := by
  by_cases h : u < Real.exp (-(1 / 2 : ℝ))
  · simpa only [adaptiveCompositeResponse, if_pos h] using tendsto_actual_band_sub_compositeResidual P y hu h
  · simpa only [adaptiveCompositeResponse, if_neg h] using
      ZetaRieszSmoothCofactor.tendsto_actual_band_sub_optimizedRoughResponse P y hu hu1

/-- The exact original hypothetical-zero normalization on the adaptive
carrier, with the physical length and fixed pole-jet filter retained. -/
def normalizedAdaptiveComposite (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) (N : ℕ) : ℂ :=
  (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
    adaptiveCompositeResponse (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
      (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) (3 / 2 - rho.1.re)

/-- Every hypothetical right-half zero retains its exact negative
multiplicity source after the complete composite deletion and its all-scale fallback. -/
theorem tendsto_normalizedAdaptiveComposite (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re) :
    Tendsto (normalizedAdaptiveComposite rho hrho) atTop
      (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 1 / 2 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have hs := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  have he := tendsto_actual_band_sub_adaptiveComposite (zetaRightHalfPoleJetFilter rho hrho) rho.1.im hu hu1
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by push_cast; rfl
  simp only [hcast] at he
  have h := hs.sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold normalizedAdaptiveComposite
  ring

/-- A strict cofinal floor for the whole adaptive residual suffices
for contradiction. The independent arithmetic floor is still a premise. -/
theorem false_of_adaptiveComposite_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop, -c ≤ (normalizedAdaptiveComposite rho hrho N).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_normalizedAdaptiveComposite rho hrho)
  have hf := ge_of_tendsto_of_frequently hs hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- Independent full floors for the adaptive remaining carriers would
prove Mathlib RH. This implication does not establish their arithmetic floors. -/
theorem rh_of_adaptiveComposite_cofinal_floors
    (hfloor : ∀ (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re),
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop, -c ≤ (normalizedAdaptiveComposite rho hrho N).re) :
    RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨c, hc, hf⟩ := hfloor rho hrho
    exact false_of_adaptiveComposite_cofinal_floor rho hrho hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

/-- The complete nonzero remaining support is explicit: either a
small-prime/large-prime semiprime beyond the physical cutoff, or an integer
with at least two distinct prime factors above the quadratic head. -/
theorem surviving_support_dichotomy {u L : ℝ} {N n : ℕ}
    (hn : n ∈ compositeResidualBand u N) (hc : SquarefreeVaughanLogSource.coefficient L n ≠ 0) :
    (∃ a p : ℕ, a.Prime ∧ a ≤ N ^ 2 ∧ p.Prime ∧
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N + 2) ^ 2 < p ∧ n = p * a) ∨
    (∃ p r : ℕ, p.Prime ∧ r.Prime ∧ p ≠ r ∧ p ∣ n ∧ r ∣ n ∧ N ^ 2 < p ∧ N ^ 2 < r) := by
  have hold := ZetaRieszPhysicalPrefixDeletion.prefixResidualBand_subset u N
    (Finset.mem_sdiff.mp hn).1
  obtain ⟨_hb, hsf, p, hp, hpd, hbig⟩ := ZetaRieszSmoothCofactor.optimizedRoughBand_support hold
  by_cases hother : ∃ r : ℕ, r.Prime ∧ r ∣ n ∧ N ^ 2 < r ∧ r ≠ p
  · obtain ⟨r, hr, hrd, hrbig, hrp⟩ := hother
    exact Or.inr ⟨p, r, hp, hr, hrp.symm, hpd, hrd, hbig, hrbig⟩
  · obtain ⟨a, he⟩ := hpd
    have hmul : Squarefree (p * a) := by rwa [← he]
    have ha : Squarefree a := (Nat.squarefree_mul_iff.mp hmul).2.2
    have hpa : ¬ p ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hmul)
    have hsmall (r : ℕ) (hr : r ∈ a.primeFactors) : r ≤ N ^ 2 := by
      apply le_of_not_gt
      intro hrbig
      have hrd : r ∣ n := by
        rw [he]
        exact dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hr) p
      have hrp : r ≠ p := by
        intro hrp
        exact hpa (hrp ▸ Nat.dvd_of_mem_primeFactors hr)
      exact hother ⟨r, Nat.prime_of_mem_primeFactors hr, hrd, hrbig, hrp⟩
    obtain ⟨hap, hpX⟩ := surviving_single_prime_nonzero_is_semiprime hn ha hsmall hp hbig he hc
    have hamem : a ∈ a.primeFactors := by rw [hap.primeFactors]; simp
    exact Or.inl ⟨a, p, hap, hsmall a hamem, hp, hpX, he⟩

/-- The signed Euler-window residual remains independently connected
to the more tightly supported adaptive arithmetic carrier at every scale. -/
theorem tendsto_quadraticResidual_sub_adaptiveComposite (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (ZetaRieszEulerWindowDeletion.windowResidualResponse P N (N ^ 2) y
        (SquarefreeVaughanLogSource.length u N) -
        adaptiveCompositeResponse P N y (SquarefreeVaughanLogSource.length u N) u))
      atTop (nhds 0) := by
  have h := (tendsto_actual_band_sub_adaptiveComposite P y hu hu1).sub
    (ZetaRieszEulerQuadraticHead.tendsto_actual_band_sub_quadraticResidual P y
      (show 0 < u by linarith) hu1)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  ring

end
end RiemannGaussian.ZetaRieszCompositeDeletion
