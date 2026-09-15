/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszSmoothDeletion
import RiemannGaussian.ZetaRieszGeneralCofactorTilt
import RiemannGaussian.ZetaRieszEulerQuadraticHead

/-!
# Joint smooth-prime and composite-cofactor deletion

Both independent arithmetic deletions hold together in one literal band.
Every remaining label has a prime above N^2, and every eligible composite
cofactor exceeds its previously paid threshold, including the scalar-contact
fallback. The full negative source and an independent bridge to the signed
Euler-window residual are proved. The complete joint floor and RH remain open.
-/

namespace RiemannGaussian.ZetaRieszSmoothCofactor
noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszSmoothHead

/-- The previous optimized composite-cofactor deletion remains a
literal subset of the original arithmetic band, including its scalar contact. -/
theorem optimizedReducedBand_subset (u : ℝ) (N : ℕ) :
    ZetaRieszGeneralCofactorTilt.optimizedReducedBand u N ⊆ zetaPrimeLogBand N := by
  unfold ZetaRieszGeneralCofactorTilt.optimizedReducedBand
  split_ifs
  · exact Finset.filter_subset _ _
  · exact Finset.filter_subset _ _

/-- The smooth labels still present after the independently paid
optimized cofactor deletion. -/
def optimizedSmoothBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  (ZetaRieszGeneralCofactorTilt.optimizedReducedBand u N).filter
    (fun n => Squarefree n ∧ ∀ p ∈ n.primeFactors, p ≤ N ^ 2)

/-- The remaining labels satisfy both arithmetic restrictions at once:
an actual prime exceeds N^2, and every eligible composite cofactor exceeds
the previous independently paid range. -/
def optimizedRoughBand (u : ℝ) (N : ℕ) : Finset ℕ :=
  (ZetaRieszGeneralCofactorTilt.optimizedReducedBand u N).filter
    (fun n => Squarefree n ∧ ∃ p ∈ n.primeFactors, N ^ 2 < p)

/-- The intersection class keeps both previously checked source
restrictions and the unchanged original coefficient and complex filter. -/
def optimizedRoughResponse (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) : ℂ :=
  ∑ n ∈ optimizedRoughBand u N, SquarefreeVaughanLogSource.coefficient L n *
    zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n

/-- Smooth-class decay is uniform over intersections with the
previous arithmetic deletion; no subtraction of unbounded pieces is used. -/
theorem tendsto_optimized_smooth_sum (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      ∑ n ∈ optimizedSmoothBand u N,
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n *
          zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) atTop (nhds 0) := by
  apply tendsto_actual_quadratic_head_sum (optimizedSmoothBand u)
    (fun N => Nat.primesLE (N ^ 2)) _ _ _ _ P y (SquarefreeVaughanLogSource.length u)
    (SquarefreeVaughanLogSource.length_pos u) hu hu1
  · intro N n hn
    exact (Finset.mem_filter.mp hn).2.1
  · intro N
    exact (Finset.filter_subset _ _).trans (optimizedReducedBand_subset u N)
  · intro N n hn p hp
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_filter.mp hn).2.2 p hp,
      Nat.prime_of_mem_primeFactors hp⟩
  · intro N p hp
    exact ⟨(Nat.mem_primesLE.mp hp).2, (Nat.mem_primesLE.mp hp).1⟩

/-- The previous optimized residual splits exactly into a newly paid
smooth class and the remaining intersection class, without duplicate labels. -/
theorem optimized_sum_eq_smooth_add_rough (P : Polynomial ℂ) (N : ℕ) (y L u : ℝ) :
    (∑ n ∈ ZetaRieszGeneralCofactorTilt.optimizedReducedBand u N,
      SquarefreeVaughanLogSource.coefficient L n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) =
      (∑ n ∈ optimizedSmoothBand u N, SquarefreeVaughanLogSource.coefficient L n *
        zetaPrimeFilterKernel P N (3 / 2 + Complex.I * y) n) +
      optimizedRoughResponse P N y L u := by
  simp only [optimizedRoughResponse, optimizedSmoothBand, optimizedRoughBand,
    Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hs : Squarefree n
  · by_cases hp : ∀ p ∈ n.primeFactors, p ≤ N ^ 2
    · have hnlarge : ¬ ∃ p ∈ n.primeFactors, N ^ 2 < p := by
        rintro ⟨p, hpn, hpb⟩
        exact (hp p hpn).not_gt hpb
      rw [if_pos ⟨hs, hp⟩, if_neg (fun h => hnlarge h.2), add_zero]
    · have hlarge : ∃ p ∈ n.primeFactors, N ^ 2 < p := by
        by_contra hh
        apply hp
        intro p hpn
        exact le_of_not_gt (fun hpb => hh ⟨p, hpn, hpb⟩)
      rw [if_neg (fun h => hp h.2), if_pos ⟨hs, hlarge⟩, zero_add]
  · have hc : SquarefreeVaughanLogSource.coefficient L n = 0 := by
      simp [SquarefreeVaughanLogSource.coefficient, hs]
    simp only [hc, zero_mul, ite_self, zero_add]

/-- Both complete arithmetic deletions have independently vanishing
total error. The new remaining class preserves the optimized cofactor cut
and also requires a prime above N^2, at every original order. -/
theorem tendsto_actual_band_sub_optimizedRoughResponse (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (zetaArithmeticBand
        (SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N)) P N y -
        optimizedRoughResponse P N y (SquarefreeVaughanLogSource.length u N) u))
      atTop (nhds 0) := by
  have h := (ZetaRieszGeneralCofactorTilt.tendsto_optimized_composite_band P y hu hu1).add
    (tendsto_optimized_smooth_sum P y (show 0 < u by linarith) hu1)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with N
  rw [ZetaRieszGeneralCofactorTilt.actual_band_eq_optimized_add_reduced P N y
    (SquarefreeVaughanLogSource.length u N) u, optimized_sum_eq_smooth_add_rough]
  ring

/-- Every label remaining after both independent deletions has an
actual prime above N^2 and belongs to the previous cofactor residual. -/
theorem optimizedRoughBand_support {u : ℝ} {N n : ℕ} (hn : n ∈ optimizedRoughBand u N) :
    n ∈ ZetaRieszGeneralCofactorTilt.optimizedReducedBand u N ∧
      Squarefree n ∧ ∃ p, p.Prime ∧ p ∣ n ∧ N ^ 2 < p := by
  obtain ⟨hm, hs, p, hp, hb⟩ := Finset.mem_filter.mp hn
  exact ⟨hm, hs, p, Nat.prime_of_mem_primeFactors hp, Nat.dvd_of_mem_primeFactors hp, hb⟩

/-- The actual cofactor threshold retained by the combined deletion,
including the independently paid polynomial fallback at scalar contact. -/
def optimizedCofactorThreshold (u : ℝ) (N : ℕ) : ℕ :=
  if u = Real.exp (-(1 / 2 : ℝ)) then ZetaRieszGrowingCofactor.eighthRootSchedule N
  else ZetaRieszGeneralCofactorTilt.tiltedSchedule u (ZetaRieszCofactorTiltRate.optimalTilt u) N

/-- Every eligible composite cofactor of every remaining label
exceeds the previously paid threshold. Semiprime cofactors stay explicit. -/
theorem optimizedRoughBand_cofactor_gt {u : ℝ} {N n a p : ℕ}
    (hn : n ∈ optimizedRoughBand u N) (ha1 : 1 < a) (hasf : Squarefree a)
    (hap : ¬ a.Prime) (hp : p.Prime) (hpa : ¬ p ∣ a) (he : n = p * a) :
    optimizedCofactorThreshold u N < a := by
  have hm := (Finset.mem_filter.mp hn).1
  by_cases hc : u = Real.exp (-(1 / 2 : ℝ))
  · rw [ZetaRieszGeneralCofactorTilt.optimizedReducedBand, if_pos hc] at hm
    simpa only [optimizedCofactorThreshold, if_pos hc] using
      ZetaRieszGrowingCofactor.surviving_composite_cofactor_gt hm ha1 hasf hap hp hpa he
  · rw [ZetaRieszGeneralCofactorTilt.optimizedReducedBand, if_neg hc] at hm
    simpa only [optimizedCofactorThreshold, if_neg hc] using
      ZetaRieszGeneralCofactorTilt.surviving_tilted_cofactor_gt hm ha1 hasf hap hp hpa he

/-- The exact original source normalization on the class satisfying
both independently proved arithmetic restrictions. -/
def normalizedOptimizedRoughResponse (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re)
    (N : ℕ) : ℂ :=
  (3 / 2 - rho.1.re : ℂ) ^ (N + 1) *
    optimizedRoughResponse (zetaRightHalfPoleJetFilter rho hrho) N rho.1.im
      (SquarefreeVaughanLogSource.length (3 / 2 - rho.1.re) N) (3 / 2 - rho.1.re)

/-- Both independent arithmetic deletions preserve the exact negative
multiplicity source at every order, including the scalar contact. -/
theorem tendsto_normalizedOptimizedRoughResponse (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) :
    Tendsto (normalizedOptimizedRoughResponse rho hrho) atTop
      (nhds (-(analyticZetaZeroMultiplicity rho : ℂ))) := by
  have hu : 1 / 2 < (3 / 2 - rho.1.re : ℝ) := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hu1 : (3 / 2 - rho.1.re : ℝ) < 1 := by linarith
  have hs := SquarefreeVaughanLogSource.tendsto_actual_riesz_band rho hrho
  have he := tendsto_actual_band_sub_optimizedRoughResponse (zetaRightHalfPoleJetFilter rho hrho)
    rho.1.im hu hu1
  have hcast : ((3 / 2 - rho.1.re : ℝ) : ℂ) = (3 / 2 - rho.1.re : ℂ) := by push_cast; rfl
  simp only [hcast] at he
  have h := hs.sub he
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  unfold normalizedOptimizedRoughResponse
  ring

/-- Only a strict cofinal floor for the complete intersection sum is
needed for contradiction. That independent floor remains an explicit premise. -/
theorem false_of_optimizedRoughResponse_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1 / 2 < rho.1.re) {c : ℝ} (hc : c < 1)
    (hfloor : ∃ᶠ N in atTop, -c ≤ (normalizedOptimizedRoughResponse rho hrho N).re) : False := by
  have hs := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_normalizedOptimizedRoughResponse rho hrho)
  have hf := ge_of_tendsto_of_frequently hs hfloor
  simp only [Complex.neg_re, Complex.natCast_re] at hf
  have hm : (1 : ℝ) ≤ analyticZetaZeroMultiplicity rho := by
    exact_mod_cast analyticZetaZeroMultiplicity_positive rho
  linarith

/-- Independent full floors for the remaining intersection sums would
prove Mathlib RH. No bound for those full sums is assumed to have been proved. -/
theorem rh_of_optimizedRoughResponse_cofinal_floors
    (hfloor : ∀ (rho : NontrivialZetaZero) (hrho : 1 / 2 < rho.1.re),
      ∃ c : ℝ, c < 1 ∧ ∃ᶠ N in atTop, -c ≤ (normalizedOptimizedRoughResponse rho hrho N).re) :
    RiemannHypothesis := by
  have hright (rho : NontrivialZetaZero) : rho.1.re ≤ 1 / 2 := by
    apply le_of_not_gt
    intro hrho
    obtain ⟨c, hc, hf⟩ := hfloor rho hrho
    exact false_of_optimizedRoughResponse_cofinal_floor rho hrho hc hf
  intro s hs htriv hone
  let rho : NontrivialZetaZero := ⟨s, hs, htriv, hone⟩
  have hupper := hright rho
  have hlower := hright (NontrivialZetaZero.functionalPartner rho)
  simp only [NontrivialZetaZero.functionalPartner_coe, Complex.sub_re, Complex.one_re] at hlower
  change s.re ≤ 1 / 2 at hupper
  change 1 - s.re ≤ 1 / 2 at hlower
  linarith

/-- The signed Euler-window residual and the more tightly supported
actual arithmetic residual differ by an independently vanishing quantity.
This connects both representations without a hypothetical-zero premise. -/
theorem tendsto_quadraticResidual_sub_optimizedRoughResponse (P : Polynomial ℂ) (y : ℝ)
    {u : ℝ} (hu : 1 / 2 < u) (hu1 : u < 1) :
    Tendsto (fun N : ℕ => (u : ℂ) ^ (N + 1) *
      (ZetaRieszEulerWindowDeletion.windowResidualResponse P N (N ^ 2) y
        (SquarefreeVaughanLogSource.length u N) -
        optimizedRoughResponse P N y (SquarefreeVaughanLogSource.length u N) u))
      atTop (nhds 0) := by
  have h := (tendsto_actual_band_sub_optimizedRoughResponse P y hu hu1).sub
    (ZetaRieszEulerQuadraticHead.tendsto_actual_band_sub_quadraticResidual P y
      (show 0 < u by linarith) hu1)
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [] with N
  ring

end
end RiemannGaussian.ZetaRieszSmoothCofactor
