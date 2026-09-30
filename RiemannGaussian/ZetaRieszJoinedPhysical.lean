/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszGammaJoint
import RiemannGaussian.ZetaRieszJointPrimeEnergy

/-!
# The unsaturated physical endgame

The existing `joinedPhysical` carries the full multiplicity-dependent source.
Its sufficient floor and ceiling remain explicit arithmetic hypotheses.
Prime deletion gives a full two-hinge atom on the entire original squarefree
core, so saturation and the factorial rectangle occur only in the already
geometrically paid recombination error. No physical support is completed.
-/

namespace RiemannGaussian.ZetaRieszJoinedPhysical
noncomputable section
open Filter Topology
open scoped BigOperators Classical ArithmeticFunction.Moebius
open ZetaRieszGammaJoint ZetaRieszJointFloor ZetaRieszPrimeCountFrequency
open ZetaRieszMaskSupport ZetaRieszJointAllocation ZetaRieszParityPacket
open ZetaRieszPrimeEndpoint ZetaRieszWideOwnerAudit ZetaRieszAnnulusJoint

/-- The existing physical carrier retains the exact source at every analytic
multiplicity. No arithmetic floor or ceiling is inferred from this limit. -/
theorem tendsto_joinedPhysical_exact_source (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling) :
    Tendsto (fun j => ((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
      joinedPhysical (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)) atTop
      (𝓝 (-(analyticZetaZeroMultiplicity rho : ℂ)+
        (analyticZetaZeroMultiplicity rho : ℂ)^2*(retainedCost (3/2-rho.1.re) : ℂ))) := by
  have hu : 0 < 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hs := (ZetaRieszJointFloor.tendsto_joint_exact_source rho hrho hexposed hU).sub
    (tendsto_joint_sub_joined hu hU (fun _ => rho.1.im)
      dyadicMomentOrder dyadicPrimeCount tendsto_dyadicMomentOrder)
  simp only [sub_zero] at hs
  exact hs.congr' (Eventually.of_forall fun _ => by ring)

/-- For a SIMPLE zero, a cofinal floor for joinedPhysical, with any vanishing real error,
would suffice. This hypothesis is open. In particular, no separate decay,
norm estimate, or one-sided floor for either component is required. -/
theorem false_of_joinedPhysical_cofinal_floor (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hsimple : analyticZetaZeroMultiplicity rho = 1)
    (err : ℕ → ℝ) (he : Tendsto err atTop (𝓝 0))
    (hfloor : ∃ᶠ j in atTop, -(79/1000 : ℝ)-err j ≤
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
        joinedPhysical (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)).re) : False := by
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  simp only [hsimple,Nat.cast_one,one_pow,one_mul,Complex.add_re,
    Complex.neg_re,Complex.one_re,Complex.ofReal_re] at hs
  have hc : -(79/1000 : ℝ) ≤ (-1+retainedCost (3/2-rho.1.re))+0 :=
    ge_of_tendsto_of_frequently (hs.add he)
      (hfloor.mono fun j hj => by dsimp only [Function.comp_def]; linarith)
  have hu : 1/2 ≤ 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hcost := retainedCost_lt_restricted hu hU
  linarith

/-- The same joinedPhysical carrier excludes a multiple exposed zero if it has
an independent cofinal ceiling. The ceiling is an OPEN arithmetic premise. -/
theorem false_of_joinedPhysical_cofinal_ceiling_of_multiple (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (hm : 2 ≤ analyticZetaZeroMultiplicity rho)
    (err : ℕ → ℝ) (he : Tendsto err atTop (𝓝 0))
    (hceiling : ∃ᶠ j in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
        joinedPhysical (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)).re ≤ 3/2+err j) : False := by
  have hs := Complex.continuous_re.tendsto _ |>.comp
    (tendsto_joinedPhysical_exact_source rho hrho hexposed hU)
  have hreal : (-(analyticZetaZeroMultiplicity rho : ℂ)+
      (analyticZetaZeroMultiplicity rho : ℂ)^2*(retainedCost (3/2-rho.1.re) : ℂ)).re =
      -(analyticZetaZeroMultiplicity rho : ℝ)+
        (analyticZetaZeroMultiplicity rho : ℝ)^2*retainedCost (3/2-rho.1.re) := by
    norm_cast
  rw [hreal] at hs
  have hc : -(analyticZetaZeroMultiplicity rho : ℝ)+
      (analyticZetaZeroMultiplicity rho : ℝ)^2*retainedCost (3/2-rho.1.re)-0 ≤ 3/2 :=
    le_of_tendsto_of_frequently (hs.sub he)
      (hceiling.mono fun j hj => by dsimp only [Function.comp_def]; linarith)
  have hu : 1/2 ≤ 3/2-rho.1.re := by linarith [NontrivialZetaZero.re_lt_one rho]
  have hcost := multiple_source_gt_three_halves hu hU hm
  linarith

/-- A two-sided cofinal band excludes EVERY analytic multiplicity, using
the existing carrier and source. The two cofinal subsequences may differ.
Neither arithmetic premise is proved by this conditional criterion. -/
theorem false_of_joinedPhysical_cofinal_bounds (rho : NontrivialZetaZero)
    (hrho : 1/2 < rho.1.re)
    (hexposed : ∀ tau : NontrivialZetaZero, tau ≠ rho →
      3/2-rho.1.re < ‖(3/2+Complex.I*(rho.1.im : ℂ))-tau.1‖)
    (hU : 3/2-rho.1.re ≤ ZetaRieszWideOwnerAudit.radiusCeiling)
    (lowerError upperError : ℕ → ℝ)
    (hl : Tendsto lowerError atTop (𝓝 0)) (hu : Tendsto upperError atTop (𝓝 0))
    (hfloor : ∃ᶠ j in atTop, -(79/1000 : ℝ)-lowerError j ≤
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
        joinedPhysical (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)).re)
    (hceiling : ∃ᶠ j in atTop,
      (((3/2-rho.1.re : ℝ) : ℂ)^(dyadicMomentOrder j+1)*
        joinedPhysical (3/2-rho.1.re) rho.1.im (dyadicMomentOrder j) (dyadicPrimeCount j)).re ≤ 3/2+upperError j) : False := by
  by_cases hm : analyticZetaZeroMultiplicity rho = 1
  · exact false_of_joinedPhysical_cofinal_floor rho hrho hexposed hU hm lowerError hl hfloor
  · have hpos := analyticZetaZeroMultiplicity_positive rho
    exact false_of_joinedPhysical_cofinal_ceiling_of_multiple rho hrho hexposed hU
      (by omega) upperError hu hceiling

/-- Prime deletion gives BOTH hinges without a cofactor saturation assumption.
The complex phase and the exact original allocation are unchanged. -/
theorem residual_atom_two_hinges (A : Finset ℕ) (L : ℝ) (N : ℕ) (s : ℂ)
    {p a : ℕ} (hp : p.Prime) (hsf : Squarefree (p*a)) (ha1 : a ≠ 1) :
    residualCoefficient A L N (p*a)*zetaPrimeLogKernel N s (p*a) =
      ((N+1 : ℕ) : ℂ)/(L : ℂ)*((1-boundedShare A N (p*a) : ℝ) : ℂ)*
        ((VaughanLogAverage.riesz (L-Real.log p) a-VaughanLogAverage.riesz L a : ℝ) : ℂ)*
          zetaPrimeLogKernel (N+1) s (p*a) := by
  have hpn : ¬p ∣ a := hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul hsf)
  have hnp : ¬(p*a).Prime := Nat.not_prime_mul hp.ne_one ha1
  simp only [residualCoefficient,SquarefreeVaughanLogSource.coefficient,
    if_pos (And.intro hsf hnp),ZetaSquarefreeRieszWindows.riesz_prime_mul L hp hpn]
  push_cast
  calc
    _ = ((1-boundedShare A N (p*a) : ℝ) : ℂ)*
        ((VaughanLogAverage.riesz (L-Real.log p) a : ℂ)-VaughanLogAverage.riesz L a)/L*
          ((Real.log (p*a : ℕ) : ℂ)*zetaPrimeLogKernel N s (p*a)) := by push_cast; ring
    _ = _ := by rw [ZetaRieszHeadOrders.log_mul_kernel]; push_cast; ring

/-- The full canonical atom on the original support. It has the full factorial
kernel and both physical hinges; there is no rectangle or saturation mask. -/
def fullTranslatedAtom (u y : ℝ) (N n : ℕ) : ℂ :=
  ((N+1 : ℕ) : ℂ)/(SquarefreeVaughanLogSource.length u N : ℂ)*
    ((1-boundedShare (intermediatePrimes u N) N n : ℝ) : ℂ)*
      ((VaughanLogAverage.riesz
          (SquarefreeVaughanLogSource.length u N-Real.log (largestPrime n))
          (n/largestPrime n)-
        VaughanLogAverage.riesz (SquarefreeVaughanLogSource.length u N)
          (n/largestPrime n) : ℝ) : ℂ)*
      zetaPrimeLogKernel (N+1) (3/2+Complex.I*y) n

/-- Every squarefree core atom has the same two-hinge formula, including
small-prime and unsaturated labels outside the former matched band. -/
theorem fullTranslatedAtom_eq_original {u : ℝ} {N K n : ℕ}
    (hn : n ∈ coreBand u N K) (hsf : Squarefree n) (y : ℝ) :
    fullTranslatedAtom u y N n =
      residualCoefficient (intermediatePrimes u N) (SquarefreeVaughanLogSource.length u N)
        N n*zetaPrimeLogKernel N (3/2+Complex.I*y) n := by
  have hc := ZetaRieszJointPrimeEnergy.core_count hn
  have hp := ZetaRieszOwnedCells.largestPrime_mem_of_two (by omega : 2 ≤ n.primeFactors.card)
  have hpp := Nat.prime_of_mem_primeFactors hp
  have he : largestPrime n*(n/largestPrime n)=n := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
  have hd := ZetaRieszMarkedSaturation.cofactor_data hsf hc hp
  have ha := residual_atom_two_hinges (intermediatePrimes u N)
    (SquarefreeVaughanLogSource.length u N) N (3/2+Complex.I*y) hpp
    (he.symm ▸ hsf) hd.2.1
  rw [he] at ha
  exact ha.symm

/-- Exact removal of the saturation split on the ENTIRE original core.
Nonsquarefree terms vanish; all other count, radial, allocation and physical
conditions remain literally those of coreBand. -/
theorem core_eq_fullTranslated (u y : ℝ) (N K : ℕ) :
    coreResponse u y N K =
      ∑ n ∈ (coreBand u N K).filter Squarefree, fullTranslatedAtom u y N n := by
  rw [ZetaRieszJointPrimeEnergy.core_eq_squarefree]
  exact Finset.sum_congr rfl (fun n hn =>
    (fullTranslatedAtom_eq_original (Finset.mem_filter.mp hn).1
      (Finset.mem_filter.mp hn).2 y).symm)

/-- Removing the remaining rectangle from joinedPhysical costs only the
already paid geometric boundary. This is a bound on the DIFFERENCE, not a
norm bound for either source-carrying expression. -/
theorem joined_fullTranslated_bound {u : ℝ} (hu : 0 ≤ u) (hU : u ≤ radiusCeiling)
    (N K : ℕ) (y : ℝ)
    (hL : (11/8 : ℝ)*N ≤ SquarefreeVaughanLogSource.length u N) :
    ‖(u : ℂ)^(N+1)*(joinedPhysical u y N K-
      ∑ n ∈ (coreBand u N K).filter Squarefree, fullTranslatedAtom u y N n)‖ ≤
      2*(19/20 : ℝ)^N*zetaMoebiusLogMajorantMass (1+1/256) := by
  rw [← core_eq_fullTranslated]
  have he : (u : ℂ)^(N+1)*(joinedPhysical u y N K-coreResponse u y N K) =
      -((u : ℂ)^(N+1)*(coreResponse u y N K-joinedPhysical u y N K)) := by ring
  rw [he,norm_neg]
  exact core_joined_bound hu hU N K y hL

/-- The full two-hinge core has no anonymous unmatched boundary at source
scale, for arbitrary growing orders, moving counts and moving heights. -/
theorem tendsto_joined_sub_fullTranslated {u : ℝ} (hu : 0 < u) (hU : u ≤ radiusCeiling)
    (heights : ℕ → ℝ) (orders counts : ℕ → ℕ) (ho : Tendsto orders atTop atTop) :
    Tendsto (fun t => (u : ℂ)^(orders t+1)*
      (joinedPhysical u (heights t) (orders t) (counts t)-
        ∑ n ∈ (coreBand u (orders t) (counts t)).filter Squarefree,
          fullTranslatedAtom u (heights t) (orders t) n)) atTop (𝓝 0) := by
  have h := (tendsto_core_sub_joined hu hU heights orders counts ho).neg
  simp only [neg_zero] at h
  apply h.congr'
  filter_upwards [] with t
  rw [core_eq_fullTranslated]
  ring

/-- The difference of translated hinges is a clipped interval length. -/
theorem hinge_difference_eq_neg_min {h : ℝ} (hh : 0 ≤ h) (x : ℝ) :
    max 0 (x-h)-max 0 x = -min h (max 0 x) := by
  by_cases hx : x ≤ 0
  · rw [max_eq_left hx,max_eq_left (by linarith : x-h ≤ 0),min_eq_right hh]
    ring
  · rw [max_eq_right (by linarith : 0 ≤ x)]
    by_cases hxh : x ≤ h
    · rw [max_eq_left (by linarith : x-h ≤ 0),min_eq_right hxh]
      ring
    · rw [max_eq_right (by linarith : 0 ≤ x-h),min_eq_left (by linarith : h ≤ x)]
      ring

/-- Both hinges are joined BEFORE the divisor signs are summed. The minimum
is nonnegative, but its Möbius-weighted sum has no asserted sign. -/
theorem riesz_difference_eq_clipped (L : ℝ) (p a : ℕ) :
    VaughanLogAverage.riesz (L-Real.log p) a-VaughanLogAverage.riesz L a =
      -(∑ d ∈ a.divisors, (μ d : ℝ)*min (Real.log p) (max 0 (L-Real.log d))) := by
  simp only [VaughanLogAverage.riesz,← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib,← mul_sub]
  apply Finset.sum_congr rfl
  intro d _
  rw [show L-Real.log p-Real.log d = (L-Real.log d)-Real.log p by ring,
    hinge_difference_eq_neg_min (Real.log_natCast_nonneg p)]
  ring

/-- The finite all-count Euler identity applies to the joined hinges with
its exact empty-middle correction retained. This does NOT remove arbitrary
label-dependent masks or change ordinary-prime weights into Euler odds. -/
theorem all_count_two_hinges (Q : Finset ℕ) (r : ℕ) (hr : r.Prime)
    (hQ : ∀ p ∈ Q, p.Prime) (hrQ : r ∉ Q)
    (s : ℂ) (hs : ∀ p ∈ Q, 1-zetaPrimeFeature s p ≠ 0) (L h : ℝ) :
    (∑ U ∈ Q.powerset.filter Finset.Nonempty,
      ZetaRieszSelectedCofactor.middleWeight U s*
        ((VaughanLogAverage.riesz (L-h) (r*∏ p ∈ U, p)-
          VaughanLogAverage.riesz L (r*∏ p ∈ U, p) : ℝ) : ℂ)) =
      ZetaRieszAllCountBoundary.eulerBoundary r Q s (L-h)-
        ZetaRieszAllCountBoundary.eulerBoundary r Q s L := by
  simp only [Complex.ofReal_sub,mul_sub,Finset.sum_sub_distrib]
  rw [ZetaRieszAllCountBoundary.all_count_riesz_eq Q r hr hQ hrQ s hs,
    ZetaRieszAllCountBoundary.all_count_riesz_eq Q r hr hQ hrQ s hs]

/-- The existing three-reflected-prime cancellation applies to the WHOLE
full-mass atom, without any leftover rectangle allocation. -/
theorem fullTranslatedAtom_eq_zero_of_three_outer {u : ℝ} (hu : 1/2 ≤ u)
    {N K n : ℕ} (hN : 2 ≤ N) (hn : n ∈ coreBand u N K)
    (hsf : Squarefree n) (hc : 5 ≤ n.primeFactors.card)
    (ho : 3 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes
      (Real.log n-SquarefreeVaughanLogSource.length u N) n).card) (y : ℝ) :
    fullTranslatedAtom u y N n = 0 := by
  rw [fullTranslatedAtom_eq_original hn hsf y,residualCoefficient,
    ZetaRieszReflectedPrimeBounds.coefficient_eq_zero_of_three_outer hsf hc
      (ZetaRieszReflectedPrimeBounds.core_cutoff_quarter hu hN hn) ho,mul_zero,zero_mul]

/-- Exact deletion of the already sign-cancelled reflected sector. This
spends no positive allowance and introduces no countwise triangle bound. -/
theorem core_eq_fullTranslated_without_three_outer {u : ℝ} (hu : 1/2 ≤ u)
    (y : ℝ) {N : ℕ} (hN : 2 ≤ N) (K : ℕ) :
    coreResponse u y N K =
      ∑ n ∈ ((coreBand u N K).filter Squarefree).filter
        (fun n : ℕ => ¬(5 ≤ n.primeFactors.card ∧
          3 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes
            (Real.log n-SquarefreeVaughanLogSource.length u N) n).card)),
        fullTranslatedAtom u y N n := by
  rw [core_eq_fullTranslated]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro n hn hnot
  have hh : 5 ≤ n.primeFactors.card ∧
      3 ≤ (ZetaRieszReflectedPrimeBounds.outerPrimes
        (Real.log n-SquarefreeVaughanLogSource.length u N) n).card := by
    by_contra h
    exact hnot (Finset.mem_filter.mpr ⟨hn,h⟩)
  exact fullTranslatedAtom_eq_zero_of_three_outer hu hN (Finset.mem_filter.mp hn).1
    (Finset.mem_filter.mp hn).2 hh.1 hh.2 y

end
end RiemannGaussian.ZetaRieszJoinedPhysical
