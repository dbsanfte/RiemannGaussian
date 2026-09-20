/-
Copyright (c) 2026 David Sanftenberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Sanftenberg
-/
import RiemannGaussian.ZetaRieszMaskSizeBounds

/-!
# The entire original mask correction is accounted for

All old support restrictions follow on the stated lower-count subcutoff window. Every nonzero label remaining after the proved corrections lies in the original finite mask. The independent signed floor is not assumed.
-/

namespace RiemannGaussian.ZetaRieszMaskSupport

noncomputable section
open Filter Topology
open scoped BigOperators Classical
open ZetaRieszJointAllocation ZetaRieszPrimeCountFrequency
open ZetaRieszGeneralCofactorTilt ZetaRieszCofactorTiltRate
open ZetaRieszCompanionMask ZetaRieszWeightedCount

/-- A lower-count squarefree integer in the reserve window with every prime below the physical cutoff satisfies every original support mask. -/
theorem window_mem_originalMask (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2<u) (huh : u ≤ Real.exp (-(11/16:ℝ)))
    (hLlo : (5/4:ℝ)*dyadicMomentOrder j ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    {n : ℕ} (hnW : n ∈ literalWindow (dyadicMomentOrder j)) (hn : Squarefree n)
    (hc3 : 3 ≤ n.primeFactors.card) (hc : n.primeFactors.card < dyadicPrimeCount j)
    (hpX : ∀ p ∈ n.primeFactors, p < (ZetaVaughanCutoffBudget.linearDampedCutoff u (dyadicMomentOrder j)+2)^2) :
    n ∈ ZetaRieszCompanionMask.originalMask u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  let N := dyadicMomentOrder j
  let X := (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2
  let L := SquarefreeVaughanLogSource.length u N
  have hN : 2 ≤ N := by
    have hk := four_le_dyadicPrimeCount j
    dsimp [N, dyadicMomentOrder]
    nlinarith
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hX : 0<X := by dsimp [X]; positivity
  have hlogX : Real.log X = L := by
    simp only [X, L, SquarefreeVaughanLogSource.length, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  have hn0 : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn.ne_zero
  have hW := (mem_literalWindow N n).mp hnW
  have hband : n ∈ zetaPrimeLogBand N := (Finset.mem_filter.mp hnW).1
  have hLhi : L ≤ (3/2:ℝ)*N := by
    have h := ZetaRieszHeadOrders.length_le_two_log_two hu.le hN
    dsimp only [L]
    nlinarith [Real.log_two_lt_d9]
  have hu2 : u < Real.exp (-(2/3:ℝ)) := huh.trans_lt (Real.exp_lt_exp.mpr (by norm_num))
  have huc : u < Real.exp (-(1/2:ℝ)) := huh.trans_lt (Real.exp_lt_exp.mpr (by norm_num))
  have hu0 : 0<u := by linarith
  have hsmooth (a : ℕ) (had : a ∣ n) (ha : ∀ p ∈ a.primeFactors, p ≤ N^2) :
      Real.log a ≤ (N:ℝ)/4 := few_smooth_divisor_log_le j hj hn had hc ha
  have hplog (p : ℕ) (hpp : p.Prime) (hpd : p ∣ n) : Real.log p ≤ L := by
    have hp := hpX p (Nat.mem_primeFactors.mpr ⟨hpp,hpd,hn.ne_zero⟩)
    exact Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hp.le)
  have hnoFactor (a p : ℕ) (ha0 : 0<a) (hpp : p.Prime) (he : n=p*a)
      (halog : Real.log a ≤ (N:ℝ)/4) : False := by
    have hp := hplog p hpp (he ▸ dvd_mul_right p a)
    have hl : Real.log n = Real.log p+Real.log a := by
      rw [he, Nat.cast_mul, Real.log_mul (by exact_mod_cast hpp.ne_zero) (by exact_mod_cast Nat.ne_of_gt ha0)]
    linarith [hW.1]
  have hred : n ∈ ZetaRieszGeneralCofactorTilt.optimizedReducedBand u N := by
    rw [ZetaRieszGeneralCofactorTilt.optimizedReducedBand, if_neg (ne_of_lt huc), tiltedReducedBand]
    refine Finset.mem_filter.mpr ⟨hband, ?_⟩
    rintro ⟨a,p,ha1,haA,has,_hap,hpp,_hpa,he⟩
    exact hnoFactor a p (by omega) hpp he (tiltedSchedule_log_le_quarter hu huh (by omega) haA)
  have hrough : n ∈ ZetaRieszSmoothCofactor.optimizedRoughBand u N := by
    refine Finset.mem_filter.mpr ⟨hred, hn, ?_⟩
    by_contra hh
    have hsmall : ∀ p ∈ n.primeFactors, p ≤ N^2 := by
      intro p hp
      exact le_of_not_gt (fun h => hh ⟨p,hp,h⟩)
    have hs := hsmooth n (dvd_refl _) hsmall
    linarith [hW.1]
  have hprefix : n ∈ ZetaRieszPhysicalPrefixDeletion.prefixResidualBand u N := by
    refine Finset.mem_sdiff.mpr ⟨hrough, ?_⟩
    intro hm
    obtain ⟨_,a,p,has,ha,hpp,_hpN,_hpX,he⟩ :=
      (ZetaRieszSmoothPrimePrefix.mem_actualProductBand_iff _ u N n).mp hm
    exact hnoFactor a p (Nat.pos_of_ne_zero has.ne_zero) hpp he
      (hsmooth a (he ▸ dvd_mul_left a p) ha)
  have hcomp : n ∈ ZetaRieszCompositeDeletion.compositeResidualBand u N := by
    refine Finset.mem_sdiff.mpr ⟨hprefix, ?_⟩
    intro hm
    obtain ⟨_,a,p,has,_ha1,_hap,ha,hpp,_hpN,he⟩ :=
      (ZetaRieszCompositeSmooth.mem_compositeSmoothBand_iff _ N n).mp hm
    exact hnoFactor a p (Nat.pos_of_ne_zero has.ne_zero) hpp he
      (hsmooth a (he ▸ dvd_mul_left a p) ha)
  have hprevious : n ∈ ZetaRieszLargeSmoothDeletion.previousBand u N := by
    simpa only [ZetaRieszLargeSmoothDeletion.previousBand, if_pos huc] using hcomp
  have hlarge : n ∈ ZetaRieszLargeSmoothDeletion.largeSmoothResidualBand u N := by
    refine Finset.mem_sdiff.mpr ⟨hprevious, ?_⟩
    intro hm
    obtain ⟨_,a,b,has,ha,hXa,_hbs,_hb,he⟩ :=
      (ZetaRieszLargeSmoothClass.mem_largeSmoothFactorBand_iff _ u N n).mp hm
    have haL : L ≤ Real.log a := Real.log_le_log (by exact_mod_cast hX) (by exact_mod_cast hXa)
    have hs := hsmooth a (he ▸ dvd_mul_left a b) ha
    linarith
  have hadapt : n ∈ ZetaRieszSemiprimeSupport.adaptiveBand u N := by
    have huu : 2*u^2<1 := by
      have h := huh.trans radius_ceiling
      nlinarith
    simpa only [ZetaRieszSemiprimeSupport.adaptiveBand, if_pos huu] using hlarge
  have hsemi : n ∈ ZetaRieszSemiprimeDeletion.residualBand u N := by
    refine Finset.mem_sdiff.mpr ⟨hadapt, ?_⟩
    intro hm
    obtain ⟨a,ha,p,hp,he⟩ := productBand_factorization (fun _ => True) _ _ N n hm
    have hpa := (Nat.mem_primesLE.mp ha).2
    have hpp := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
    have hc2 := pair_prime_count_le_two hpp hpa
    rw [he] at hc2
    omega
  have hnarrow : n ∈ ZetaRieszNarrowCarrier.residualBand u N := by
    apply Finset.mem_filter.mpr
    refine ⟨hsemi, ?_, ?_⟩
    · linarith [hW.1]
    · nlinarith [hW.2, Real.log_two_gt_d9]
  have hext : ZetaRieszExtremePrimeCount.extremePrimes u N n = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hpn,hpx⟩ := Finset.mem_filter.mp hp
    exact (hpX p hpn).not_ge hpx
  have hfour : n ∈ ZetaRieszFourExtremeDeletion.fourResidualBand u N := by
    rw [ZetaRieszFourExtremeDeletion.fourResidualBand, if_pos huc]
    exact Finset.mem_filter.mpr ⟨hnarrow, by simp [hext]⟩
  have hdegree : n ∈ ZetaRieszLowerDegreeDeletion.degreeResidualBand u N := by
    rw [ZetaRieszLowerDegreeDeletion.degreeResidualBand, if_pos hu2]
    exact Finset.mem_filter.mpr ⟨hfour, by simp [hext]⟩
  have hannulus : n ∈ ZetaRieszPhysicalAnnulus.annulusBand u N := by
    rw [ZetaRieszPhysicalAnnulus.annulusBand, if_pos hu2]
    refine Finset.mem_filter.mpr ⟨hdegree, ?_, ?_⟩
    · have hl : Real.log X < Real.log n := by rw [hlogX]; linarith [hW.1]
      exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast hX) hn0).mp hl
    · have hl : Real.log n < Real.log (X^2:ℕ) := by
        rw [Nat.cast_pow, Real.log_pow, hlogX]
        norm_num only [Nat.cast_ofNat]
        linarith [hW.2]
      exact_mod_cast (Real.log_lt_log_iff hn0 (by exact_mod_cast pow_pos hX 2)).mp hl
  have hunpaired : n ∈ ZetaRieszCentralPrimeLayers.centralUnpairedBand u N := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hannulus,hpX⟩, ?_⟩, ?_, ?_⟩
    · intro hm
      obtain ⟨⟨a,p⟩,hap,he⟩ := Finset.mem_image.mp hm
      obtain ⟨hap,_⟩ := Finset.mem_filter.mp hap
      obtain ⟨ha,hp⟩ := Finset.mem_product.mp hap
      have hpa := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N a).mp ha
      have hpp := (ZetaRieszAnnulusJoint.mem_intermediatePrimes u N p).mp hp
      have hc2 := pair_prime_count_le_two hpa.1 hpp.1
      rw [he] at hc2
      omega
    · linarith [hW.1]
    · linarith [hW.2]
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hunpaired,hc3,hc⟩,hW⟩


/-- A nonunit squarefree composite has at least two distinct prime factors. -/
theorem composite_squarefree_count_ge_two {a : ℕ} (ha : Squarefree a) (ha1 : a ≠ 1) (hap : ¬a.Prime) :
    2 ≤ a.primeFactors.card := by
  by_contra hh
  have hc : a.primeFactors.card=0 ∨ a.primeFactors.card=1 := by omega
  rcases hc with hc | hc
  · have he : a.primeFactors=∅ := Finset.card_eq_zero.mp hc
    have hp := Nat.prod_primeFactors_of_squarefree ha
    simp only [he, Finset.prod_empty] at hp
    exact ha1 hp.symm
  · obtain ⟨p,hp⟩ := Finset.card_eq_one.mp hc
    have hpa : p=a := by simpa only [hp,Finset.prod_singleton] using Nat.prod_primeFactors_of_squarefree ha
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp]; exact Finset.mem_singleton_self p)
    exact hap (hpa ▸ hprime)

/-- Every eligible original companion incidence has at least three distinct prime factors. -/
theorem eligible_product_count_ge_three {p a : ℕ} (hp : p.Prime) (ha : eligibleCofactor p a) :
    3 ≤ (p*a).primeFactors.card := by
  have hc := composite_squarefree_count_ge_two ha.1 ha.2.1 ha.2.2.1
  have hpa : p ∉ a.primeFactors := fun h => ha.2.2.2 (Nat.dvd_of_mem_primeFactors h)
  rw [Nat.primeFactors_mul hp.ne_zero ha.1.ne_zero, hp.primeFactors, Finset.singleton_union,
    Finset.card_insert_of_notMem hpa]
  omega

/-- The complete assigned coefficient is exactly zero below three prime factors. -/
theorem assigned_zero_of_count_lt_three (A : Finset ℕ) (L : ℝ) (N n : ℕ)
    (hc : n.primeFactors.card < 3) : assignedCoefficient A L N n = 0 := by
  have ha0 : assignedAmplitude A N n=0 := by
    unfold assignedAmplitude
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro k _
    have hg : ¬(p∈A ∧ eligibleCofactor p (n/p)) := by
      rintro ⟨_,hel⟩
      have h := eligible_product_count_ge_three (Nat.prime_of_mem_primeFactors hp) hel
      rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_primeFactors hp)] at h
      omega
    exact if_neg hg
  unfold assignedCoefficient boundedShare allocationShare
  rw [ha0, zero_div]
  simp

/-- The finite signed coefficient is exactly its original masked coefficient minus the assigned coefficient. -/
theorem finiteCoefficient_eq_mask_sub_assigned (u : ℝ) (N K n : ℕ) :
    finiteCoefficient u N K n =
      (if n ∈ ZetaRieszCompanionMask.originalMask u N K then
        SquarefreeVaughanLogSource.coefficient (SquarefreeVaughanLogSource.length u N) n else 0) -
      assignedCoefficient (ZetaRieszAnnulusJoint.intermediatePrimes u N)
        (SquarefreeVaughanLogSource.length u N) N n := by
  unfold finiteCoefficient finiteWeight assignedCoefficient
  unfold ZetaRieszCompanionMask.originalMask
  split_ifs <;> push_cast <;> ring

/-- No low-degree coefficient survives in the joint finite response. -/
theorem coefficient_zero_of_count_lt_three (u : ℝ) (N K n : ℕ)
    (hc : n.primeFactors.card < 3) : finiteCoefficient u N K n=0 := by
  have hnS : n ∉ ZetaRieszCompanionMask.originalMask u N K := by
    intro h
    have h := (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2.1
    omega
  rw [finiteCoefficient_eq_mask_sub_assigned, if_neg hnS, assigned_zero_of_count_lt_three _ _ N n hc]
  simp

/-- An unselected prime carrying at least half the logarithm forces every eligible selected prime to be balanced. -/
theorem balanced_of_unselected_large_prime (A : Finset ℕ) {n q : ℕ} (hn : Squarefree n)
    (hq : q ∈ n.primeFactors) (hqA : q ∉ A) (hqlog : Real.log n/2 ≤ Real.log q) :
    ∀ p ∈ n.primeFactors, p ∈ A → eligibleCofactor p (n/p) → Real.log p ≤ Real.log n/2 := by
  intro p hp hpA _
  have hpq : p ≠ q := by rintro rfl; exact hqA hpA
  have hsub : ({p,q}:Finset ℕ) ⊆ n.primeFactors := by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hp
    · have he := Finset.mem_singleton.mp hr
      simpa only [he] using hq
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun r : ℕ => Real.log r) hsub
    (fun r _ _ => Real.log_natCast_nonneg r)
  rw [Finset.sum_pair hpq, ← CoprimeEulerPhase.squarefree_log_eq_prime_sum hn] at hs
  linarith


open ZetaRieszCompanionMask ZetaRieszWeightedCount

/-- After the independently paid count and balanced corrections, every nonzero residual coefficient belongs to the actual original mask. -/
theorem residual_nonzero_mem_original (j : ℕ) (hj : 32 ≤ j) {u : ℝ}
    (hu : 1/2<u) (huh : u ≤ Real.exp (-(11/16:ℝ)))
    (hLlo : (5/4:ℝ)*dyadicMomentOrder j ≤ SquarefreeVaughanLogSource.length u (dyadicMomentOrder j))
    {n : ℕ} (hnB : n ∈ residualMaskBand u (dyadicMomentOrder j) (dyadicPrimeCount j))
    (hcoeff : finiteCoefficient u (dyadicMomentOrder j) (dyadicPrimeCount j) n ≠ 0) :
    n ∈ originalMask u (dyadicMomentOrder j) (dyadicPrimeCount j) := by
  let N := dyadicMomentOrder j
  let K := dyadicPrimeCount j
  obtain ⟨hnlow,hnnot⟩ := Finset.mem_sdiff.mp hnB
  obtain ⟨hnremaining,hcount⟩ := Finset.mem_filter.mp hnlow
  have hnW : n ∈ literalWindow N := (Finset.mem_sdiff.mp hnremaining).1
  have hsf : Squarefree n := by
    by_contra h
    exact hcoeff (coefficient_zero_of_not_squarefree u N K n h)
  have hc3 : 3 ≤ n.primeFactors.card := by
    by_contra h
    exact hcoeff (coefficient_zero_of_count_lt_three u N K n (by omega))
  by_contra hnS
  have hq : ∃ q ∈ n.primeFactors,
      (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 ≤ q := by
    by_contra hh
    have hpX : ∀ p ∈ n.primeFactors, p < (ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2 := by
      intro p hp
      exact lt_of_not_ge (fun h => hh ⟨p,hp,h⟩)
    exact hnS (window_mem_originalMask j hj hu huh hLlo hnW hsf hc3 hcount hpX)
  obtain ⟨q,hqn,hXq⟩ := hq
  have hqA : q ∉ ZetaRieszAnnulusJoint.intermediatePrimes u N := by
    intro h
    exact ((ZetaRieszAnnulusJoint.mem_intermediatePrimes u N q).mp h).2.2.not_ge hXq
  have hqL : SquarefreeVaughanLogSource.length u N ≤ Real.log q := by
    have h := Real.log_le_log (by positivity : (0:ℝ)<((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2:ℕ))
      (by exact_mod_cast hXq : (((ZetaVaughanCutoffBudget.linearDampedCutoff u N+2)^2:ℕ):ℝ) ≤ q)
    simpa only [SquarefreeVaughanLogSource.length,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat] using h
  have hqlog : Real.log n/2 ≤ Real.log q := by
    have hw := ((mem_literalWindow N n).mp hnW).2
    have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
    change (5/4:ℝ)*N ≤ SquarefreeVaughanLogSource.length u N at hLlo
    linarith
  exact hnnot (Finset.mem_filter.mpr ⟨hnlow,hnS,
    balanced_of_unselected_large_prime _ hsf hqn hqA hqlog⟩)


end
end RiemannGaussian.ZetaRieszMaskSupport
